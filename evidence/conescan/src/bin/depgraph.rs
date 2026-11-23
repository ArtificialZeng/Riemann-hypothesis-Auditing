// depgraph: one pass over a lean4export (format 3.x, NDJSON) stream that writes the
// complete declaration-level dependency graph of the export.
//
// For every declaration record (def / thm / opaque / axiom / quot / inductive block) it
// walks the expression DAG of the declaration's type and of its value and records which
// other declarations are referenced (constants, and the structure named by a projection).
// Dependencies found in the TYPE (the statement) and in the VALUE (the proof term or the
// definition body) are kept apart, so that "what a statement talks about" can be separated
// from "what a proof uses".
//
// It also records, per declaration, two kinds of DIRECT occurrences that a node-level graph
// cannot express: structure projections `proj S i e` (which field of which structure is read),
// and references to individual names from an optional watch list (e.g. a recursor `T.rec`,
// which shares its graph node with the inductive type `T`).
//
// No external crates.  Usage:   depgraph OUTDIR [WATCHFILE] < solution.ndjson
// Output:  OUTDIR/nodes.tsv   node_id <TAB> kind <TAB> n_type_deps <TAB> n_value_deps <TAB> name
//                             (an inductive block has one line per declared name, same node_id)
//          OUTDIR/edges.bin   little-endian u32 stream; for each node in order:
//                             n_type, n_value, n_type ids, n_value ids   (ids are node_ids)
//          OUTDIR/projs.tsv   node_id <TAB> T|V <TAB> structure name <TAB> field index
//          OUTDIR/watch_hits.tsv  node_id <TAB> T|V <TAB> watched name
//          OUTDIR/depgraph_summary.txt
use std::io::{self, BufRead, Write};

struct Lex<'a> { b: &'a [u8], i: usize }
enum Val<'a> { Num(u64), Str(&'a [u8]), Other }
impl<'a> Lex<'a> {
    fn new(b: &'a [u8]) -> Self { Lex { b, i: 0 } }
    fn read_str(&mut self) -> &'a [u8] {
        let b = self.b; let start = self.i + 1; let mut j = start;
        while j < b.len() { match b[j] { b'\\' => j += 2, b'"' => break, _ => j += 1 } }
        self.i = (j + 1).min(b.len());
        &b[start..j.min(b.len())]
    }
    fn next(&mut self) -> Option<(&'a [u8], Val<'a>)> {
        let b = self.b;
        loop {
            while self.i < b.len() && b[self.i] != b'"' { self.i += 1; }
            if self.i >= b.len() { return None; }
            let s = self.read_str();
            if self.i < b.len() && b[self.i] == b':' {
                self.i += 1;
                if self.i >= b.len() { return None; }
                let c = b[self.i];
                if c.is_ascii_digit() {
                    let mut n: u64 = 0;
                    while self.i < b.len() && b[self.i].is_ascii_digit() { n = n * 10 + (b[self.i] - b'0') as u64; self.i += 1; }
                    return Some((s, Val::Num(n)));
                } else if c == b'"' { let v = self.read_str(); return Some((s, Val::Str(v))); }
                else { return Some((s, Val::Other)); }
            }
        }
    }
}

fn unescape(raw: &[u8]) -> String {
    let mut out: Vec<u8> = Vec::with_capacity(raw.len());
    let mut i = 0;
    while i < raw.len() {
        if raw[i] == b'\\' && i + 1 < raw.len() {
            match raw[i + 1] {
                b'n' => out.push(b'\n'), b't' => out.push(b'\t'), b'r' => out.push(b'\r'),
                b'b' => out.push(8), b'f' => out.push(12),
                b'u' if i + 5 < raw.len() => {
                    let h = std::str::from_utf8(&raw[i + 2..i + 6]).ok().and_then(|x| u32::from_str_radix(x, 16).ok()).unwrap_or(0xFFFD);
                    let ch = char::from_u32(h).unwrap_or('\u{FFFD}');
                    let mut buf = [0u8; 4]; out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                    i += 4;
                }
                c => out.push(c),
            }
            i += 2;
        } else { out.push(raw[i]); i += 1; }
    }
    String::from_utf8_lossy(&out).into_owned()
}

const NONE: u32 = u32::MAX;
// expression tags
const T_LEAF: u8 = 0; const T_TWO: u8 = 1; const T_CONST: u8 = 2; const T_PROJ: u8 = 3; const T_ONE: u8 = 4; const T_LET: u8 = 5;

struct G {
    tag: Vec<u8>, a: Vec<u32>, b: Vec<u32>, stamp: Vec<u32>,
    let_val: std::collections::HashMap<u32, u32>,
    node_of_name: Vec<u32>, node_stamp: Vec<u32>,
    visits: u64,
    proj_idx: std::collections::HashMap<u32, u32>,      // proj expr -> field index
    watch: std::collections::HashSet<u32>,              // watched name indices
    projs: Vec<(u32, u32)>, hits: Vec<u32>,             // direct occurrences found by the current walk
}
impl G {
    fn set(&mut self, ie: usize, t: u8, a: u32, b: u32) {
        if ie >= self.tag.len() { let n = ie + 1; self.tag.resize(n, T_LEAF); self.a.resize(n, NONE); self.b.resize(n, NONE); self.stamp.resize(n, 0); }
        self.tag[ie] = t; self.a[ie] = a; self.b[ie] = b;
    }
    // collect node ids referenced from the expression DAG rooted at `roots`; `epoch` must be unique per call
    fn collect(&mut self, roots: &[u32], epoch: u32, me: u32, out: &mut Vec<u32>, stack: &mut Vec<u32>) {
        stack.clear();
        for r in roots { if *r != NONE { stack.push(*r); } }
        while let Some(e) = stack.pop() {
            let i = e as usize;
            if i >= self.tag.len() || self.stamp[i] == epoch { continue; }
            self.stamp[i] = epoch; self.visits += 1;
            match self.tag[i] {
                T_TWO => { stack.push(self.a[i]); stack.push(self.b[i]); }
                T_ONE => { stack.push(self.a[i]); }
                T_LET => { stack.push(self.a[i]); stack.push(self.b[i]); if let Some(v) = self.let_val.get(&e) { stack.push(*v); } }
                T_PROJ => { stack.push(self.a[i]); self.name_ref(self.b[i], epoch, me, out);
                    let key = (self.b[i], self.proj_idx.get(&e).copied().unwrap_or(NONE));
                    if !self.projs.contains(&key) { self.projs.push(key); } }
                T_CONST => { let nm = self.a[i];
                    if !self.watch.is_empty() && self.watch.contains(&nm) && !self.hits.contains(&nm) { self.hits.push(nm); }
                    self.name_ref(nm, epoch, me, out); }
                _ => {}
            }
        }
    }
    fn name_ref(&mut self, name: u32, epoch: u32, me: u32, out: &mut Vec<u32>) {
        let n = name as usize; if n >= self.node_of_name.len() { return; }
        let node = self.node_of_name[n]; if node == NONE || node == me { return; }
        let k = node as usize; if self.node_stamp[k] == epoch { return; }
        self.node_stamp[k] = epoch; out.push(node);
    }
}

fn main() {
    let outdir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    let stdin = io::stdin();
    let mut rd = io::BufReader::with_capacity(1 << 26, stdin.lock());
    let mut line: Vec<u8> = Vec::with_capacity(1 << 16);
    let mut pre: Vec<u32> = vec![0]; let mut comp: Vec<Box<str>> = vec!["".into()];
    let full = |pre: &Vec<u32>, comp: &Vec<Box<str>>, mut n: u32| -> String {
        let mut parts: Vec<&str> = Vec::new();
        while n != 0 && (n as usize) < pre.len() { parts.push(&comp[n as usize]); n = pre[n as usize]; }
        parts.reverse(); parts.join(".")
    };
    let mut g = G { tag: Vec::new(), a: Vec::new(), b: Vec::new(), stamp: Vec::new(), let_val: Default::default(), node_of_name: Vec::new(), node_stamp: Vec::new(), visits: 0,
        proj_idx: Default::default(), watch: Default::default(), projs: Vec::new(), hits: Vec::new() };
    let watch_full: std::collections::HashSet<String> = match std::env::args().nth(2) {
        Some(f) => std::fs::read_to_string(f).expect("read watch file").lines().map(|l| l.trim().to_string()).filter(|l| !l.is_empty() && !l.starts_with('#')).collect(),
        None => Default::default() };
    let watch_last: std::collections::HashSet<String> = watch_full.iter().map(|s| s.rsplit('.').next().unwrap().to_string()).collect();
    let mut projs_f = io::BufWriter::new(std::fs::File::create(format!("{}/projs.tsv", outdir)).unwrap());
    let mut hits_f = io::BufWriter::new(std::fs::File::create(format!("{}/watch_hits.tsv", outdir)).unwrap());
    let mut watch_seen: Vec<String> = Vec::new();
    let mut nodes = io::BufWriter::with_capacity(1 << 22, std::fs::File::create(format!("{}/nodes.tsv", outdir)).unwrap());
    let mut edges = io::BufWriter::with_capacity(1 << 24, std::fs::File::create(format!("{}/edges.bin", outdir)).unwrap());
    let (mut nlines, mut nbytes, mut n_nodes, mut n_names_decl, mut n_te, mut n_ve) = (0u64, 0u64, 0u32, 0u64, 0u64, 0u64);
    let mut epoch: u32 = 0;
    let mut tdeps: Vec<u32> = Vec::new(); let mut vdeps: Vec<u32> = Vec::new(); let mut stack: Vec<u32> = Vec::new();
    let mut kinds: std::collections::BTreeMap<&'static str, u64> = Default::default();

    loop {
        line.clear();
        let n = rd.read_until(b'\n', &mut line).expect("read");
        if n == 0 { break; }
        nlines += 1; nbytes += n as u64;
        if nlines % 100_000_000 == 0 { eprintln!("... {} M lines, {:.1} GB, exprs {}, nodes {}, dag visits {}", nlines / 1_000_000, nbytes as f64 / 1e9, g.tag.len(), n_nodes, g.visits); }
        let b = &line[..];
        if b.len() < 6 { continue; }
        let is = |p: &[u8]| b.starts_with(p);
        if is(b"{\"app\":") {
            let mut lx = Lex::new(b); let (mut a, mut f, mut ie) = (0u64, 0u64, 0u64);
            while let Some((k, v)) = lx.next() { if let Val::Num(x) = v { match k { b"arg" => a = x, b"fn" => f = x, b"ie" => ie = x, _ => {} } } }
            g.set(ie as usize, T_TWO, f as u32, a as u32);
            continue;
        }
        let kind: &'static str =
            if is(b"{\"in\":") { "name" } else if is(b"{\"il\":") { "level" }
            else if is(b"{\"bvar\":") { "bvar" } else if is(b"{\"const\":") { "const" } else if is(b"{\"forallE\":") { "forallE" }
            else if is(b"{\"ie\":") { "ie" }
            else if is(b"{\"def\":") { "def" } else if is(b"{\"thm\":") { "thm" } else if is(b"{\"axiom\":") { "axiom" }
            else if is(b"{\"opaque\":") { "opaque" } else if is(b"{\"quot\":") { "quot" } else if is(b"{\"inductive\":") { "inductive" }
            else if is(b"{\"meta\":") { "meta" } else { "unknown" };
        match kind {
            "level" | "meta" => {}
            "name" => {
                let mut lx = Lex::new(b); let (mut idx, mut p) = (0u64, 0u64); let mut c: Box<str> = "".into();
                while let Some((k, v)) = lx.next() { match (k, v) {
                    (b"in", Val::Num(x)) => idx = x, (b"pre", Val::Num(x)) => p = x,
                    (b"i", Val::Num(x)) => c = x.to_string().into_boxed_str(),
                    (b"str", Val::Str(s)) => c = unescape(s).into_boxed_str(),
                    _ => {} } }
                let idx = idx as usize;
                if idx >= pre.len() { pre.resize(idx + 1, 0); comp.resize(idx + 1, "".into()); }
                pre[idx] = p as u32; comp[idx] = c;
                if idx >= g.node_of_name.len() { g.node_of_name.resize(idx + 1, NONE); }
                if !watch_last.is_empty() && watch_last.contains(&*comp[idx]) {
                    let fl = full(&pre, &comp, idx as u32);
                    if watch_full.contains(&fl) { g.watch.insert(idx as u32); watch_seen.push(fl); }
                }
            }
            "bvar" | "const" | "forallE" | "ie" => {
                let mut lx = Lex::new(b);
                let (mut ie, mut body, mut ty, mut val, mut st, mut tn, mut cname, mut ex, mut pidx) = (0u64, u64::MAX, u64::MAX, u64::MAX, u64::MAX, u64::MAX, u64::MAX, u64::MAX, u64::MAX);
                let mut ek: &'static str = kind; let mut is_const = kind == "const"; let mut is_binder = kind == "forallE";
                while let Some((k, v)) = lx.next() {
                    match k {
                        b"lam" => { ek = "lam"; is_binder = true; } b"letE" => { ek = "letE"; is_binder = true; } b"proj" => { ek = "proj"; }
                        b"sort" => ek = "sort", b"natVal" => ek = "natVal", b"strVal" => ek = "strVal",
                        b"mdata" => ek = "mdata", b"const" => is_const = true, _ => {}
                    }
                    if let Val::Num(x) = v { match k {
                        b"ie" => ie = x, b"body" => body = x, b"type" => ty = x, b"value" => val = x, b"struct" => st = x,
                        b"typeName" => tn = x, b"expr" => ex = x, b"idx" => pidx = x,
                        b"name" => { if is_const && !is_binder { cname = x; } }
                        _ => {} } }
                }
                let u = |x: u64| if x == u64::MAX { NONE } else { x as u32 };
                let ie = ie as usize;
                match ek {
                    "const" => g.set(ie, T_CONST, u(cname), NONE),
                    "forallE" | "lam" => g.set(ie, T_TWO, u(ty), u(body)),
                    "letE" => { g.set(ie, T_LET, u(ty), u(body)); if val != u64::MAX { g.let_val.insert(ie as u32, val as u32); } }
                    "proj" => { g.set(ie, T_PROJ, u(st), u(tn)); if pidx != u64::MAX { g.proj_idx.insert(ie as u32, pidx as u32); } }
                    "mdata" => g.set(ie, T_ONE, u(ex), NONE),
                    _ => g.set(ie, T_LEAF, NONE, NONE),
                }
            }
            "def" | "thm" | "opaque" | "axiom" | "quot" => {
                *kinds.entry(kind).or_insert(0) += 1;
                let mut lx = Lex::new(b); let (mut name, mut ty, mut val) = (u64::MAX, u64::MAX, u64::MAX);
                while let Some((k, v)) = lx.next() { match (k, v) {
                    (b"name", Val::Num(x)) => { if name == u64::MAX { name = x; } }
                    (b"type", Val::Num(x)) => ty = x, (b"value", Val::Num(x)) => val = x,
                    _ => {} } }
                let me = n_nodes; n_nodes += 1;
                if me as usize >= g.node_stamp.len() { g.node_stamp.resize(me as usize + 1, 0); }
                tdeps.clear(); vdeps.clear();
                epoch += 1; let r = [if ty == u64::MAX { NONE } else { ty as u32 }];
                g.projs.clear(); g.hits.clear();
                g.collect(&r, epoch, me, &mut tdeps, &mut stack);
                for (s, i) in &g.projs { writeln!(projs_f, "{}\tT\t{}\t{}", me, full(&pre, &comp, *s), *i as i64).unwrap(); }
                for h in &g.hits { writeln!(hits_f, "{}\tT\t{}", me, full(&pre, &comp, *h)).unwrap(); }
                epoch += 1; let r = [if val == u64::MAX { NONE } else { val as u32 }];
                g.projs.clear(); g.hits.clear();
                g.collect(&r, epoch, me, &mut vdeps, &mut stack);
                for (s, i) in &g.projs { writeln!(projs_f, "{}\tV\t{}\t{}", me, full(&pre, &comp, *s), *i as i64).unwrap(); }
                for h in &g.hits { writeln!(hits_f, "{}\tV\t{}", me, full(&pre, &comp, *h)).unwrap(); }
                if name != u64::MAX { let nm = name as usize; if nm >= g.node_of_name.len() { g.node_of_name.resize(nm + 1, NONE); } g.node_of_name[nm] = me; }
                writeln!(nodes, "{}\t{}\t{}\t{}\t{}", me, kind, tdeps.len(), vdeps.len(), full(&pre, &comp, name as u32)).unwrap();
                n_names_decl += 1; n_te += tdeps.len() as u64; n_ve += vdeps.len() as u64;
                edges.write_all(&(tdeps.len() as u32).to_le_bytes()).unwrap(); edges.write_all(&(vdeps.len() as u32).to_le_bytes()).unwrap();
                for d in &tdeps { edges.write_all(&d.to_le_bytes()).unwrap(); } for d in &vdeps { edges.write_all(&d.to_le_bytes()).unwrap(); }
            }
            "inductive" => {
                *kinds.entry(kind).or_insert(0) += 1;
                let mut lx = Lex::new(b); let mut nms: Vec<u32> = Vec::new(); let mut roots: Vec<u32> = Vec::new();
                while let Some((k, v)) = lx.next() { if let Val::Num(x) = v { match k {
                    b"name" => nms.push(x as u32), b"type" | b"rhs" => roots.push(x as u32), _ => {} } } }
                let me = n_nodes; n_nodes += 1;
                if me as usize >= g.node_stamp.len() { g.node_stamp.resize(me as usize + 1, 0); }
                for nm in &nms { let k = *nm as usize; if k >= g.node_of_name.len() { g.node_of_name.resize(k + 1, NONE); } g.node_of_name[k] = me; }
                tdeps.clear(); vdeps.clear(); epoch += 1;
                g.projs.clear(); g.hits.clear();
                g.collect(&roots, epoch, me, &mut tdeps, &mut stack);
                for (s, i) in &g.projs { writeln!(projs_f, "{}\tT\t{}\t{}", me, full(&pre, &comp, *s), *i as i64).unwrap(); }
                for h in &g.hits { writeln!(hits_f, "{}\tT\t{}", me, full(&pre, &comp, *h)).unwrap(); }
                for nm in &nms { writeln!(nodes, "{}\t{}\t{}\t{}\t{}", me, kind, tdeps.len(), 0, full(&pre, &comp, *nm)).unwrap(); n_names_decl += 1; }
                n_te += tdeps.len() as u64;
                edges.write_all(&(tdeps.len() as u32).to_le_bytes()).unwrap(); edges.write_all(&0u32.to_le_bytes()).unwrap();
                for d in &tdeps { edges.write_all(&d.to_le_bytes()).unwrap(); }
            }
            _ => { *kinds.entry("unknown").or_insert(0) += 1; }
        }
    }
    nodes.flush().unwrap(); edges.flush().unwrap(); projs_f.flush().unwrap(); hits_f.flush().unwrap();
    watch_seen.sort();
    let never: Vec<&String> = { let mut v: Vec<&String> = watch_full.iter().filter(|w| !watch_seen.contains(w)).collect(); v.sort(); v };
    let mut s = std::fs::File::create(format!("{}/depgraph_summary.txt", outdir)).unwrap();
    let msg = format!("lines: {}\nbytes: {}\nexpression records: {}\ndeclaration records (graph nodes): {}\ndeclared names: {}\nrecords by kind: {:?}\ntype-dependency edges: {}\nvalue-dependency edges: {}\nexpression-DAG visits during the walk: {}\nwatched names present in the export: {:?}\nwatched names that never occur in the export: {:?}\n",
        nlines, nbytes, g.tag.len(), n_nodes, n_names_decl, kinds, n_te, n_ve, g.visits, watch_seen, never);
    print!("{}", msg); s.write_all(msg.as_bytes()).unwrap();
}
