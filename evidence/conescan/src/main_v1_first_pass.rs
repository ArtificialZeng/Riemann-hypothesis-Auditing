// conescan: single forward pass over a lean4export (format 3.x, NDJSON) stream.
// Computes, at kernel level, which declarations transitively depend on a set of
// "seed" constants (taint propagation), an axiom census, and declaration counts.
// No external crates. Usage:  zstd -dc --long=30 solution.ndjson.zst | conescan OUTDIR
use std::collections::HashMap;
use std::io::{self, BufRead, Write};

#[derive(Clone)]
enum Comp { Str(Box<str>), Num(u64) }

struct Lex<'a> { b: &'a [u8], i: usize }
enum Val<'a> { Num(u64), Str(&'a [u8]), Other }
impl<'a> Lex<'a> {
    fn new(b: &'a [u8]) -> Self { Lex { b, i: 0 } }
    // read a JSON string starting at opening quote; returns raw (still escaped) bytes
    fn read_str(&mut self) -> &'a [u8] {
        let b = self.b; let start = self.i + 1; let mut j = start;
        while j < b.len() {
            match b[j] { b'\\' => j += 2, b'"' => break, _ => j += 1 }
        }
        self.i = (j + 1).min(b.len());
        &b[start..j.min(b.len())]
    }
    // next (key, value) pair where value is a number or a string; other values yield Other
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
                } else if c == b'"' {
                    let v = self.read_str();
                    return Some((s, Val::Str(v)));
                } else { return Some((s, Val::Other)); }
            }
            // a string that was not a key (array element etc.): continue
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

struct Names { pre: Vec<u32>, comp: Vec<Comp> }
impl Names {
    fn full(&self, mut n: u32) -> String {
        let mut parts: Vec<String> = Vec::new();
        while n != 0 && (n as usize) < self.pre.len() {
            match &self.comp[n as usize] { Comp::Str(s) => parts.push(s.to_string()), Comp::Num(k) => parts.push(k.to_string()) }
            n = self.pre[n as usize];
        }
        parts.reverse(); parts.join(".")
    }
}

const SEEDS: &[(&str, u8)] = &[
    ("GlobalTheory.Mem.Top.Bl.anyGeometry", 0),
    ("GlobalTheory.Mem.Top.Bl.geoOf", 1),
    ("GlobalTheory.Mem.Top.Bl.GeoCl.rec", 2),
    // bit 3 = projection of field 0 (geo) out of GlobalTheory.Mem.Top.Bl.OAt (set on proj exprs) or const OAt.geo
    ("GlobalTheory.Mem.Top.Bl.OAt.geo", 3),
    ("UpperTheory.Top.plugAll", 4),
    ("UpperTheory.Top.every_character_of_green_v_win", 5),
    ("sorryAx", 6),
    ("GlobalTheory.Mem.Top.Bl.GeoCl", 7),
];
const BITNAMES: &[&str] = &["anyGeometry", "geoOf", "GeoCl.rec(elim)", "OAt.geo(proj)", "plugAll", "every_character_of_green_v_win", "sorryAx", "GeoCl(type)"];
const WATCH: &[&str] = &[
    "riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive",
    "rhOfAll", "allChi", "critAll", "claimAll", "RiemannHypothesis", "riemannZeta",
    "UpperTheory.FinalTheorems.everyCharacter", "UpperTheory.FinalTheorems.everyCharacter_of_row",
    "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin",
    "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
    "UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound",
    "UpperTheory.Top.every_character_of_green_v_win", "UpperTheory.Top.zero_free_all_of_green_v_win",
    "UpperTheory.Top.plugAll", "UpperTheory.Top.plugWin", "UpperTheory.Lit.everyE₂", "UpperTheory.Lit.hypsE₂",
    "GlobalTheory.Mem.Top.Bl.anyGeometry", "GlobalTheory.Mem.Top.Bl.geoOf", "GlobalTheory.Mem.Top.Bl.geoCl", "GlobalTheory.Mem.Top.Bl.GeoCl",
    "GlobalTheory.Mem.Top.Bl.GeoCl.rec", "GlobalTheory.Mem.Top.Bl.GeoCl.casesOn", "GlobalTheory.Mem.Top.Bl.GeoCl.recOn",
    "GlobalTheory.Mem.Top.Bl.OAt", "GlobalTheory.Mem.Top.Bl.OAt.geo", "GlobalTheory.Mem.Top.Bl.OAt.lam", "GlobalTheory.Mem.Top.Bl.OX",
    "GlobalTheory.Mem.Top.Bl.parametersOfDependence", "GlobalTheory.Mem.Top.Bl.parametersOfExtension", "GlobalTheory.Mem.Top.Bl.Parameters",
    "GlobalTheory.Mem.Top.Bl.prm0", "GlobalTheory.Mem.Top.Bl.prm1", "GlobalTheory.Mem.Top.Bl.prmR", "GlobalTheory.Mem.Top.Bl.Prm",
    "GlobalTheory.Fc.HypsAlt", "GlobalTheory.Fc.Hyps", "GlobalTheory.Glob.open_and_linked_of_stronger_extension_alt",
    "GlobalTheory.T.linkedAt_geometricWeakTies_of_tie", "GlobalTheory.T.open0_of_unitary_group_hypotheses",
    "GlobalTheory.ShFam.IsGeoOf", "GlobalTheory.ShFam.Pad.HasTrueSurf",
    "sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler", "propext", "Quot.sound", "Classical.choice",
];

fn main() {
    let outdir = std::env::args().nth(1).unwrap_or_else(|| ".".to_string());
    let stdin = io::stdin();
    let mut rd = io::BufReader::with_capacity(1 << 26, stdin.lock());
    let mut line: Vec<u8> = Vec::with_capacity(1 << 16);
    let mut names = Names { pre: vec![0], comp: vec![Comp::Str("".into())] };
    let mut taint: Vec<u8> = Vec::new();
    let mut seed_of_name: HashMap<u32, u8> = HashMap::new();      // name idx -> seed bitmask
    let mut decl_mask: HashMap<u32, u8> = HashMap::new();         // decl name idx -> taint mask
    let mut oat_name: u32 = u32::MAX;
    const NW: usize = 8;
    let mut wit_expr: Vec<HashMap<u32, u32>> = (0..NW).map(|_| HashMap::new()).collect(); // per bit: expr -> const name
    let mut tainted_decls: Vec<(u32, &'static str, u8, u8, [u32; NW])> = Vec::new(); // name, kind, tmask, vmask, witnesses
    let mut axioms: Vec<u32> = Vec::new();
    let mut quots: Vec<u32> = Vec::new();
    let mut kinds: HashMap<&'static str, u64> = HashMap::new();
    let mut ekinds: HashMap<&'static str, u64> = HashMap::new();
    let mut unsafe_flags: u64 = 0;
    let mut watch_idx: HashMap<String, u32> = HashMap::new();
    let watch_set: HashMap<&str, ()> = WATCH.iter().map(|s| (*s, ())).collect();
    let watch_last: HashMap<String, ()> = WATCH.iter().map(|s| (s.rsplit('.').next().unwrap().to_string(), ())).collect();
    let seed_last: HashMap<String, ()> = SEEDS.iter().map(|(s, _)| (s.rsplit('.').next().unwrap().to_string(), ())).collect();
    let mut decl_info: HashMap<u32, (&'static str, u32, u32)> = HashMap::new(); // watched decls: kind,type,value
    let mut const_expr: HashMap<u32, u32> = HashMap::new(); // expr idx -> const name idx (only for watched-name consts)
    let mut nlines: u64 = 0; let mut nbytes: u64 = 0; let mut meta = String::new();
    let mut n_names: u64 = 0;

    macro_rules! tget { ($e:expr) => {{ let x = $e as usize; if x < taint.len() { taint[x] } else { 0 } }} }

    loop {
        line.clear();
        let n = rd.read_until(b'\n', &mut line).expect("read");
        if n == 0 { break; }
        nlines += 1; nbytes += n as u64;
        if nlines % 100_000_000 == 0 { eprintln!("... {} M lines, {:.1} GB, exprs {}", nlines / 1_000_000, nbytes as f64 / 1e9, taint.len()); }
        let b = &line[..];
        if b.len() < 6 { continue; }
        // classify by prefix
        let is = |p: &[u8]| b.starts_with(p);
        if is(b"{\"app\":") {
            // {"app":{"arg":A,"fn":F},"ie":N}
            let mut lx = Lex::new(b); let (mut a, mut f, mut ie) = (0u64, 0u64, 0u64);
            while let Some((k, v)) = lx.next() { if let Val::Num(x) = v { match k { b"arg" => a = x, b"fn" => f = x, b"ie" => ie = x, _ => {} } } }
            let m = tget!(a) | tget!(f);
            let ie = ie as usize; if ie >= taint.len() { taint.resize(ie + 1, 0); }
            taint[ie] = m;
            if m != 0 { for bit in 0..NW { if m & (1 << bit) != 0 {
                let w = wit_expr[bit].get(&(f as u32)).or_else(|| wit_expr[bit].get(&(a as u32))).copied();
                if let Some(w) = w { wit_expr[bit].insert(ie as u32, w); } } } }
            *ekinds.entry("app").or_insert(0) += 1;
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
            "level" => {}
            "name" => {
                n_names += 1;
                let mut lx = Lex::new(b); let (mut idx, mut pre) = (0u64, 0u64); let mut comp = Comp::Str("".into()); let mut is_num = false;
                while let Some((k, v)) = lx.next() { match (k, v) {
                    (b"in", Val::Num(x)) => idx = x, (b"pre", Val::Num(x)) => pre = x,
                    (b"i", Val::Num(x)) => { comp = Comp::Num(x); is_num = true; }
                    (b"str", Val::Str(s)) => comp = Comp::Str(unescape(s).into_boxed_str()),
                    (b"num", _) => is_num = true,
                    _ => {} } }
                let _ = is_num;
                let idx = idx as usize;
                if idx >= names.pre.len() { names.pre.resize(idx + 1, 0); names.comp.resize(idx + 1, Comp::Str("".into())); }
                names.pre[idx] = pre as u32;
                let last = match &comp { Comp::Str(s) => s.to_string(), Comp::Num(k) => k.to_string() };
                names.comp[idx] = comp;
                if seed_last.contains_key(&last) || watch_last.contains_key(&last) {
                    let full = names.full(idx as u32);
                    for (s, bit) in SEEDS { if *s == full { *seed_of_name.entry(idx as u32).or_insert(0) |= 1 << bit; } }
                    if full == "GlobalTheory.Mem.Top.Bl.OAt" { oat_name = idx as u32; }
                    if watch_set.contains_key(full.as_str()) { watch_idx.insert(full, idx as u32); }
                }
            }
            "bvar" | "const" | "forallE" | "ie" => {
                let mut lx = Lex::new(b);
                let (mut ie, mut body, mut ty, mut val, mut st, mut tn, mut pidx, mut cname, mut ex) = (0u64, u64::MAX, u64::MAX, u64::MAX, u64::MAX, u64::MAX, u64::MAX, u64::MAX, u64::MAX);
                let mut ek: &'static str = kind; let mut first = true; let mut is_proj = false; let mut is_const = kind == "const"; let mut is_binder = kind == "forallE";
                while let Some((k, v)) = lx.next() {
                    if first { first = false; }
                    match k {
                        b"lam" => { ek = "lam"; is_binder = true; } b"letE" => { ek = "letE"; is_binder = true; } b"proj" => { ek = "proj"; is_proj = true; }
                        b"sort" => ek = "sort", b"natVal" => ek = "natVal", b"strVal" => { ek = "strVal"; }
                        b"mdata" => ek = "mdata", b"const" => is_const = true, _ => {}
                    }
                    if let Val::Num(x) = v { match k {
                        b"ie" => ie = x, b"body" => body = x, b"type" => ty = x, b"value" => val = x, b"struct" => st = x,
                        b"typeName" => tn = x, b"idx" => pidx = x, b"expr" => ex = x,
                        b"name" => { if is_const && !is_binder { cname = x; } }
                        _ => {} } }
                    if ek == "strVal" || ek == "natVal" { /* literal: nothing else matters */ }
                }
                *ekinds.entry(ek).or_insert(0) += 1;
                let mut m: u8 = 0; let mut wsrc: [u32; NW] = [u32::MAX; NW];
                for c in [body, ty, val, st, ex] { if c != u64::MAX { let t = tget!(c); if t != 0 { m |= t;
                    for bit in 0..NW { if t & (1 << bit) != 0 && wsrc[bit] == u32::MAX { if let Some(w) = wit_expr[bit].get(&(c as u32)) { wsrc[bit] = *w; } } } } } }
                if is_const && cname != u64::MAX {
                    let cn = cname as u32; let mut cm = 0u8;
                    if let Some(s) = seed_of_name.get(&cn) { cm |= *s; }
                    if let Some(d) = decl_mask.get(&cn) { cm |= *d; }
                    if cm != 0 { m |= cm; for bit in 0..NW { if cm & (1 << bit) != 0 { wsrc[bit] = cn; } } }
                    if !watch_idx.is_empty() { const_expr.insert(ie as u32, cn); }
                }
                if is_proj && tn != u64::MAX && tn as u32 == oat_name && pidx == 0 { m |= 1 << 3; wsrc[3] = oat_name; }
                let ie = ie as usize; if ie >= taint.len() { taint.resize(ie + 1, 0); }
                taint[ie] = m;
                if m != 0 { for bit in 0..NW { if m & (1 << bit) != 0 && wsrc[bit] != u32::MAX { wit_expr[bit].insert(ie as u32, wsrc[bit]); } } }
            }
            "def" | "thm" | "opaque" | "axiom" | "quot" => {
                *kinds.entry(kind).or_insert(0) += 1;
                let mut lx = Lex::new(b); let (mut name, mut ty, mut val) = (u64::MAX, u64::MAX, u64::MAX);
                while let Some((k, v)) = lx.next() { match (k, v) {
                    (b"name", Val::Num(x)) => name = x, (b"type", Val::Num(x)) => ty = x, (b"value", Val::Num(x)) => val = x,
                    (b"safety", Val::Str(s)) => { if s != b"safe" { unsafe_flags += 1; } }
                    _ => {} } }
                if b.windows(15).any(|w| w == b"\"isUnsafe\":true") { unsafe_flags += 1; }
                let nm = name as u32;
                if kind == "axiom" { axioms.push(nm); } if kind == "quot" { quots.push(nm); }
                let tm = if ty != u64::MAX { tget!(ty) } else { 0 }; let vm = if val != u64::MAX { tget!(val) } else { 0 };
                let mut self_seed = 0u8; if let Some(s) = seed_of_name.get(&nm) { self_seed = *s; }
                let m = tm | vm;
                if m != 0 {
                    decl_mask.insert(nm, m);
                    let mut w = [u32::MAX; NW];
                    for bit in 0..NW { if m & (1 << bit) != 0 {
                        let a = if val != u64::MAX { wit_expr[bit].get(&(val as u32)).copied() } else { None };
                        let c = if ty != u64::MAX { wit_expr[bit].get(&(ty as u32)).copied() } else { None };
                        w[bit] = a.or(c).unwrap_or(u32::MAX); } }
                    tainted_decls.push((nm, kind, tm, vm, w));
                }
                let _ = self_seed;
                if watch_idx.values().any(|x| *x == nm) { decl_info.insert(nm, (kind, ty as u32, val as u32)); }
            }
            "inductive" => {
                *kinds.entry(kind).or_insert(0) += 1;
                if b.windows(15).any(|w| w == b"\"isUnsafe\":true") { unsafe_flags += 1; }
                let mut lx = Lex::new(b); let mut nms: Vec<u32> = Vec::new(); let mut m = 0u8; let mut w = [u32::MAX; NW];
                while let Some((k, v)) = lx.next() { if let Val::Num(x) = v { match k {
                    b"name" => nms.push(x as u32),
                    b"type" | b"rhs" => { let t = tget!(x); if t != 0 { m |= t; for bit in 0..NW { if t & (1 << bit) != 0 && w[bit] == u32::MAX {
                        if let Some(ww) = wit_expr[bit].get(&(x as u32)) { w[bit] = *ww; } } } } }
                    _ => {} } } }
                for nm in &nms { if watch_idx.values().any(|x| x == nm) { decl_info.insert(*nm, ("inductive", u32::MAX, u32::MAX)); } }
                if m != 0 { for nm in &nms { decl_mask.insert(*nm, m); tainted_decls.push((*nm, "inductive", m, 0, w)); } }
            }
            "meta" => { meta = String::from_utf8_lossy(b).trim().to_string(); }
            _ => { *kinds.entry("unknown").or_insert(0) += 1; if kinds["unknown"] < 5 { eprintln!("UNKNOWN LINE: {}", String::from_utf8_lossy(&b[..b.len().min(200)])); } }
        }
    }

    // ---------- report ----------
    let mut out = std::fs::File::create(format!("{}/conescan_report.txt", outdir)).unwrap();
    let mut p = |s: String| { println!("{}", s); writeln!(out, "{}", s).unwrap(); };
    p(format!("meta: {}", meta));
    p(format!("lines: {}  bytes: {}  names: {}  exprs: {}", nlines, nbytes, n_names, taint.len()));
    let mut kv: Vec<_> = kinds.iter().collect(); kv.sort();
    p(format!("declaration records by kind: {:?}", kv));
    let total: u64 = kinds.iter().filter(|(k, _)| **k != "unknown").map(|(_, v)| *v).sum();
    p(format!("total declaration records: {}", total));
    let mut ev: Vec<_> = ekinds.iter().collect(); ev.sort();
    p(format!("expression records by kind: {:?}", ev));
    p(format!("records flagged unsafe/partial: {}", unsafe_flags));
    p(format!("AXIOMS in export ({}): {:?}", axioms.len(), axioms.iter().map(|a| names.full(*a)).collect::<Vec<_>>()));
    p(format!("QUOT primitives ({}): {:?}", quots.len(), quots.iter().map(|a| names.full(*a)).collect::<Vec<_>>()));
    p("".into());
    p("WATCHED NAMES: present in export (= in the dependency cone of the 5 exported theorems)?".into());
    for w in WATCH {
        match watch_idx.get(*w) {
            None => p(format!("  ABSENT (name never interned)   {}", w)),
            Some(idx) => {
                let di = decl_info.get(idx);
                let dm = decl_mask.get(idx).copied().unwrap_or(0);
                let bits: Vec<&str> = (0..NW).filter(|b| dm & (1 << b) != 0).map(|b| BITNAMES[b]).collect();
                match di {
                    None => p(format!("  NAME-ONLY (interned, but no declaration record)   {}", w)),
                    Some((k, ty, _)) => {
                        let tyc = const_expr.get(ty).map(|c| names.full(*c));
                        p(format!("  PRESENT [{}]  {}   type-is-const: {:?}   depends-on: {:?}", k, w, tyc, bits)) } }
            }
        }
    }
    p("".into());
    for bit in 0..NW {
        let ds: Vec<_> = tainted_decls.iter().filter(|d| (d.2 | d.3) & (1 << bit) != 0).collect();
        p(format!("SEED bit {} [{}]: {} declarations transitively depend on it", bit, BITNAMES[bit], ds.len()));
        let mut f = std::fs::File::create(format!("{}/tainted_bit{}_{}.tsv", outdir, bit, BITNAMES[bit].replace(|c: char| !c.is_alphanumeric(), "_"))).unwrap();
        writeln!(f, "kind\tin_type\tin_value\tdirect_witness\tname").unwrap();
        for d in &ds {
            let w = if d.4[bit] == u32::MAX { "-".to_string() } else { names.full(d.4[bit]) };
            writeln!(f, "{}\t{}\t{}\t{}\t{}", d.1, (d.2 >> bit) & 1, (d.3 >> bit) & 1, w, names.full(d.0)).unwrap();
        }
    }
    p("".into());
    // witness chains from main theorems back to seeds 0,2,3
    let wmap: Vec<HashMap<u32, u32>> = (0..NW).map(|bit| tainted_decls.iter().filter(|d| d.4[bit] != u32::MAX).map(|d| (d.0, d.4[bit])).collect()).collect();
    for bit in [0usize, 1, 2, 3, 4, 5, 6] {
        for t in ["riemannHypothesis", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive", "riemannZeta_eq_zero_re"] {
            if let Some(idx) = watch_idx.get(t) {
                let dm = decl_mask.get(idx).copied().unwrap_or(0);
                if dm & (1 << bit) == 0 { p(format!("CHAIN[{}] {}: NOT dependent", BITNAMES[bit], t)); continue; }
                let mut chain = vec![names.full(*idx)]; let mut cur = *idx; let mut guard = 0;
                while let Some(nx) = wmap[bit].get(&cur) { chain.push(names.full(*nx)); if *nx == cur { break; } cur = *nx; guard += 1; if guard > 200 { break; } }
                p(format!("CHAIN[{}] {}:", BITNAMES[bit], t)); for (i, c) in chain.iter().enumerate() { p(format!("      {:2}. {}", i, c)); }
            }
        }
    }
}
