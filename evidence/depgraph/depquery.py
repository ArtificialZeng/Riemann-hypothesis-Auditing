#!/usr/bin/env python3
"""Queries on the declaration-level dependency graph written by `depgraph`.

Usage: python3 -I depquery.py GRAPH_DIR MATHLIB_NAMES.txt OUT_DIR

GRAPH_DIR must contain nodes.tsv and edges.bin (see ../conescan/src/bin/depgraph.rs).
MATHLIB_NAMES.txt lists every constant of the environment `import Mathlib` (see DumpNames.lean);
a declaration whose name is not in that list is counted as declared by the release ("project").

Terminology
  dependency cone of X   all declarations X transitively refers to, through types and values
  statement cone of X    what the STATEMENT of X refers to: the type of X, then, transitively,
                         type+value of every definition / inductive / axiom met, but only the
                         TYPE of every theorem met (a proof occurring inside a statement matters
                         only through what it proves)
  dependents of S        all declarations that transitively refer to some member of S
"""
import sys, os, json, collections
import numpy as np

gdir, mathlib_file, outdir = sys.argv[1], sys.argv[2], sys.argv[3]
os.makedirs(outdir, exist_ok=True)

# ---------------------------------------------------------------- load
kind_of, names_of, primary = [], [], []
name2node = {}
with open(os.path.join(gdir, "nodes.tsv"), encoding="utf-8", errors="replace") as f:
    for line in f:
        p = line.rstrip("\n").split("\t", 4)
        nid = int(p[0]); nm = p[4] if len(p) > 4 else ""
        if nid == len(kind_of):
            kind_of.append(p[1]); names_of.append([nm]); primary.append(nm)
        else:
            names_of[nid].append(nm)
        name2node[nm] = nid
N = len(kind_of)
raw = np.fromfile(os.path.join(gdir, "edges.bin"), dtype="<u4")
t_ptr = np.zeros(N + 1, dtype=np.int64); v_ptr = np.zeros(N + 1, dtype=np.int64)
t_chunks, v_chunks = [], []
pos = 0
for i in range(N):
    nt = int(raw[pos]); nv = int(raw[pos + 1]); pos += 2
    t_chunks.append(raw[pos:pos + nt]); pos += nt
    v_chunks.append(raw[pos:pos + nv]); pos += nv
    t_ptr[i + 1] = t_ptr[i] + nt; v_ptr[i + 1] = v_ptr[i] + nv
assert pos == len(raw), (pos, len(raw))
t_idx = np.concatenate(t_chunks) if t_chunks else np.zeros(0, dtype="<u4")
v_idx = np.concatenate(v_chunks) if v_chunks else np.zeros(0, dtype="<u4")
del t_chunks, v_chunks

mathlib = set(l.rstrip("\n") for l in open(mathlib_file, encoding="utf-8", errors="replace"))
is_lib = np.array([any(n in mathlib for n in names_of[i]) for i in range(N)], dtype=bool)
is_thm = np.array([k == "thm" for k in kind_of], dtype=bool)

# reverse adjacency (dependents), over type+value edges
src = np.concatenate([np.repeat(np.arange(N, dtype=np.int64), np.diff(t_ptr)), np.repeat(np.arange(N, dtype=np.int64), np.diff(v_ptr))])
dst = np.concatenate([t_idx.astype(np.int64), v_idx.astype(np.int64)])
order = np.argsort(dst, kind="stable")
r_idx = src[order]; r_ptr = np.zeros(N + 1, dtype=np.int64)
np.cumsum(np.bincount(dst, minlength=N), out=r_ptr[1:])
del src, dst, order

def deps(i, typ=True, val=True):
    out = []
    if typ: out.append(t_idx[t_ptr[i]:t_ptr[i + 1]])
    if val: out.append(v_idx[v_ptr[i]:v_ptr[i + 1]])
    return out

def cone(roots):
    """dependency cone (roots included)"""
    seen = np.zeros(N, dtype=bool); st = list(roots)
    for r in st: seen[r] = True
    while st:
        i = st.pop()
        for arr in deps(i):
            for j in arr[~seen[arr]]:
                j = int(j)
                if not seen[j]: seen[j] = True; st.append(j)
    return seen

def statement_cone(root):
    """see module docstring; root itself is not included"""
    seen = np.zeros(N, dtype=bool); st = []
    def push(arrs):
        for arr in arrs:
            for j in arr[~seen[arr]]:
                j = int(j)
                if not seen[j]: seen[j] = True; st.append(j)
    push(deps(root, typ=True, val=False))
    while st:
        i = st.pop()
        push(deps(i, typ=True, val=not is_thm[i]))
    return seen

def dependents(roots):
    seen = np.zeros(N, dtype=bool); st = list(roots)
    for r in st: seen[r] = True
    while st:
        i = st.pop()
        arr = r_idx[r_ptr[i]:r_ptr[i + 1]]
        for j in arr[~seen[arr]]:
            j = int(j)
            if not seen[j]: seen[j] = True; st.append(j)
    return seen

def find(suffix):
    """resolve a declaration by exact name, else by unique '.suffix' match"""
    if suffix in name2node: return name2node[suffix]
    c = [n for n in name2node if n.endswith("." + suffix)]
    if len(c) == 1: return name2node[c[0]]
    raise KeyError(f"{suffix}: {len(c)} candidates {c[:8]}")

def stats(mask):
    proj = mask & ~is_lib
    return {"all": int(mask.sum()), "library": int((mask & is_lib).sum()), "project": int(proj.sum()),
            "project_theorems": int((proj & is_thm).sum()), "project_other": int((proj & ~is_thm).sum())}

R = collections.OrderedDict()
log = open(os.path.join(outdir, "depquery_report.txt"), "w", encoding="utf-8")
def P(*a):
    s = " ".join(str(x) for x in a); print(s); log.write(s + "\n")

# ---------------------------------------------------------------- census
P("== census ==")
R["nodes"] = N; R["type_edges"] = int(len(t_idx)); R["value_edges"] = int(len(v_idx))
kc = collections.Counter(kind_of)
R["by_kind"] = dict(kc)
R["by_kind_project"] = dict(collections.Counter(k for k, l in zip(kind_of, is_lib) if not l))
R["by_kind_library"] = dict(collections.Counter(k for k, l in zip(kind_of, is_lib) if l))
P("declaration records:", N, dict(kc)); P("  project:", R["by_kind_project"]); P("  library:", R["by_kind_library"])
P("type edges:", len(t_idx), " value edges:", len(v_idx))
R["axioms"] = [primary[i] for i in range(N) if kind_of[i] == "axiom"]
P("axioms:", R["axioms"])
R["opaque_project"] = [primary[i] for i in range(N) if kind_of[i] == "opaque" and not is_lib[i]]
P("opaque records not from the library:", R["opaque_project"])

SEEDS = ["GlobalTheory.Mem.Top.Bl.anyGeometry", "Formalism.L2.Geo.geoDegenerate", "Formalism.L2.Geo.algDegenerate",
         "Formalism.L2.Geo.padDegenerate", "Formalism.L2.Geo.mdlJunk", "Formalism.L2.Geo.cxJunk", "Formalism.L2.Geo.divXFl",
         "GlobalTheory.Mem.Top.DivRec.geoOver_stages", "Formalism.L2.LPTiedPlaceholder",
         "GlobalTheory.HeightCounting.NTiedGPlaceholder", "Formalism.BasicNotions.Examples₂.geoExample",
         "GlobalTheory.PointGeometry.pointGeo", "GlobalTheory.Mem.Top.DivRec.x0", "GlobalTheory.provisionalDivX",
         "GlobalTheory.GeoGraft.graft"]
seed_nodes = {}
for s in SEEDS:
    try: seed_nodes[s] = find(s)
    except KeyError as e: P("SEED NOT FOUND", e)

main = find("riemannHypothesis")
main_cone = cone([main])
R["main_cone"] = stats(main_cone)
P("\n== dependency cone of riemannHypothesis ==", R["main_cone"])
R["main_statement_cone"] = stats(statement_cone(main))
P("statement cone of riemannHypothesis:", R["main_statement_cone"])

P("\n== dependents of the objects the paper calls vacuous ==")
R["dependents"] = {}
for s, n in seed_nodes.items():
    d = dependents([n]); d[n] = False
    R["dependents"][s] = {"count": int(d.sum()), "main_depends": bool(d[main])}
    P(f"  {int(d.sum()):6d} declarations depend on {s}   (riemannHypothesis among them: {bool(d[main])})")
NIELSEN = [s for s in SEEDS if "Placeholder" not in s]
nv = dependents([seed_nodes[s] for s in NIELSEN if s in seed_nodes])
R["dependents_union_flagged"] = stats(nv & main_cone)
P("  union over the objects flagged in [N] (anyGeometry, degenerate model, junk models, divXFl, geoOver_stages, geoExample), seeds included:", R["dependents_union_flagged"])
R["cone_free_of_flagged"] = stats(main_cone & ~nv)
P("  cone of riemannHypothesis NOT depending on any flagged object:", R["cone_free_of_flagged"])
with open(os.path.join(outdir, "dependents_of_flagged_objects.tsv"), "w", encoding="utf-8") as f:
    f.write("kind\tname\n")
    for i in np.nonzero(nv & main_cone)[0]: f.write(f"{kind_of[i]}\t{primary[i]}\n")
allv = dependents(list(seed_nodes.values()))
R["dependents_union"] = stats(allv & main_cone)
P("  union (seeds included), inside the cone of riemannHypothesis:", R["dependents_union"])
free = main_cone & ~allv
R["cone_free_of_vacuous"] = stats(free)
P("  cone of riemannHypothesis NOT depending on any of them:", R["cone_free_of_vacuous"])
with open(os.path.join(outdir, "dependents_of_vacuous_objects.tsv"), "w", encoding="utf-8") as f:
    f.write("kind\tname\n")
    for i in np.nonzero(allv & main_cone)[0]:
        f.write(f"{kind_of[i]}\t{primary[i]}\n")

TARGETS = ["riemannHypothesis", "rhOfAll", "allChi", "UpperTheory.FinalTheorems.everyCharacter",
           "UpperTheory.Top.every_character_of_green_v_win", "UpperTheory.Top.zero_free_all_of_green_v_win",
           "UpperTheory.Top.zeroFreeAll_of_topG", "UpperTheory.Top.shape_closed_link_n_of_green",
           "GlobalTheory.Fc.forall_goal_of_shape_of_hyps", "UpperTheory.Top.topDesWin",
           "UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound",
           "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
           "Formalism.L2.DIV.divClausesR_of", "wordFacts_of", "linkDIVt_closedK", "closed_linkDIVt_of_closed_bridge_kernel",
           "zeroFreeOn_of_tiedWin_cyc", "GlobalTheory.Fc.HypsAlt", "UpperTheory.Top.TopG", "UpperTheory.EveryCharacter",
           "Formalism.HC.ZeroFreeAll", "divEx_of_ox", "exists_divT", "hExpl6", "setDiv", "WordFacts", "DivInputsR",
           "SlopeBoundFamilyStatement", "degree_value_of_determinant", "GeoTiedP", "tiedX_fl", "tiedDataS_assemble_alt",
           "WeightCaseCondition", "InGeo", "exists_pre2_of_fine_of_resChar_mem", "LinkGLOBAL", "ChainTied",
           "GlobalTheoremInputs", "plugAll", "shapeWin", "everyE₂", "geoOf", "FrobeniusOrbitPlaceCount",
           "height_chain_atR", "complex_height_cast_at", "Formalism.DivisorInequality.boundsMu", "buRat_rrFull_closed_alt",
           "buRational_of", "mjH_good", "jM_lat", "jM_metric", "exists_mjHTie", "lamAre_of_eq", "kapSharp",
           "Formalism.VW.rh_of_every", "UpperTheory.Top.imprimitive", "UpperTheory.Top.supplyChi",
           "GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt",
           "GlobalTheory.Mem.Top.Bl.parametersOfDependence", "GlobalTheory.Mem.Top.DivRec.divEx_prov",
           "GlobalTheory.Mem.Top.DivRec.divEx_geoCl", "GlobalTheory.Fc.TopShapeAlt", "GlobalTheory.GLq.Green", "UpperTheory.Top.VWin"]
P("\n== targets ==")
R["targets"] = collections.OrderedDict()
for t in TARGETS:
    try: n = find(t)
    except KeyError as e:
        R["targets"][t] = {"present": False, "note": str(e)[:200]}; P(f"  ABSENT/AMBIGUOUS {t}: {str(e)[:160]}"); continue
    c = cone([n]); sc = statement_cone(n)
    info = {"present": True, "full_name": primary[n], "kind": kind_of[n], "in_cone_of_main": bool(main_cone[n]),
            "cone": stats(c), "statement_cone": stats(sc),
            "cone_contains": {s.split(".")[-1]: bool(c[m]) for s, m in seed_nodes.items()},
            "statement_contains": {s.split(".")[-1]: bool(sc[m]) for s, m in seed_nodes.items()},
            "direct_type_deps": int(t_ptr[n + 1] - t_ptr[n]), "direct_value_deps": int(v_ptr[n + 1] - v_ptr[n])}
    for extra in ["GlobalTheory.Mem.Top.Bl.GeoCl", "Formalism.BasicNotions.DV.Geo", "GlobalTheory.Mem.Top.Bl.GeoP"]:
        try:
            m = find(extra); info["cone_contains"][extra.split(".")[-1]] = bool(c[m]); info["statement_contains"][extra.split(".")[-1]] = bool(sc[m])
        except KeyError: pass
    R["targets"][t] = info
    P(f"  {primary[n]} [{kind_of[n]}] in cone of main: {bool(main_cone[n])}")
    P(f"      dependency cone: {info['cone']}")
    P(f"      statement cone : {info['statement_cone']}")
    P(f"      cone contains      : {[k for k, v in info['cone_contains'].items() if v]}")
    P(f"      statement contains : {[k for k, v in info['statement_contains'].items() if v]}")

# ---------------------------------------------------------------- direct occurrences (projections, watched names)
def load_tsv(fn, ncol):
    rows = []
    path = os.path.join(gdir, fn)
    if os.path.exists(path):
        for line in open(path, encoding="utf-8", errors="replace"):
            p = line.rstrip("\n").split("\t")
            if len(p) >= ncol: rows.append(p)
    return rows

P("\n== direct references to watched names ==")
R["watch"] = collections.OrderedDict()
hits = collections.defaultdict(list)
for nid, tv, nm in load_tsv("watch_hits.tsv", 3): hits[nm].append((int(nid), tv))
wl = [l.strip() for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "watch_names.txt"), encoding="utf-8") if l.strip() and not l.startswith("#")]
for w in wl:
    own = name2node.get(w)
    refs = sorted(set((primary[n], tv) for n, tv in hits.get(w, []) if n != own))
    selfrefs = sorted(set(tv for n, tv in hits.get(w, []) if n == own))
    R["watch"][w] = {"declared_in_export": own is not None, "direct_referrers_outside_own_block": len(set(r[0] for r in refs)),
                     "referenced_inside_own_block": bool(selfrefs), "referrers": [f"{a} [{b}]" for a, b in refs[:60]]}
    P(f"  {w}: declared={own is not None}; referrers outside its own declaration block: {len(set(r[0] for r in refs))}; inside own block: {bool(selfrefs)}")
    for a_, b_ in refs[:12]: P(f"        {b_} {a_}")
    if len(refs) > 12: P(f"        ... ({len(refs)} occurrences in all)")

P("\n== direct projection reads ==")
R["proj"] = collections.OrderedDict()
projs = collections.defaultdict(list)
for nid, tv, st, idx in load_tsv("projs.tsv", 4): projs[st].append((int(nid), tv, int(idx)))
def proj_report(label, st, idx=None):
    rows = [r for r in projs.get(st, []) if idx is None or r[2] == idx]
    readers = sorted(set(r[0] for r in rows))
    thm = [n for n in readers if is_thm[n]]
    fields = sorted(set(r[2] for r in rows))
    info = {"direct_readers": len(readers), "of_which_theorems": len(thm), "fields_read": fields,
            "readers": [f"{kind_of[n]} {primary[n]}" for n in readers[:80]]}
    if readers:
        d = dependents(readers)
        info["transitive_dependents_incl_readers"] = int(d.sum()); info["main_depends"] = bool(d[main])
    R["proj"][label] = info
    P(f"  {label}: {len(readers)} declarations contain the projection directly ({len(thm)} theorems); fields: {fields}; "
      f"transitive dependents: {info.get('transitive_dependents_incl_readers', 0)}")
    for n in readers[:14]: P(f"        {kind_of[n]:9s} {primary[n]}")
    if len(readers) > 14: P(f"        ... ({len(readers)} in all)")
proj_report("OAt field 0 (geo)", "GlobalTheory.Mem.Top.Bl.OAt", 0)
proj_report("OAt field 1 (lam)", "GlobalTheory.Mem.Top.Bl.OAt", 1)
proj_report("DV.Geo any field", "Formalism.BasicNotions.DV.Geo")
proj_report("DivX field 0 (geo)", "Formalism.BasicNotions.DivX", 0)
proj_report("DivT any field", "Formalism.BasicNotions.DivT")

# direct use of the field accessors of the geometry interface
acc = sorted(set(n for nm, n in name2node.items() if nm.startswith("Formalism.BasicNotions.DV.Geo.") and kind_of[n] == "def"))
accmask = np.zeros(N, dtype=bool); accmask[acc] = True
tsrc = np.repeat(np.arange(N, dtype=np.int64), np.diff(t_ptr)); vsrc = np.repeat(np.arange(N, dtype=np.int64), np.diff(v_ptr))
rt = set(tsrc[accmask[t_idx]].tolist()) - set(acc); rv = set(vsrc[accmask[v_idx]].tolist()) - set(acc)
R["geo_accessors"] = {"accessors_in_export": len(acc), "accessor_names": [primary[n].split(".")[-1] for n in acc],
                      "direct_referrers": len(rt | rv), "of_which_theorems": int(sum(is_thm[n] for n in (rt | rv))),
                      "theorems_whose_proof_refers": int(sum(is_thm[n] for n in rv))}
P("\n== field accessors of DV.Geo ==", R["geo_accessors"])
with open(os.path.join(outdir, "direct_users_of_geometry_fields.tsv"), "w", encoding="utf-8") as f:
    f.write("kind\tin_type\tin_value\tname\n")
    for n in sorted(rt | rv): f.write(f"{kind_of[n]}\t{int(n in rt)}\t{int(n in rv)}\t{primary[n]}\n")
del tsrc, vsrc
with open(os.path.join(outdir, "dependents_of_anyGeometry.tsv"), "w", encoding="utf-8") as f:
    d = dependents([seed_nodes["GlobalTheory.Mem.Top.Bl.anyGeometry"]]); d[seed_nodes["GlobalTheory.Mem.Top.Bl.anyGeometry"]] = False
    f.write("kind\tname\n")
    for i in np.nonzero(d)[0]: f.write(f"{kind_of[i]}\t{primary[i]}\n")

P("\n== the abstract geometry interface versus its degenerate instance ==")
for nm in ["Formalism.BasicNotions.DV.Geo", "Formalism.BasicNotions.DivX", "GlobalTheory.Mem.Top.Bl.GeoCl", "GlobalTheory.Mem.Top.Bl.GeoP", "GlobalTheory.Mem.Top.Bl.OAt",
           "Formalism.L2.Geo.GeoTiedP", "Formalism.L2.Geo.GeoOver", "Formalism.BasicNotions.DivT", "Formalism.L2.LPTiedPlaceholder", "GlobalTheory.HeightCounting.NTiedGPlaceholder"]:
    try: n = find(nm)
    except KeyError as e: P("  not found", nm); continue
    d = dependents([n]); d[n] = False
    R.setdefault("type_dependents", {})[nm] = stats(d & main_cone)
    P(f"  declarations depending on the declaration block of {nm}: {stats(d & main_cone)}")

json.dump(R, open(os.path.join(outdir, "depquery.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)
P("\nwritten:", os.path.join(outdir, "depquery.json"))
