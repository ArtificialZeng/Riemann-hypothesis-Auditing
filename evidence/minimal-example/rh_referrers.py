#!/usr/bin/env python3
"""Which declarations of the proof export refer DIRECTLY to the constant `RiemannHypothesis`,
in their type (statement) or in their value (proof / body)?
It also prints the direct references of the last declarations on the route.
GRAPH_DIR holds nodes.tsv and edges.bin written by `depgraph` (see ../REPRODUCE.md, section 3).
Usage: python3 -I rh_referrers.py GRAPH_DIR MATHLIB_NAMES.txt"""
import sys, os
import numpy as np
gdir, mathlib_file = sys.argv[1], sys.argv[2]
kind_of, names_of = [], []
name2node = {}
with open(os.path.join(gdir, "nodes.tsv"), encoding="utf-8", errors="replace") as f:
    for line in f:
        p = line.rstrip("\n").split("\t", 4)
        nid = int(p[0]); nm = p[4] if len(p) > 4 else ""
        if nid == len(kind_of):
            kind_of.append(p[1]); names_of.append([nm])
        else:
            names_of[nid].append(nm)
        name2node[nm] = nid
N = len(kind_of)
mathlib = set(l.rstrip("\n") for l in open(mathlib_file, encoding="utf-8", errors="replace"))
raw = np.fromfile(os.path.join(gdir, "edges.bin"), dtype="<u4")
target = name2node["RiemannHypothesis"]
print("declarations:", N, " target node:", target, kind_of[target], names_of[target],
      "library" if names_of[target][0] in mathlib else "RELEASE")
pos = 0; in_type, in_value = [], []
edges = {}
want = {name2node[n] for n in ("riemannHypothesis", "rhOfAll", "allChi", "Formalism.VW.rh_of_every") if n in name2node}
for i in range(N):
    nt = int(raw[pos]); nv = int(raw[pos + 1]); pos += 2
    t = raw[pos:pos + nt]; pos += nt
    v = raw[pos:pos + nv]; pos += nv
    if nt and (t == target).any(): in_type.append(i)
    if nv and (v == target).any(): in_value.append(i)
    if i in want: edges[i] = (t.tolist(), v.tolist())
assert pos == len(raw)
def show(lst, label):
    lib = [i for i in lst if any(n in mathlib for n in names_of[i])]
    rel = [i for i in lst if i not in set(lib)]
    print(f"\n{label}: {len(lst)} total = {len(lib)} library + {len(rel)} release")
    for i in rel: print("   RELEASE", kind_of[i], " | ".join(names_of[i]))
    for i in lib[:12]: print("   library", kind_of[i], " | ".join(names_of[i]))
    if len(lib) > 12: print("   library … and", len(lib) - 12, "more")
show(in_type, "refer to RiemannHypothesis in their TYPE")
show(in_value, "refer to RiemannHypothesis in their VALUE")
for i, (t, v) in edges.items():
    print(f"\n{names_of[i][0]} [{kind_of[i]}]")
    print("   type  refers to:", [names_of[j][0] for j in t])
    print("   value refers to:", [names_of[j][0] for j in v])
