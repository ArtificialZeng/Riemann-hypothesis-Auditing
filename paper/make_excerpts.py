#!/usr/bin/env python3
"""Generate verbatim source excerpts (with true line numbers) for the paper.
Usage: python3 -I make_excerpts.py <source tree root (dir containing src/)> <output dir>
Every excerpt is cut mechanically from the author's original archive; nothing is retyped."""
import sys, os, re, json
root, out = sys.argv[1], sys.argv[2]
D = "src/Development/"
A = D + "AbelianVarietyTheory/Definitions/AutomorphicMembership/"
T = D + "AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/"
I = D + "AbelianVarietyTheory/Proofs/IwasawaDecomposition/"
F = "src/Formalism/LocalToGlobal/Divisibility/"
# (id, file, start-regex, number of lines, max columns)
SPEC = [
 ("anygeo",      A + "OverIx.lean", r"^abbrev GeoP", 6, 200),
 ("oat",         A + "OverIx.lean", r"^structure OAt", 6, 200),
 ("geocl",       A + "NotGeoClFalse.lean", r"^inductive GeoCl", 8, 200),
 ("main",        "src/Main.lean", r"^import Statements", 12, 200),
 ("maintheorems","src/Supplements/Kernels/MainTheorems.lean", r"^theorem allChi", 3, 200),
 ("siegel_a",    T + "SiegelEisensteinSecondTermHypotheses.lean", r"^  have hMono :=", 9, 205),
 ("zfa",         T + "TopPlug.lean", r"^theorem UpperTheory.Top.zero_free_all_of_green_v_win", 7, 250),
 ("shapeof",     T + "ShapeOf.lean", r"^theorem GlobalTheory.Fc.forall_goal_of_shape_of_hyps", 2, 300),
 ("topshape",    T + "TopShape.lean", r"^theorem UpperTheory.Top.shape_closed_link_n_of_green", 1, 300),
 ("topg",        D + "AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean", r"^def TopG : Prop", 3, 200),
 ("zfatopg",     D + "AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean", r"^theorem zeroFreeAll_of_topG", 9, 215),
 ("params",      T + "CoreAltAltBis.lean", r"^structure Parameters", 7, 215),
 ("mono_sig",    T + "OpenAndLinkedOfStrongerExtension.lean", r"^theorem open_and_linked_of_stronger_extension_alt", 1, 330),
 ("hypsalt",     T + "Hyps.lean", r"^structure HypsAlt", 6, 215),
 ("divexprov",   I + "TupPinsOfMuIsW.lean", r"^theorem divEx_prov", 6, 200),
 ("divexgeocl",  I + "PublishedInputsImplyConclusion.lean", r"^theorem divEx_geoCl", 11, 200),
 ("geodegen",    "src/Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean", r"^@\[reducible\] def geoDegenerate", 14, 200),
 ("existsdivt",  I + "TupPinsOfMuIsW.lean", r"^  refine ⟨GlobalTheory.GeoGraft.graft Xg X₂ iM hiM,", 4, 215),
 ("heighteq",    D + "AbelianVarietyTheory/Definitions/GlobalTwisting/SetUnipotentTranslate.lean", r"^def ht : D.what₂.Word", 22, 200),
 ("hexpl6",      "src/Formalism/LocalRingCardinality/KernelPlaceMeanBound.lean", r"^def hExpl6", 3, 200),
 ("wordfacts",   F + "RecBridge.lean", r"^def WordFacts", 6, 200),
 ("wordfactsof", F + "RecBridge.lean", r"^theorem wordFacts_of", 19, 200),
 ("divclauses",  F + "ConstantGeTwentyEight.lean", r"^def DivClausesR", 11, 200),
 ("divclausesof",F + "ConstantGeTwentyEight.lean", r"^theorem divClausesR_of", 26, 215),
 ("divclausesof2",F + "ConstantGeTwentyEight.lean", r"^    have hB := P.base.boundsMu", 2, 215),
 ("divclausesof3",F + "ConstantGeTwentyEight.lean", r"^    exact R.divIneq", 1, 215),
 ("kcopy",       "src/Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean", r"^  if let \.const S us := tgt.getAppFn then", 12, 200),
]
os.makedirs(out, exist_ok=True)
meta = {}
for (eid, f, rx, n, maxc) in SPEC:
    lines = open(os.path.join(root, f), encoding="utf-8").read().split("\n")
    start = next((i for i, l in enumerate(lines) if re.search(rx, l)), None)
    if start is None:
        print("ANCHOR NOT FOUND", eid, f, rx); sys.exit(1)
    chunk = lines[start:start + n]
    cut = [(l if len(l) <= maxc else l[:maxc] + " …[line truncated here]") for l in chunk]
    open(os.path.join(out, eid + ".txt"), "w", encoding="utf-8").write("\n".join(cut) + "\n")
    meta[eid] = {"file": f, "first": start + 1, "last": start + len(chunk)}
    print(f"{eid:14s} {f}:{start+1}-{start+len(chunk)}")
json.dump(meta, open(os.path.join(out, "excerpts.json"), "w"), indent=1, ensure_ascii=False)
with open(os.path.join(out, "excerpts_meta.tex"), "w", encoding="utf-8") as g:
    for eid, m in meta.items():
        g.write("\\expandafter\\def\\csname ex@%s@first\\endcsname{%d}\n" % (eid, m["first"]))
        g.write("\\expandafter\\def\\csname ex@%s@last\\endcsname{%d}\n" % (eid, m["last"]))
        g.write("\\expandafter\\def\\csname ex@%s@file\\endcsname{\\path{%s}}\n" % (eid, m["file"]))
