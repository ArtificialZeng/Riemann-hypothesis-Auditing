#!/usr/bin/env python3
"""Generate verbatim source excerpts (with true line numbers) for the audit report.
Usage: python3 -I make_excerpts.py <path to source tree root (dir containing src/)> <output dir>"""
import sys, os, re, json
root, out = sys.argv[1], sys.argv[2]
D = "src/Development/"
A = D + "AbelianVarietyTheory/Definitions/AutomorphicMembership/"
T = D + "AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/"
I = D + "AbelianVarietyTheory/Proofs/IwasawaDecomposition/"
# (id, file, start-regex, number of lines, max columns)
SPEC = [
 ("anygeo",      A + "OverIx.lean", r"^abbrev GeoP", 6, 200),
 ("oat",         A + "OverIx.lean", r"^structure OAt", 6, 200),
 ("geocl",       A + "NotGeoClFalse.lean", r"^inductive GeoCl", 8, 200),
 ("main",        "src/Main.lean", r"^import Statements", 12, 200),
 ("maintheorems","src/Supplements/Kernels/MainTheorems.lean", r"^theorem allChi", 3, 200),
 ("mainconcl",   D + "AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean", r"^theorem UpperTheory.FinalTheorems.everyCharacter_of_row", 5, 230),
 ("lit810",      T + "EveryCharacterOfLiteratureOfVWin.lean", r"^theorem UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin", 2, 250),
 ("siegel_a",    T + "SiegelEisensteinSecondTermHypotheses.lean", r"^  have hMono :=", 9, 215),
 ("siegel_b",    T + "SiegelEisensteinSecondTermHypotheses.lean", r"^theorem every_character_of_theta_integrals_local_matching", 5, 260),
 ("topplug",     T + "TopPlug.lean", r"^theorem UpperTheory.Top.every_character_of_green_v_win", 3, 230),
 ("plugall",     D + "AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean", r"^theorem UpperTheory.Top.plugAll", 3, 200),
 ("everyE2",     D + "AutomorphicArithmetic/ThetaCorrespondence/FockModels/EveryCharacterE.lean", r"^theorem everyE₂", 5, 215),
 ("prm1",        T + "Prm1.lean", r"^@\[reducible\] def parametersOfDependence", 2, 230),
 ("params",      T + "CoreAltAltBis.lean", r"^structure Parameters", 7, 215),
 ("mono_sig",    T + "OpenAndLinkedOfStrongerExtension.lean", r"^theorem open_and_linked_of_stronger_extension_alt", 1, 330),
 ("geo0_sig",    T + "RowGeo0AtStatement.lean", r"^theorem _root_.GlobalTheory.T.linkedAt_geometricWeakTies_of_tie", 1, 760),
 ("openorbit",   T + "OpenOrbitOfUnramifiedExponents.lean", r"^  have hGeo :=", 1, 300),
 ("openstmt",    T + "GeometricWeakTies.lean", r"^structure OpenParameterStatements", 13, 200),
 ("hypsalt",     T + "Hyps.lean", r"^structure HypsAlt", 9, 215),
 ("divexprov",   I + "TupPinsOfMuIsW.lean", r"^theorem divEx_prov", 6, 200),
 ("divexgeocl",  I + "PublishedInputsImplyConclusion.lean", r"^theorem divEx_geoCl", 11, 200),
 ("oatsetdiv",   I + "DivisionGeometryScalarsTransferSetDivision.lean", r"GeoCl\.step", 1, 200),
 ("geodegen",    "src/Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean", r"^@\[reducible\] def geoDegenerate", 20, 200),
 ("divxfl",      "src/Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean", r"^def divXFl", 6, 200),
 ("geoover",     I + "TupPinsOfMuIsW.lean", r"^theorem geoOver_stages", 1, 200),
 ("geoover2",    I + "TupPinsOfMuIsW.lean", r"^  refine ⟨divXFl D jc X₀, fun _ _ => True", 3, 215),
 ("heighteq",    D + "AbelianVarietyTheory/Definitions/GlobalTwisting/SetUnipotentTranslate.lean", r"^def ht : D.what₂.Word", 22, 200),
 ("buildaid",    "src/BuildAid/D3.lean", r"^import Lean.LibrarySuggestions", 4, 200),
 ("cptcopy",     "src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean", r"^def copyAll", 17, 200),
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
    cut = [(l if len(l) <= maxc else l[:maxc] + " …[本行在报告中截断]") for l in chunk]
    open(os.path.join(out, eid + ".txt"), "w", encoding="utf-8").write("\n".join(cut) + "\n")
    meta[eid] = {"file": f, "first": start + 1, "last": start + len(chunk)}
    print(f"{eid:14s} {f}:{start+1}-{start+len(chunk)}")
json.dump(meta, open(os.path.join(out, "excerpts.json"), "w"), indent=1, ensure_ascii=False)
# also emit a TeX file with \excerptfile{id}{path}{first}{last} definitions
with open(os.path.join(out, "excerpts_meta.tex"), "w", encoding="utf-8") as g:
    for eid, m in meta.items():
        g.write("\\expandafter\\def\\csname ex@%s@first\\endcsname{%d}\n" % (eid, m["first"]))
        g.write("\\expandafter\\def\\csname ex@%s@last\\endcsname{%d}\n" % (eid, m["last"]))
        g.write("\\expandafter\\def\\csname ex@%s@file\\endcsname{\\path{%s}}\n" % (eid, m["file"]))
