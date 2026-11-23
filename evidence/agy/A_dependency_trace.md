# Audit Task A — Declaration-Level Dependency Trace of `anyGeometry` and `geoOf`

**Repository audited:** `~/rh-audit/src/omega` (commit `c7d25b3bfd7906388bb8eb0774e027a2b756a7b6`, read-only source inspection; Lean 4 not installed).  
**Target theorem:** `riemannHypothesis : RiemannHypothesis` in `src/Main.lean:4`.  
**Scope:** Declaration-level dependency analysis (not merely file-import reachability) of `GlobalTheory.Mem.Top.Bl.anyGeometry`, `GlobalTheory.Mem.Top.Bl.geoOf`, `UpperTheory.Lit.everyE₂` / `hypsE₂`, `UpperTheory.Top.plugAll` / `GlobalTheory.Fc.Hyps`, and their active `ThirdPlaceSeries` counterparts.

---

## 1. Executive Summary of Findings

1. **`anyGeometry` IS rigorously on the declaration-level dependency cone of `Main.lean:riemannHypothesis`.**  
   From `riemannHypothesis` (`src/Main.lean:4`), an explicit 7-hop declaration chain reaches `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (`.../ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69`), which at hop 8 calls both `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound` (whose proof term directly applies `geoCl anyGeometry` at lines 60, 63, 67) and `GlobalTheory.Mem.Top.Bl.parametersOfDependence` (`.../ThirdPlaceSeries/Prm1.lean:20–21`, whose body directly applies `geoCl anyGeometry`). Deeper on the same active cone (hops 9–15), the proof constructs `DivEx` via `divEx_geoCl` → `divEx_of_ox` → `divEx_prov` (`.../TupPinsOfMuIsW.lean:204–213`), which requires `𝒮.Ox = OX anyGeometry` and discharges the `.geo` field of `OAt anyGeometry` using `trivial` (`line 209`).
2. **However, the critic's cited entry point (`everyE₂`, `hypsE₂`, `plugAll`, `Hyps`) is NOT on the cone of `riemannHypothesis`.**  
   The codebase contains two parallel copies of the top-level hypothesis-bundle machinery:
   - A **superseded legacy stack** (`Hyps`, `plugWin`, `plugAll`, `hypsE₂`, `everyE₂`, `prmR`/`prm0`/`prm1`/`prmA`) under `AbelianVarietyTheory/...`, `CharacterBoxes/EveryCharacter.lean`, and `FockModels/EveryCharacterE.lean`. `everyE₂` has **zero callers** anywhere in the repository; `hypsE₂` and `plugAll` are called **only** by `everyE₂`. `EveryCharacterE.lean` is imported only at the file level (`SiegelEisensteinSecondTermHypotheses.lean:1`, `EveryCharacterOfLiteratureOfVWin.lean:189`, `TemperedProductOfSquareIntegrable.lean:195`).
   - An **active `ThirdPlaceSeries` ("alt") twin stack** (`HypsAlt`, `zero_free_all_of_green_v_win`, `every_character_of_green_v_win`, `nonempty_hyps_definite_side_of_closed_bound`, `every_character_of_theta_integrals_local_matching`, `parametersOfExtension`/`parametersOfDependence`). This active stack is what `riemannHypothesis` actually calls — and it equally hardcodes `geoCl anyGeometry` throughout.
3. **No alternative route to `UpperTheory.EveryCharacter` (or unconditional `RiemannHypothesis`) avoids `anyGeometry`.**  
   Across the entire repository, both stacks that construct `UpperTheory.EveryCharacter` (active `ThirdPlaceSeries` and unused `EveryCharacterE`) pass `geoCl anyGeometry`. Furthermore, all three proofs of `DivEx` in the entire codebase (`divEx_prov`, `divEx_of_ox`, `divEx_geoCl`) hardcode `OX anyGeometry` or `OX (geoCl anyGeometry)`.
4. **All 24 files (118 lines) mentioning `anyGeometry` split into 10 purely on-cone files, 1 mixed file (`PublishedInputsImplyConclusion.lean`), and 13 purely off-cone files.**
5. **`GlobalTheory.Mem.Top.Bl.geoOf` (the non-trivial `GeoP` predicate) is 100% OFF-CONE.**  
   It is defined at `OverIx.lean:16–17` and referenced in only one other file (`NotLamAreShift.lean:27, 30, 159`), whose three lemmas (`geoOf_set`, `geoOf_surf`, `oAt_geoOf`) have zero external callers in the entire repository. (A repo-wide search for `\bgeoOf\b` also finds two unrelated homonymous definitions of completely different types, `GlobalTheory.TrueGeo.geoOf : ... → DV.Geo F` and `GlobalTheory.DRFlag.geoOf : ... → Geo ...`, disambiguated in Section 7.)

---

## 2. Explicit Declaration-Level Dependency Chain: `riemannHypothesis` → `anyGeometry`

Every link below was verified directly from Lean source files (checking imports, namespaces, `open` clauses, and absence of local shadowing).

### 2.1 Primary Chain to the First Direct Uses of `anyGeometry` (Hops 1–8)

#### Hop 1: `riemannHypothesis` → `rhOfAll`
- **File:** `src/Main.lean:1-4`
```lean
import Statements
import Supplements.Kernels.MainTheoremsAll

theorem riemannHypothesis : RiemannHypothesis := rhOfAll
```
*(Note: `src/Supplements/Kernels/MainTheoremsAll.lean:1` imports `Supplements.Kernels.MainTheoremsCritical`, whose line 1 imports `Supplements.Kernels.MainTheorems`. Inspection of `MainTheoremsAll.lean`, `MainTheoremsCritical.lean`, `Statements.lean`, `CorGKOf.lean`, `ClassNumberThree.lean`, `LenEqZeroIff.lean`, and `OnePoint.lean` confirmed none of them redefine `rhOfAll` or `RiemannHypothesis`.)*

#### Hop 2: `rhOfAll` → `Formalism.VW.rh_of_every` & `allChi`
- **File:** `src/Supplements/Kernels/MainTheorems.lean:7-9`
```lean
theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter

theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi
```
*(In `src/Formalism/GammaFactorNonvanishing/CritLine.lean:29-32`, `Formalism.VW.rh_of_every` uses its argument `h : UpperTheory.EveryCharacter` genuinely in its proof term via `have := h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)`.)*

#### Hop 3: `allChi` → `UpperTheory.FinalTheorems.everyCharacter`
- **File:** `src/Supplements/Kernels/MainTheorems.lean:7`
```lean
theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter
```

#### Hop 4: `UpperTheory.FinalTheorems.everyCharacter` → `UpperTheory.FinalTheorems.everyCharacter_of_row`
- **File:** `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:10-11`
```lean
theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=
  UpperTheory.FinalTheorems.everyCharacter_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
```

#### Hop 5: `UpperTheory.FinalTheorems.everyCharacter_of_row` → `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin`
- **File:** `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7-8`
```lean
theorem UpperTheory.FinalTheorems.everyCharacter_of_row (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) : UpperTheory.EveryCharacter :=
  UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩ (UpperTheory.One.vwin_of_row h)
```

#### Hop 6: `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` → `UpperTheory.Lit.every_character_of_theta_integrals_local_matching`
- **File:** `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810-813`
```lean
theorem UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) (hV : UpperTheory.Top.VWin) : UpperTheory.EveryCharacter :=
  _root_.UpperTheory.Lit.every_character_of_theta_integrals_local_matching (_root_.UpperTheory.LiteratureTheorems.published_results_eigen O) (_root_.UpperTheory.LiteratureTheorems.published_results_first O) (_root_.UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature O).1 (_root_.UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature O).2
    (_root_.SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt ...)
    (_root_.UpperTheory.LiteratureTheorems.local_langlands_gl_recT_exists_of_literature O) hV
```

#### Hop 7: `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` → `UpperTheory.Top.every_character_of_green_v_win`, `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound`, and `GlobalTheory.Mem.Top.Bl.parametersOfDependence`
- **File:** `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69-73`
```lean
theorem every_character_of_theta_integrals_local_matching (P : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses) (F : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hX : _root_.GlobalTheory.CovTop.CovolumeBoundOfX) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hV : VWin) :
    UpperTheory.EveryCharacter :=
  _root_.UpperTheory.Top.every_character_of_green_v_win (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) hV
    (_root_.UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound P F hA hM hX hL fun cDep => _root_.UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep))
```

#### Hop 8a (Direct `anyGeometry` in proof term — Branch 1): `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound` → `anyGeometry` (and `geoCl`)
- **File:** `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:44, 58-68`
```lean
theorem nonempty_hyps_definite_side_of_closed_bound : ... → Nonempty (_root_.GlobalTheory.Fc.HypsAlt S0.NL _root_.GlobalTheory.Fc.DefiniteSideCondition) := by
  ...
  have hOpen1 : _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL (max CF0 CF1)) := _root_.GlobalTheory.T.open0_of_unitary_group_hypotheses P hL (max CF0 CF1)
  have hMono := _root_.GlobalTheory.Glob.open_and_linked_of_stronger_extension_alt hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL (max CF0 CF1))
    (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL (max CF0 CF1)) (GridA (max CF0 CF1))) SExt.none (geoCl anyGeometry)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1⟩)
  have hOpenA := hMono.2 hOpen1
  have hFun := hCF0 (max CF0 CF1) (le_max_left _ _) hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL (max CF0 CF1)) SExt.none (geoCl anyGeometry)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1⟩) hOpenA
  have hL3 := _root_.GlobalTheory.Glob.CovolRow.linked_bundles_l3_of_open_alt P.discreteSeriesCover P.harishChandraModules P.cuspRapidDecay
    P.casselmanWallach P.rayClassFieldSt hX hL (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL (max CF0 CF1)) (GridA (max CF0 CF1)))
    SExt.none (geoCl anyGeometry) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1.1⟩) hOpenA
  exact _root_.GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt P hRat hL (max CF0 CF1) (GridA (max CF0 CF1)) hEv (hN (max CF0 CF1)) hFun hL3
```
- `GlobalTheory.Mem.Top.Bl` is opened at line 41; `anyGeometry` resolves to `GlobalTheory.Mem.Top.Bl.anyGeometry` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean:19`):
```lean
def anyGeometry : GeoP := fun _ _ _ => True
```
and `geoCl` resolves to `GlobalTheory.Mem.Top.Bl.geoCl` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotGeoClFalse.lean:21-26`):
```lean
inductive GeoCl (Γ : GeoP) : ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop
  | base {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} : Γ D J X → GeoCl Γ D J X
  | step {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
      {J : Formalism.L2.Pj.Core D} {X : DivX D} : GeoCl Γ D J X → GeoCl Γ (setDiv D N h) (coreS N h J) (divTr N h X)

def geoCl (Γ : GeoP) : GeoP := GeoCl Γ
```

#### Hop 8b (Direct `anyGeometry` in definition body — Branch 2): `GlobalTheory.Mem.Top.Bl.parametersOfDependence` → `anyGeometry`
- **File:** `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Prm1.lean:20-21`
```lean
@[reducible] def parametersOfDependence (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL :=
  _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
```
*(Referenced directly at `SiegelEisensteinSecondTermHypotheses.lean:44, 58, 73`.)*

---

### 2.2 Continuation Down the Active Cone to the Discharge Site `divEx_prov` (Hops 9–15)

Tracing further from Hop 8a (`nonempty_hyps_definite_side_of_closed_bound`, line 68) shows not merely that `anyGeometry` appears in parameter expressions, but where `anyGeometry`'s definition `fun _ _ _ => True` is actually *evaluated and discharged by `trivial`* inside the active proof cone:

- **Hop 9:** `nonempty_hyps_definite_side_of_closed_bound` (`SiegelEisensteinSecondTermHypotheses.lean:68`) → `GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt` (`.../ThirdPlaceSeries/HypothesesNonemptyOfUnramifiedExponents.lean:41-61`):
  - Mentions `(geoCl anyGeometry)` directly at lines 41, 49, 52.
  - Branches into three active sub-chains that also mention `anyGeometry`:
    - **Sub-branch 9A (line 46):** calls `_root_.GlobalTheory.T.open0_of_unitary_group_hypotheses` (`.../ThirdPlaceSeries/OpenOrbitOfUnramifiedExponents.lean:75-76`) → `GlobalTheory.Fc.S0.Open0ProofU.open_orbit_of_unramified_exponents_alt` (lines 39–69), which directly passes `(geoCl anyGeometry)` on 12 lines (44, 45, 47, 49, 53, 55, 59, 63, 64, 65, 66, 68).
    - **Sub-branch 9B (line 47):** calls `_root_.UpperTheory.GalC.final_alt_alt` (`.../ThirdPlaceSeries/CFinal.lean:19-22`) → `_root_.UpperTheory.GalC.final_of_alt` (`.../ThirdPlaceSeries/LinkNFam.lean:75-86`), which directly passes `anyGeometry` / `(geoCl anyGeometry)` on lines 80, 81, 83, 85.
    - **Sub-branch 9C (line 43):** calls `_root_.GlobalTheory.T.large_unramified_exponent_bundles_exist_alt` (`.../ThirdPlaceSeries/MemberBundlesLargeUnramifiedExponents.lean:69-70`), continuing below.
- **Hop 10:** `GlobalTheory.T.large_unramified_exponent_bundles_exist_alt` (`MemberBundlesLargeUnramifiedExponents.lean:69-70`) → `GlobalTheory.Fc.StageOneU.member_bundles_large_unramified_exponents_alt` (`MemberBundlesLargeUnramifiedExponents.lean:34-63`):
  - Directly mentions `(geoCl anyGeometry)` / `anyGeometry` at lines 37–40, 58, 63, 69.
  - At line 61: calls `_root_.GlobalTheory.T.member_exists_baseLattice_alt`.
- **Hop 11:** `GlobalTheory.T.member_exists_baseLattice_alt` (`.../ThirdPlaceSeries/ExistsBaseLatticeOfPrime.lean:80-81`) → `GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt` (lines 57–72) → `GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_pair_alt` (lines 36–56):
  - Directly mentions `(geoCl anyGeometry)` / `anyGeometry` on 20 lines (40–48, 51, 55–56, 58–60, 68–69, 71–72, 80).
  - At line 53: calls `_root_.GlobalTheory.Mem.Top.Closing.memberE_closing_alt_alt`.
- **Hop 12:** `GlobalTheory.Mem.Top.Closing.memberE_closing_alt_alt` (`.../ThirdPlaceSeries/MemberEClosing.lean:17-26`):
  - Directly mentions `(geoCl anyGeometry)` at lines 17, 19, 20, 23, 26.
  - At lines 21 and 24: calls `(divEx_geoCl p1 p2 p3 _ _ _)`.
- **Hop 13:** `GlobalTheory.Mem.Top.Closing.divEx_geoCl` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PublishedInputsImplyConclusion.lean:39-49`):
```lean
theorem divEx_geoCl (h1 : GlobalTheory.NT.RayField) (h2 : GlobalTheory.Published.PrincipalIdealSt) (h3 : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt)
    (R : RPosition) (N : NCondition) (S : SPosition) : DivEx ⟨R, N, S, OX (geoCl anyGeometry)⟩ := by
  have h := GlobalTheory.Mem.Top.DivRec.divEx_of_ox h1 h2 h3 ⟨R, N, S, OX anyGeometry⟩ rfl
  ...
  exact ⟨⟨geoCl_of o.geo, o.lam⟩⟩
```
- **Hop 14:** `GlobalTheory.Mem.Top.DivRec.divEx_of_ox` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:211-213`):
```lean
theorem divEx_of_ox : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → ∀ 𝒮 : Slots,
    𝒮.Ox = OX anyGeometry → DivEx 𝒮 :=
  fun _ _ _ 𝒮 hOx => divEx_prov 𝒮 hOx
```
- **Hop 15 (Terminal discharge of `anyGeometry`):** `GlobalTheory.Mem.Top.DivRec.divEx_prov` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:204-209`):
```lean
theorem divEx_prov (𝒮 : Slots) (hOx : 𝒮.Ox = OX anyGeometry) : DivEx 𝒮 :=
  StepW.of_all fun _ _ _ _ w _ _ hpin Z l =>
    let ⟨Y, h1, h2, h3, h4⟩ := exists_divT w hpin.some Z l
    ⟨Y, h1, h2, h3, fun O t hX hp ht => by
      rw [hOx]
      exact ⟨⟨trivial, lamAre_heq hp ht (hX ▸ h4)⟩⟩⟩
```
Here `OAt anyGeometry t O.X` (`OverIx.lean:44-47`) has field `geo : anyGeometry (w.st Z).toD7 t.r.z.core.toCore O.X`, which reduces definitionally to `True` and is inhabited by `trivial` at `TupPinsOfMuIsW.lean:209`, then wrapped into `GeoCl.base trivial` via `geoCl_of` at `PublishedInputsImplyConclusion.lean:49`.

*(Note also that `nonempty_hyps_definite_side_of_closed_bound` produces `Nonempty (HypsAlt S0.NL DefiniteSideCondition)` via `hypotheses_nonempty_of_unramified_exponents_alt` → `nonempty_hyps_of_allRows_alt` (`.../ThirdPlaceSeries/NonemptyHypsOfAllRows.lean:19-101`), which is genuinely eliminated by `UpperTheory.Top.every_character_of_green_v_win` → `UpperTheory.Top.zero_free_all_of_green_v_win` (`.../ThirdPlaceSeries/TopPlug.lean:12-18`) via `h.elim fun h => ... forall_goal_of_shape_of_hyps ... h`. Thus the `anyGeometry` branch is not an unused proof argument.)*

---

## 3. Is `UpperTheory.Lit.everyE₂` or `hypsE₂` Referenced on the Active Path?

**NO.** Neither `UpperTheory.Lit.everyE₂` nor `UpperTheory.Lit.hypsE₂` (nor `UpperTheory.Top.plugAll` / `plugWin`) is referenced on the path from `every_character_of_literature_of_vWin` or `every_character_of_theta_integrals_local_matching` — or anywhere else in the dependency cone of `riemannHypothesis`.

Verified via repo-wide `git grep` across all 175k files:
- **`everyE₂`** appears **exactly once** in the entire repository: its own definition at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/EveryCharacterE.lean:67`:
  ```lean
  theorem everyE₂ (P : S0.HypothesesUE) (F : GlobalTheory.FunPr.Hypotheses₂) (hA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
      (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hX : GlobalTheory.CovTop.CovolX) (hL : GlobalTheory.Published.LocalLanglandsGL) (hV : VWin) :
      UpperTheory.EveryCharacter :=
    plugAll (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) hV
      (hypsE₂ P F hA hM hX hL fun cDep => UpperTheory.N.boundAtTwoThree_at_prm_of_prints P.nLink (prm1 hL cDep))
  ```
  It has **zero callers**.
- **`hypsE₂`** appears **exactly twice** in the entire repository: its definition at `EveryCharacterE.lean:41` and its sole call inside `everyE₂` at `EveryCharacterE.lean:71`.
- **`plugAll`** appears **exactly twice** in the entire repository: its definition at `src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:16` and its sole call inside `everyE₂` at `EveryCharacterE.lean:70`.
- **`EveryCharacterE.lean`** is imported at the file level by `SiegelEisensteinSecondTermHypotheses.lean:1`, `EveryCharacterOfLiteratureOfVWin.lean:189`, and `TemperedProductOfSquareIntegrable.lean:195`, which explains why file-import inspection (or reading `EveryCharacterE.lean` in isolation) can easily mistake `everyE₂`/`hypsE₂`/`plugAll` for the active path. At declaration level, however, `EveryCharacterOfLiteratureOfVWin.lean:811` calls `_root_.UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (`SiegelEisensteinSecondTermHypotheses.lean:69`), which calls `_root_.UpperTheory.Top.every_character_of_green_v_win` (`.../ThirdPlaceSeries/TopPlug.lean:16`) and `_root_.UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound` (`SiegelEisensteinSecondTermHypotheses.lean:44`).

Structurally, `nonempty_hyps_definite_side_of_closed_bound` and `every_character_of_theta_integrals_local_matching` (`SiegelEisensteinSecondTermHypotheses.lean:44-73`) are near-verbatim "alt" rewrites of `hypsE₂` and `everyE₂` (`EveryCharacterE.lean:41-71`) adapted to `_root_.UpperTheory.Zero.LLC.RecTExists` (instead of `GlobalTheory.Published.LocalLanglandsGL`) and `GlobalTheory.Fc.HypsAlt` (instead of `GlobalTheory.Fc.Hyps`). Both copies pass `(geoCl anyGeometry)` in the exact same positions.

---

## 4. All Sites Producing `Nonempty (Hyps …)` and `Nonempty (HypsAlt …)`

A repo-wide search for `\bHyps\b` (319 files total, most defining unrelated local `Hyps` predicates/structures in `CompanionTheory`, `Formalism`, `GroundTheory`, `EtaleCohomology`, etc.) and `\bHypsAlt\b` (9 files total, 1 unrelated in `GroundTheory/.../KleimanAmpleness/MemSpanOfMemIdealMod.lean:5`) identified **all** sites producing the top-level hypothesis bundles `GlobalTheory.Fc.Hyps` (`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/APerTw.lean:23`) and `GlobalTheory.Fc.HypsAlt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean:22`).

### 4.1 Producers of `Nonempty (GlobalTheory.Fc.Hyps …)` (Consumed by `UpperTheory.Top.plugAll` / `plugWin` — ALL OFF-CONE)

| # | Declaration | File:Line | Role / How Produced | Cone Status |
|---|---|---|---|---|
| 1 | `GlobalTheory.Fc.nonempty_hyps_of_allRows` | `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NonemptyHypsOfAllRows.lean:14-96` | **Primitive constructor** of `Nonempty (Hyps N DR)`. Calls `UpperTheory.Top.classSel` (line 46) and constructs `⟨{ 𝒜 := 𝒜, σ := σ, ... }⟩` (lines 50–96). Parametric in `KP Q Q' Lk N DR`. | **OFF-CONE** (only called by #2) |
| 2 | `GlobalTheory.Fc.S0.StageU.nonempty_hyps_of_classicalTheoremsUE` | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonemptyHypsOfPublishedUE.lean:30-50` | Instantiates #1 to produce `Nonempty (Hyps S0.NL DRS)` (line 46). Hardcodes `prm1 hL cDep` and `prmR (NEa hL (NEo hL cDep) A) SExt.none (geoCl anyGeometry)` (lines 30, 38, 41). | **OFF-CONE** (only called by #3) |
| 3 | `UpperTheory.Lit.hypsE₂` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/EveryCharacterE.lean:41-65` | Calls #2 to produce `Nonempty (Hyps S0.NL DRS)` (line 65). Hardcodes `prm1` and `(geoCl anyGeometry)` (lines 55, 57, 60, 64). | **OFF-CONE** (only called by `everyE₂`, which has 0 callers) |

Consumers of `Nonempty (GlobalTheory.Fc.Hyps …)`:
- `UpperTheory.Top.plugWin` (`src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:8-11`) → only called by `plugAll` (`line 18`).
- `UpperTheory.Top.plugAll` (`src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:16-18`) → only called by `everyE₂` (`EveryCharacterE.lean:70`).

### 4.2 Producers of `Nonempty (GlobalTheory.Fc.HypsAlt …)` (Consumed by `UpperTheory.Top.every_character_of_green_v_win` — ALL ON-CONE)

| # | Declaration | File:Line | Role / How Produced | Cone Status |
|---|---|---|---|---|
| 1 | `GlobalTheory.Fc.nonempty_hyps_of_allRows_alt` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/NonemptyHypsOfAllRows.lean:19-101` | **Primitive constructor** of `Nonempty (HypsAlt N DR)`. Calls `UpperTheory.Top.classSel` (line 51) and constructs `⟨{ 𝒜 := 𝒜, σ := σ, ... }⟩` (lines 55–101). Parametric in `KP Q Q' Lk N DR`. | **ON-CONE** (called by #2 at line 57) |
| 2 | `GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/HypothesesNonemptyOfUnramifiedExponents.lean:41-61` | Instantiates #1 to produce `Nonempty (HypsAlt S0.NL DefiniteSideCondition)` (line 57). Hardcodes `parametersOfDependence hL cDep` and `parametersOfExtension (extensionWithAtProperty ...) SExt.none (geoCl anyGeometry)` (lines 41, 49, 52). | **ON-CONE** (called by #3 at line 68) |
| 3 | `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:44-68` | Calls #2 to produce `Nonempty (HypsAlt S0.NL DefiniteSideCondition)` (line 68). Hardcodes `parametersOfDependence` and `(geoCl anyGeometry)` (lines 44, 58, 60, 63, 67). | **ON-CONE** (called by `every_character_of_theta_integrals_local_matching` at line 73) |

Consumers of `Nonempty (GlobalTheory.Fc.HypsAlt …)`:
- `UpperTheory.Top.zero_free_all_of_green_v_win` (`.../ThirdPlaceSeries/TopPlug.lean:12-15`) → called by `every_character_of_green_v_win` (`line 18`).
- `UpperTheory.Top.every_character_of_green_v_win` (`.../ThirdPlaceSeries/TopPlug.lean:16-18`) → called by `every_character_of_theta_integrals_local_matching` (`SiegelEisensteinSecondTermHypotheses.lean:72`).

There are **no other sites** producing `Nonempty (GlobalTheory.Fc.Hyps …)` or `Nonempty (GlobalTheory.Fc.HypsAlt …)` anywhere in the repository.

---

## 5. Is There Any Alternative Route to `EveryCharacter` Avoiding `anyGeometry`?

**NO.** Exhaustive repo-wide `git grep` for `EveryCharacter`, `ZeroFreeAll`, `RiemannHypothesis`, `DivEx`, and `GeoP` established:

1. **Every declaration in the entire repository returning `UpperTheory.EveryCharacter`** (8 declarations total, in 2 parallel stacks):
   - **Active stack (`ThirdPlaceSeries`, ON-CONE):**
     1. `UpperTheory.Top.every_character_of_green_v_win` (`.../ThirdPlaceSeries/TopPlug.lean:16-18`) — conditional on `Nonempty (HypsAlt ...)`.
     2. `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (`.../ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69-73`) — discharges via `nonempty_hyps_definite_side_of_closed_bound` (**uses `geoCl anyGeometry`**).
     3. `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` (`.../ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810-813`) — calls #2.
     4. `UpperTheory.FinalTheorems.everyCharacter_of_row` (`.../CharacterBoxes/MainConclusion.lean:7-8`) — calls #3.
     5. `UpperTheory.FinalTheorems.everyCharacter` (`.../CharacterBoxes/MainConclusion.lean:10-11`) — calls #4.
     6. `allChi` (`src/Supplements/Kernels/MainTheorems.lean:7`) — `:= UpperTheory.FinalTheorems.everyCharacter`.
   - **Legacy stack (`FockModels`, OFF-CONE):**
     7. `UpperTheory.Top.plugAll` (`.../CharacterBoxes/EveryCharacter.lean:16-18`) — conditional on `Nonempty (Hyps ...)`.
     8. `UpperTheory.Lit.everyE₂` (`.../FockModels/EveryCharacterE.lean:67-71`) — discharges via `hypsE₂` (**also uses `geoCl anyGeometry`**).
2. **Every declaration returning `Formalism.HC.ZeroFreeAll`** (3 total): `zeroFreeAll_of_topG` (`ZeroFreeAllOfTopG.lean:26`, conditional), `plugWin` (`EveryCharacter.lean:8`, conditional on `Nonempty (Hyps ...)`), and `zero_free_all_of_green_v_win` (`ThirdPlaceSeries/TopPlug.lean:12`, conditional on `Nonempty (HypsAlt ...)`).
3. **Every unconditional theorem proving `RiemannHypothesis`** (excluding `src/Challenge.lean:19`, which is `:= by sorry`):
   - `riemannHypothesis` (`src/Main.lean:4`) → `rhOfAll` (`MainTheorems.lean:9`) → `allChi` → `UpperTheory.FinalTheorems.everyCharacter`.
   - `UpperTheory.FinalTheorems.riemannHypothesis` (`MainConclusion.lean:13-14`) → `UpperTheory.riemannHypothesis_of_everyCharacter UpperTheory.FinalTheorems.everyCharacter`.
   All other occurrences of `RiemannHypothesis` in `src/Formalism/...` are conditional reduction lemmas.
4. **Structural bottleneck in `DivEx` and `GeoP`:**
   - Across all 225 occurrences of `GeoP` in the repository, the **only** definitions producing a term of type `GeoP` are `geoOf` (`OverIx.lean:16`), `anyGeometry` (`OverIx.lean:19`), and `geoCl` (`NotGeoClFalse.lean:26`).
   - Across all 9 occurrences of `DivEx` in the repository, the **only** theorems proving `DivEx 𝒮` are:
     - `divEx_prov (𝒮 : Slots) (hOx : 𝒮.Ox = OX anyGeometry) : DivEx 𝒮` (`TupPinsOfMuIsW.lean:204`),
     - `divEx_of_ox : ... → ∀ 𝒮 : Slots, 𝒮.Ox = OX anyGeometry → DivEx 𝒮` (`TupPinsOfMuIsW.lean:211-212`),
     - `divEx_geoCl ... : DivEx ⟨R, N, S, OX (geoCl anyGeometry)⟩` (`PublishedInputsImplyConclusion.lean:39-40`).
   - No theorem anywhere in the codebase proves `DivEx` for `OX (geoOf Q)` or `OX (geoCl (geoOf Q))`, nor passes `geoOf` into `prmR`, `parametersOfExtension`, `MemberE`, `Hyps`, or `HypsAlt`.

---

## 6. Complete Audit of All 24 Files (118 Lines) Mentioning `anyGeometry`

Repo-wide `git grep -n '\banyGeometry\b'` returned **exactly 24 files and 118 matching lines**. Below, every single occurrence is classified at **declaration level** as **ON-CONE** or **OFF-CONE** of `Main.lean:riemannHypothesis`.

**Summary count:**
- **10 files:** all occurrences **ON-CONE** (58 lines).
- **1 file (`PublishedInputsImplyConclusion.lean`):** **MIXED** — 2 lines **ON-CONE** (`divEx_geoCl`), 5 lines **OFF-CONE** (`memberE_closing`).
- **13 files:** all occurrences **OFF-CONE** (53 lines).
- **Total:** 60 lines ON-CONE, 58 lines OFF-CONE (118 lines across 24 files).

### 6.1 Purely ON-CONE Files (10 files)

1. **`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean`** — Line `19` (1 line)
   - **Declaration:** `GlobalTheory.Mem.Top.Bl.anyGeometry`
   - **Snippet (`line 19`):** `def anyGeometry : GeoP := fun _ _ _ => True`
   - **Classification:** **ON-CONE** — directly referenced by all on-cone declarations below.

2. **`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean`** — Lines `204, 212` (2 lines)
   - **Declarations:** `GlobalTheory.Mem.Top.DivRec.divEx_prov` (line 204), `GlobalTheory.Mem.Top.DivRec.divEx_of_ox` (line 212)
   - **Snippets:**
     - `line 204`: `theorem divEx_prov (𝒮 : Slots) (hOx : 𝒮.Ox = OX anyGeometry) : DivEx 𝒮 :=`
     - `line 212`: `𝒮.Ox = OX anyGeometry → DivEx 𝒮 :=`
   - **Classification:** **ON-CONE** — `divEx_geoCl` (`PublishedInputsImplyConclusion.lean:41`) calls `divEx_of_ox`, which calls `divEx_prov` (`line 213`).

3. **`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean`** — Lines `60, 63, 67` (3 lines)
   - **Declaration:** `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound`
   - **Snippets:**
     - `line 60`: `(_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL (max CF0 CF1)) (GridA (max CF0 CF1))) SExt.none (geoCl anyGeometry)`
     - `line 63`: `have hFun := hCF0 (max CF0 CF1) (le_max_left _ _) hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL (max CF0 CF1)) SExt.none (geoCl anyGeometry)`
     - `line 67`: `SExt.none (geoCl anyGeometry) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1.1⟩) hOpenA`
   - **Classification:** **ON-CONE** — called by `every_character_of_theta_integrals_local_matching` (`line 73`) → Hop 6 → `riemannHypothesis`.

4. **`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Prm1.lean`** — Line `21` (1 line)
   - **Declaration:** `GlobalTheory.Mem.Top.Bl.parametersOfDependence`
   - **Snippet (`lines 20-21`):**
     ```lean
     @[reducible] def parametersOfDependence (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL :=
       _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)
     ```
   - **Classification:** **ON-CONE** — called at `SiegelEisensteinSecondTermHypotheses.lean:44, 58, 73`, `HypothesesNonemptyOfUnramifiedExponents.lean:41`, `OpenOrbitOfUnramifiedExponents.lean:39, 43, 75`, `LinkNFam.lean:78, 79`.

5. **`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/HypothesesNonemptyOfUnramifiedExponents.lean`** — Lines `41, 49, 52` (3 lines)
   - **Declaration:** `GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt`
   - **Snippets:**
     - `line 41`: `... _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (... (GridA ...)) SExt.none (geoCl anyGeometry)) ...`
     - `line 49`: `have hmono := _root_.GlobalTheory.Glob.open_and_linked_of_stronger_extension_alt hL ... SExt.none (geoCl anyGeometry)`
     - `line 52`: `have hN' : _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension ... SExt.none (geoCl anyGeometry)) ...`
   - **Classification:** **ON-CONE** — called by `nonempty_hyps_definite_side_of_closed_bound` (`SiegelEisensteinSecondTermHypotheses.lean:68`).

6. **`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/OpenOrbitOfUnramifiedExponents.lean`** — Lines `44, 45, 47, 49, 53, 55, 59, 63, 64, 65, 66, 68` (12 lines)
   - **Declaration:** `GlobalTheory.Fc.S0.Open0ProofU.open_orbit_of_unramified_exponents_alt`
   - **Representative snippets:**
     - `line 44`: `have hPA := _root_.GlobalTheory.T.linkedAt_hPA_prmR hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)`
     - `line 68`: `hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)`
   - **Classification:** **ON-CONE** — wrapped by `GlobalTheory.T.open0_of_unitary_group_hypotheses` (`line 76`), which is called at `SiegelEisensteinSecondTermHypotheses.lean:58` and `HypothesesNonemptyOfUnramifiedExponents.lean:46`.

7. **`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkNFam.lean`** — Lines `80, 81, 83, 85` (4 lines)
   - **Declaration:** `UpperTheory.GalC.final_of_alt`
   - **Snippets:**
     - `line 80`: `have hW : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry)).s :=`
     - `line 81`: `GlobalTheory.T.witnesses_pass_along_set_division _ (_root_.GlobalTheory.NLink.Final.slot_mv_extension_with_list_geo_cl hL cDep anyGeometry)`
     - `line 83`: `have hTr := (_root_.GlobalTheory.Mem.AtPtTransport.atMem_at_wit_alt hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry) hW`
     - `line 85`: `exact _root_.UpperTheory.GalC.linkedAt_linkN_of_boundAtTwoThree hP hG hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry))`
   - **Classification:** **ON-CONE** — called by `UpperTheory.GalC.final_alt_alt` (`CFinal.lean:21`), which is called by `hypotheses_nonempty_of_unramified_exponents_alt` (`HypothesesNonemptyOfUnramifiedExponents.lean:47`).

8. **`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MemberBundlesLargeUnramifiedExponents.lean`** — Lines `37, 38, 39, 40, 58, 63, 69` (7 lines)
   - **Declarations:** `GlobalTheory.Fc.StageOneU.member_bundles_large_unramified_exponents_alt` (lines 37–40, 58, 63) and wrapper `GlobalTheory.T.large_unramified_exponent_bundles_exist_alt` (line 69).
   - **Representative snippets:**
     - `line 58`: `P.greenCuspidal hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)`
     - `line 63`: `(_root_.GlobalTheory.T.slot_mv_extension_with_origin_geo_cl hL cDep anyGeometry)⟩`
   - **Classification:** **ON-CONE** — called by `hypotheses_nonempty_of_unramified_exponents_alt` (`HypothesesNonemptyOfUnramifiedExponents.lean:43`).

9. **`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExistsBaseLatticeOfPrime.lean`** — Lines `40, 41, 42, 43, 44, 45, 46, 47, 48, 51, 55, 56, 58, 59, 60, 68, 69, 71, 72, 80` (20 lines)
   - **Declarations:** `GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_pair_alt` (lines 40–48, 51, 55–56), `exists_baseLattice_of_prime_alt` (lines 58–60, 68–69, 71–72), and wrapper `GlobalTheory.T.member_exists_baseLattice_alt` (line 80).
   - **Representative snippets:**
     - `line 55-56`: `exact _root_.GlobalTheory.T.geometric_parameter_uniform_alt ... hL N (geoCl anyGeometry) (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)) rfl ...`
     - `line 71`: `... (_root_.GlobalTheory.T.slot_mv_extension_with_origin_geo_cl hL cDep anyGeometry)`
   - **Classification:** **ON-CONE** — `member_exists_baseLattice_alt` (line 81) → `exists_baseLattice_of_prime_alt` (line 70) → `exists_baseLattice_of_pair_alt`; called at `MemberBundlesLargeUnramifiedExponents.lean:61`.

10. **`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MemberEClosing.lean`** — Lines `17, 19, 20, 23, 26` (5 lines)
    - **Declaration:** `GlobalTheory.Mem.Top.Closing.memberE_closing_alt_alt`
    - **Representative snippet (`lines 19-21`):**
      ```lean
      exact GlobalTheory.T.exists_member_of_construction_steps_secondPass p1 p2 p3 pv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s h3
        (_root_.GlobalTheory.T.has4_of_has3_of_lv3Mv s1 s2 s3 s4 s5 s6 s8 s9 pv hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)) rfl mv)
        (GlobalTheory.AmbCrd.ambEx_of_rx _ rfl) (divEx_geoCl p1 p2 p3 _ _ _)
      ```
    - **Classification:** **ON-CONE** — called by `exists_baseLattice_of_pair_alt` (`ExistsBaseLatticeOfPrime.lean:53`).

### 6.2 MIXED File (1 file: both ON-CONE and OFF-CONE declarations)

11. **`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PublishedInputsImplyConclusion.lean`** — Lines `40, 41` (ON-CONE) and `74, 76, 77, 80, 83` (OFF-CONE) (7 lines total)
    - **Lines 40–41 (`GlobalTheory.Mem.Top.Closing.divEx_geoCl`) — ON-CONE:**
      ```lean
      theorem divEx_geoCl ... (R : RPosition) (N : NCondition) (S : SPosition) : DivEx ⟨R, N, S, OX (geoCl anyGeometry)⟩ := by
        have h := GlobalTheory.Mem.Top.DivRec.divEx_of_ox h1 h2 h3 ⟨R, N, S, OX anyGeometry⟩ rfl
      ```
      Called directly by `memberE_closing_alt_alt` (`MemberEClosing.lean:21, 24`).
    - **Lines 74, 76, 77, 80, 83 (`GlobalTheory.Mem.Top.Closing.memberE_closing`) — OFF-CONE:**
      `memberE_closing` (using `prmR` / `GlobalTheory.Published.LocalLanglandsGL`) is called **only** by `GlobalTheory.T.published_inputs_imply_conclusion` (`PublishedInputsImplyConclusionStatement.lean:34`) → `memberE_exBL_of_pair` → `memberE_exBL_prm1` → `member_built_linked_geometric` → `member_bundles_large_ue` → `linked_bundle_construction_exists` → `nonempty_hyps_of_classicalTheoremsUE` → `hypsE₂` → `everyE₂` (0 callers).

### 6.3 Purely OFF-CONE Files (13 files)

All occurrences below were verified via repo-wide `git grep` to have zero callers reaching `riemannHypothesis` (even though several of these files are transitively *imported* by `Main.lean` for other declarations in the same file, e.g., `GridA` in `GKeyFin.lean`).

12. **`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/GKeyFin.lean`** — Line `22` (1 line)
    - **Declaration:** `GlobalTheory.Mem.LiteralAutomorphy.prmA` (`lines 21-22`: `@[reducible] def prmA ... := prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) A) SExt.none (geoCl anyGeometry)`).
    - **Classification:** **OFF-CONE** — `prmA` has **0 callers** anywhere in the repo.

13. **`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MultW.lean`** — Line `45` (1 line)
    - **Declaration:** `GlobalTheory.Mem.Top.Bl.prm1` (`lines 44-45`: `@[reducible] def prm1 ... := prmR (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry)`).
    - **Classification:** **OFF-CONE** — all 8 external references (`NonemptyHypsOfPublishedUE.lean:30`, `OpenFirstParametersOfPrintsUEStatement.lean:9`, `OpenFirstParametersOfPublishedUE.lean:26, 30`, `LinkOfClosedAtFamily.lean:68`, `EveryCharacterE.lean:41, 55, 71`) belong solely to the unused `everyE₂` legacy stack.

14. **`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotLamAreShift.lean`** — Line `153` (1 line)
    - **Declaration:** `GlobalTheory.Mem.Top.Bl.OXModel.oAt_any` (`lines 152-155`: `∃ l, Nonempty (OAt anyGeometry t ((GlobalTheory.ShFam.Pad.SurfSt.of X).put (setLam X l)))`).
    - **Classification:** **OFF-CONE** — `oAt_any` has **0 callers** anywhere in the repo. (The only file importing `NotLamAreShift.lean` is `ParameterOfDiscreteSeriesRay.lean:36`, which was read in full and does not reference `oAt_any` or any `OXModel` lemma.)

15. **`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ParMem.lean`** — Line `137` (1 line)
    - **Declaration:** `GlobalTheory.Mem.Top.Bl.prm0` (`line 137`: `@[reducible] def prm0 ... := prmR (NEb hL) SExt.none (geoCl anyGeometry)`).
    - **Classification:** **OFF-CONE** — `prm0` has **0 callers** anywhere in the repo.

16. **`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LinkedBundleConstructionExists.lean`** — Lines `28, 29, 30, 31, 51, 56` (6 lines)
    - **Declaration:** `GlobalTheory.Fc.StageOneU.member_bundles_large_ue`.
    - **Representative snippets:** `line 51`: `P.greenCuspidal hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) SExt.none (geoCl anyGeometry)`; `line 56`: `(GlobalTheory.T.movable_geometric hL cDep anyGeometry)⟩`.
    - **Classification:** **OFF-CONE** — only called by `linked_bundle_construction_exists` (`#17`, line 13) → `nonempty_hyps_of_classicalTheoremsUE` (`#18`, line 32) → `hypsE₂` (`#24`, line 65) → `everyE₂` (`#24`, line 71; 0 callers).

17. **`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LinkedBundleConstructionExistsStatement.lean`** — Line `12` (1 line)
    - **Declaration:** `GlobalTheory.T.linked_bundle_construction_exists`.
    - **Snippet (`line 12`):** `theorem _root_.GlobalTheory.T.linked_bundle_construction_exists : ... MemberE (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)).s ∧ ...`
    - **Classification:** **OFF-CONE** — only called by `nonempty_hyps_of_classicalTheoremsUE` (`#18`, line 32) → `hypsE₂` → `everyE₂` (0 callers).

18. **`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonemptyHypsOfPublishedUE.lean`** — Lines `30, 38, 41` (3 lines)
    - **Declaration:** `GlobalTheory.Fc.S0.StageU.nonempty_hyps_of_classicalTheoremsUE`.
    - **Representative snippet (`line 38`):** `have hmono := GlobalTheory.Glob.open_and_linked_of_stronger_extension hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)`
    - **Classification:** **OFF-CONE** — only called by `hypsE₂` (`EveryCharacterE.lean:65`) → `everyE₂` (0 callers).

19. **`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpenFirstParametersOfPublishedUE.lean`** — Lines `31, 32, 34, 36, 40, 42, 46, 51, 53, 55, 56, 58` (12 lines)
    - **Declaration:** `GlobalTheory.Fc.S0.Open0ProofU.open_of_hypothesesUE`.
    - **Representative snippet (`line 31`):** `have hPA := GlobalTheory.T.entry_hPA_at_parameters hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry)`
    - **Classification:** **OFF-CONE** — only wrapped by `GlobalTheory.T.open_first_parameters_of_hypothesesUE` (`OpenFirstParametersOfPrintsUEStatement.lean:9-10`), which is only called by `nonempty_hyps_of_classicalTheoremsUE` (`#18`, line 35) and `hypsE₂` (`#24`, line 55) → `everyE₂` (0 callers).

20. **`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinkOfClosedAtFamily.lean`** — Lines `71, 72, 73` (3 lines)
    - **Declaration:** `GlobalTheory.NLink.Final.main` (`lines 68-74`).
    - **Snippet (`lines 71-73`):** `have hW : WitMv (prmR (NEl hL cDep) SExt.none (geoCl anyGeometry)).s := GlobalTheory.T.witnesses_pass_along_set_division _ (movable_pin hL cDep anyGeometry)`; `exact GlobalTheory.T.residual_at_of_nonempty_exceptional hP hX.ht prN dzw dzs hL (NEl hL cDep) SExt.none (geoCl anyGeometry) hW`.
    - **Classification:** **OFF-CONE** — `GlobalTheory.NLink.Final.main` has **only 1 caller** repo-wide (`NonemptyHypsOfPublishedUE.lean:36`) → `hypsE₂` → `everyE₂` (0 callers). (`LinkOfClosedAtFamily.lean` is imported by `MainTyzTer.lean:1`, `SlotMvPin.lean:1`, and `RiemannHypothesisOfEveryCharacter.lean:85`, all read in full: none call `Final.main` or `movable_pin`.)

21. **`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MemberBuiltLinkedGeometric.lean`** — Lines `44, 45, 46, 47, 48, 49, 50, 51, 52, 55, 59, 60, 63, 64, 65, 73, 74, 76, 77` (19 lines)
    - **Declarations:** `GlobalTheory.Mem.Top.Bl.memberE_exBL_of_pair` (lines 40–60) and `memberE_exBL_prm1` (lines 62–77).
    - **Representative snippets:** `line 59-60`: `exact GlobalTheory.T.geometric_parameter_uniform ... hL N (geoCl anyGeometry) (prmR N SExt.none (geoCl anyGeometry)) rfl ...`; `line 76`: `... (GlobalTheory.T.movable_geometric hL cDep anyGeometry)`.
    - **Classification:** **OFF-CONE** — `memberE_exBL_of_pair` is only called by `memberE_exBL_prm1` (line 75), which is only called by `member_built_linked_geometric` (`#22`, line 10) → `member_bundles_large_ue` (`#16`, line 54) → ... → `everyE₂` (0 callers).

22. **`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MemberBuiltLinkedGeometricStatement.lean`** — Line `9` (1 line)
    - **Declaration:** `GlobalTheory.T.member_built_linked_geometric`.
    - **Snippet (`line 9`):** `theorem _root_.GlobalTheory.T.member_built_linked_geometric : ... MultQ (prmR (NEo hL cDep) SExt.none (geoCl anyGeometry)) → MemberE (prmR (NEo hL cDep) SExt.none (geoCl anyGeometry)).s ∧ ...`
    - **Classification:** **OFF-CONE** — only called by `member_bundles_large_ue` (`#16`, line 54) → ... → `everyE₂` (0 callers).

23. **`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PublishedInputsImplyConclusionStatement.lean`** — Line `33` (1 line)
    - **Declaration:** `GlobalTheory.T.published_inputs_imply_conclusion`.
    - **Snippet (`line 33`):** `theorem _root_.GlobalTheory.T.published_inputs_imply_conclusion : ... MemberE (prmR N SExt.none (geoCl anyGeometry)).s := by`
    - **Classification:** **OFF-CONE** — only called by `memberE_exBL_of_pair` (`#21`, line 57) → ... → `everyE₂` (0 callers).

24. **`src/Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/EveryCharacterE.lean`** — Lines `57, 60, 64` (3 lines)
    - **Declaration:** `UpperTheory.Lit.hypsE₂`.
    - **Snippets:** `line 57`: `(NEa hL (GlobalTheory.HeightCounting.Up.NEo hL (max CF0 CF1)) (GridA (max CF0 CF1))) SExt.none (geoCl anyGeometry)`; `line 60`: `have hFun := hCF0 (max CF0 CF1) (le_max_left _ _) hL (GlobalTheory.HeightCounting.Up.NEo hL (max CF0 CF1)) SExt.none (geoCl anyGeometry)`; `line 64`: `SExt.none (geoCl anyGeometry) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1.1⟩) hOpenA`.
    - **Classification:** **OFF-CONE** — only called by `UpperTheory.Lit.everyE₂` (`line 71`), which has **0 callers** repo-wide.

---

## 7. Complete Audit of `geoOf` (Non-Trivial `GeoP` Predicate) and Homonymous `geoOf` Identifiers

Repo-wide `git grep -n '\bgeoOf\b'` returned **10 files and 16 lines**, spanning **three completely distinct Lean declarations** in three different namespaces. Only the first is the non-trivial `GeoP` predicate paired with `anyGeometry`.

### 7.1 `GlobalTheory.Mem.Top.Bl.geoOf : (∀ D : D7, GlobalTheory.ShFam.KitClass D) → GeoP` (THE Non-Trivial `GeoP` Predicate)

- **Definition (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean:16-17`):**
  ```lean
  def geoOf (Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D) : GeoP := fun D J X =>
    (∃ c : ℕ, 0 < c ∧ GlobalTheory.ShFam.IsGeoOf (Q D) J c X) ∧ GlobalTheory.ShFam.Pad.HasTrueSurf X
  ```
- **All uses across the entire repository (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotLamAreShift.lean:26-36, 157-161`):**
  1. `line 26-28` (`GlobalTheory.Mem.Top.Bl.OXModel.geoOf_set`):
     ```lean
     theorem geoOf_set {Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D} {D : D7} {J} {c : ℕ} (hc : 0 < c) {X : DivX D}
         (h : GlobalTheory.ShFam.IsGeoOf (Q D) J c X) (l) : geoOf Q D J (GlobalTheory.ShFam.Pad.surfSt.put (setLam X l)) :=
       ⟨⟨c, hc, isGeoOf_set h l _⟩, rfl⟩
     ```
  2. `line 30-31` (`GlobalTheory.Mem.Top.Bl.OXModel.geoOf_surf`):
     ```lean
     theorem geoOf_surf {Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D} {D : D7} {J} {X : DivX D} (h : geoOf Q D J X) :
         Nonempty X.Surf ∧ Nonempty X.SurfFp := by
     ```
  3. `line 157-161` (`GlobalTheory.Mem.Top.Bl.OXModel.oAt_geoOf`):
     ```lean
     theorem oAt_geoOf (Q) (t : RowsT K w Z Wt p0) (h : R3.Lam3 t.r.Z) {c : ℕ} (hc : 0 < c) (X : DivX (w.st Z).toD7)
         (hX : GlobalTheory.ShFam.IsGeoOf (Q _) t.r.z.core.toCore c X) :
         ∃ l, Nonempty (OAt (geoOf Q) t (GlobalTheory.ShFam.Pad.surfSt.put (setLam X l))) := by
       obtain ⟨cOf, h1, -⟩ := h
       exact ⟨_, ⟨geoOf_set hc hX _, lamAre_set t.r.Z cOf (fun σ _ => overIx_of_via (fun i c => (h1 i c).2) σ) X _⟩⟩
     ```
- **Cone status:** **100% OFF-CONE.**
  - Repo-wide `git grep` verified `oAt_geoOf` has **0 callers**, `geoOf_surf` has **0 callers**, and `geoOf_set` is called **only** inside `oAt_geoOf` (`NotLamAreShift.lean:161`).
  - Even the two component predicates inside `geoOf`'s body cannot be inlined on-cone:
    - `GlobalTheory.ShFam.IsGeoOf` (`LargeFor.lean:78`) appears in **only 6 lines repo-wide**: its definition (`LargeFor.lean:78`), `OverIx.lean:17`, and `NotLamAreShift.lean:21, 22, 27, 158` (`isGeoOf_set`, `geoOf_set`, `oAt_geoOf`, all with 0 external callers).
    - `GlobalTheory.ShFam.Pad.HasTrueSurf` (`SecondChernDegreeVanishesTrueSurfaces.lean:346`) appears in **only 7 lines repo-wide**: `OverIx.lean:17` and lines `346, 348, 350, 355, 358, 364` of `SecondChernDegreeVanishesTrueSurfaces.lean` itself.

### 7.2 Disambiguation: Two Unrelated Homonymous `geoOf` Definitions (Not `GeoP`)

For completeness (and to avoid grep-based conflation), the remaining 12 lines in `git grep -n '\bgeoOf\b'` belong to two unrelated declarations with different types:

1. **`GlobalTheory.TrueGeo.geoOf`** (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/RingKrullDimIntegers.lean:600`):
   ```lean
   def geoOf (C : CxSt F) (K : CutSt C) (R : ResSt C) : DV.Geo F where
   ```
   - Used in `GeometrySectionsEqRiemannRoch.lean:21` (`def geoTrue ... : DV.Geo F := geoOf (cxSt F) (cutSt _) (resSt _)`) and `FormsOver.lean:57, 94, 101, 105` (`FinalTheorems.alg`, `shimOf`, `FormsOver`, `famOf`).
   - This constructs a `DV.Geo F` geometric package (used inside `LargeFor.lean`'s `FamOver`/`IsGeoOf` and related Shimura-family definitions), **not** a `GeoP` predicate. *(Note: we did not trace the full declaration-level cones of all 16 files referencing `FormsOver`/`geoTrue`, so we do not assert whether `GlobalTheory.TrueGeo.geoOf` is on-cone elsewhere, e.g. in arithmetic geometry proofs; we verified only that it is not `GlobalTheory.Mem.Top.Bl.geoOf : ... → GeoP`.)*

2. **`GlobalTheory.DRFlag.geoOf`** (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AffineOpenChartCompStructureEqSpMap.lean:503`):
   ```lean
   theorem geoOf (Z : Mdl Y i₀) : Geo (Y Z.i) Z.π where
   ```
   - Used in `AtlasModelComparison.lean:50, 53`, `ExistsDeRhamFlag.lean:69`, `ExistsFlagClosure.lean:66`, and `ExistsLatticeCoordinatesStep.lean:207`.
   - This is a theorem packaging projectivity/normality/flatness/density of a scheme model `Mdl Y i₀`, **not** a `GeoP` predicate. *(Similarly, its cone reachability via other branches was outside the scope of `GeoP` tracing and was not traced.)*

---

## 8. Separation of VERIFIED Facts vs. INFERENCES, Confidence, and Methodological Caveats

### VERIFIED Directly from Source (Confidence: **Very High / ~99%**)
- Every link in the 15-hop declaration chain `Main.lean:riemannHypothesis` → `rhOfAll` → `allChi` → `everyCharacter` → `everyCharacter_of_row` → `every_character_of_literature_of_vWin` → `every_character_of_theta_integrals_local_matching` → `{nonempty_hyps_definite_side_of_closed_bound, parametersOfDependence}` → `hypotheses_nonempty_of_unramified_exponents_alt` → `large_unramified_exponent_bundles_exist_alt` → `member_exists_baseLattice_alt` → `exists_baseLattice_of_prime_alt` → `exists_baseLattice_of_pair_alt` → `memberE_closing_alt_alt` → `divEx_geoCl` → `divEx_of_ox` → `divEx_prov` → `anyGeometry` (and sub-branches through `open_orbit_of_unramified_exponents_alt` and `final_of_alt`) was verified by reading each file's exact Lean source, imports, namespaces, and `open` statements.
- Repo-wide `git grep` exhaustively enumerated all 24 files (118 lines) mentioning `anyGeometry`, all 10 files (16 lines) mentioning `geoOf`, all 8 declarations returning `UpperTheory.EveryCharacter`, all 6 producers of `Nonempty (GlobalTheory.Fc.Hyps …)` and `Nonempty (GlobalTheory.Fc.HypsAlt …)`, all 9 occurrences of `DivEx`, and all definitions of type `GeoP`.
- `UpperTheory.Lit.everyE₂`, `UpperTheory.Lit.hypsE₂`, `UpperTheory.Top.plugAll`, and `GlobalTheory.Mem.Top.Bl.geoOf` (together with `IsGeoOf` and `HasTrueSurf`) have zero references on the declaration-level cone of `Main.lean:riemannHypothesis`.

### INFERRED / Caveats (Confidence: **High**, bounded by lack of Lean kernel execution)
- **No Lean 4 kernel execution:** Because Lean is not installed, name resolution, universe/type unification, and `#print axioms` / transitive kernel constant-dependency extraction could not be run mechanically. There is a small residual risk (~1%) of an obscured elaboration artifact (e.g. a macro or instance not visible by plain identifier grep), though every link in Section 2 uses explicit, mostly `_root_.`-qualified theorem applications with matching parameter signatures.
- **No claim of invalidity from Task A alone:** Proving that `anyGeometry := fun _ _ _ => True` is on the declaration-level dependency cone of `riemannHypothesis` is **purely a dependency fact**, NOT by itself a proof that the formal proof of `RiemannHypothesis` is invalid or vacuous! In Lean's kernel, if `riemannHypothesis : RiemannHypothesis` typechecks against Mathlib's statement using only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and no `sorry`, then passing a trivially true predicate (`anyGeometry`) to an internal parameter (`Γ : GeoP`) cannot compromise soundness — it would instead indicate that the formal proof of `RiemannHypothesis` did not need any content from `Γ` (making `geoOf` unused scaffolding, or indicating that any actual defect, if one exists, would have to lie elsewhere, e.g., in axioms, statement mismatch, or `sorry`). Conversely, if the critic's claim is about whether the proof implements the intended mathematical argument via `geoOf` rather than `anyGeometry`, Task A confirms that `geoOf` is completely dead code and `anyGeometry` is genuinely on the active cone.

---

## VERDICT

At the **declaration level**, `GlobalTheory.Mem.Top.Bl.anyGeometry` (`fun _ _ _ => True`, `OverIx.lean:19`) **unequivocally lies in the active dependency cone of `Main.lean:riemannHypothesis`**, while the non-trivial predicate `GlobalTheory.Mem.Top.Bl.geoOf` (`OverIx.lean:16–17`) is **completely off-cone** (referenced only by three uncalled lemmas in `NotLamAreShift.lean`), and **no alternative route to `UpperTheory.EveryCharacter` in the repository avoids `anyGeometry`**. Crucially, however, the critic's cited entry point (`UpperTheory.Lit.everyE₂`, `hypsE₂`, `plugAll`, and `GlobalTheory.Fc.Hyps`) is **off-cone** (`everyE₂` has zero callers repo-wide, and 13 of the 24 `anyGeometry` files plus `memberE_closing` in `PublishedInputsImplyConclusion.lean` belong exclusively to that superseded legacy copy); instead, `riemannHypothesis` routes through the parallel `ThirdPlaceSeries` twin (`every_character_of_literature_of_vWin` → `every_character_of_theta_integrals_local_matching` → `every_character_of_green_v_win` + `nonempty_hyps_definite_side_of_closed_bound` + `parametersOfDependence`), which equally hardcodes `geoCl anyGeometry` across 10 purely on-cone files and `divEx_geoCl` in `PublishedInputsImplyConclusion.lean`, terminating in `divEx_prov` (`TupPinsOfMuIsW.lean:204–209`) where `OAt anyGeometry`'s `.geo` field is discharged by `trivial`. Finally, this dependency trace establishes only that `anyGeometry` is used and `geoOf` is unused on the cone of `riemannHypothesis`; it does not by itself establish mathematical invalidity of a typechecked, axiom-clean proof of Mathlib's `RiemannHypothesis`.
