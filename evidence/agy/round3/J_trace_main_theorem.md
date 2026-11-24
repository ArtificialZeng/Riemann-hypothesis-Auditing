# Independent Review (Task J): Searching the Release for a Counterpart to `hRH`

Subject: Levent Alpöge's Lean 4 development (`~/rh-audit/src/omega`, release of 20 Nov 2026) and the minimal example posted by Nielsen (`~/rh-audit/agents3/input/posted_verbatim.txt`, indented copy `~/rh-audit/agents3/input/NielsenMinimal.lean`, 24 Nov 2026), in which `theorem claimed_rh (hRH : RiemannHypothesis)` (`NielsenMinimal.lean:35`) takes `RiemannHypothesis` as a hypothesis.

Unless otherwise specified, all repository paths are relative to `~/rh-audit/src/omega/`, and Mathlib paths are relative to `~/rh-audit/challenge-rebuild/.lake/packages/mathlib/`.

---

## 1. Full Quotation of `src/Main.lean` and Declaration Chain from `theorem riemannHypothesis`

### 1.1 `src/Main.lean` in full

`src/Main.lean:1-12`:
```lean
import Statements
import Supplements.Kernels.MainTheoremsAll

theorem riemannHypothesis : RiemannHypothesis := rhOfAll

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi

theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
```

(The intermediate aggregator imports are `src/Supplements/Kernels/MainTheoremsAll.lean:1-2`, importing `Supplements.Kernels.MainTheoremsCritical` and `Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.CorGKOf`, and `src/Supplements/Kernels/MainTheoremsCritical.lean:1-4`, importing `Supplements.Kernels.MainTheorems` plus three `SmallClassNumbers` files. All four proof terms used in `Main.lean` — `rhOfAll`, `allChi`, `claimAll`, `critAll` — are declared in `src/Supplements/Kernels/MainTheorems.lean:7-16`.)

### 1.2 Declaration chain starting from `theorem riemannHypothesis`

Below, the chain is traced from Level 0 down to Level 12, covering every branch until statements stop mentioning zeros of `riemannZeta` or `DirichletCharacter.LFunction`.

#### Level 0 — `riemannHypothesis`
- **Location**: `src/Main.lean:4`
- **Full statement**:
  ```lean
  theorem riemannHypothesis : RiemannHypothesis
  ```
- **Head of proof term**: `rhOfAll` (applied to no arguments).

#### Level 1 — `rhOfAll`
- **Location**: `src/Supplements/Kernels/MainTheorems.lean:9`
- **Full statement**:
  ```lean
  theorem rhOfAll : RiemannHypothesis
  ```
- **Head of proof term**: applies `Formalism.VW.rh_of_every` to `allChi`.

#### Level 2a — `Formalism.VW.rh_of_every`
- **Location**: `src/Formalism/GammaFactorNonvanishing/CritLine.lean:29-32`
- **Full statement**:
  ```lean
  theorem Formalism.VW.rh_of_every (h : UpperTheory.EveryCharacter) : RiemannHypothesis
  ```
- **Head of proof term**: applies `Formalism.VW.rh_of_right` (`CritLine.lean:30`) to the lambda `fun s hs hs1 => ...`, which specializes `h` to `1`, `(1 : DirichletCharacter ℂ 1)`, `s`, `hs`, `(Or.inr hs1)` and rewrites with Mathlib's `DirichletCharacter.LFunction_modOne_eq` (`CritLine.lean:31-32`).

#### Level 3a — `Formalism.VW.rh_of_right`
- **Location**: `src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:5-62`
- **Full statement**:
  ```lean
  theorem Formalism.VW.rh_of_right (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis
  ```
- **Head of proof term**: tactic proof (`RhOfRight.lean:6-62`) that unfolds `RiemannHypothesis`, splits via `lt_trichotomy s.re (1 / 2)`, applies `hz s hgt hs1` for `s.re > 1/2`, and for `s.re < 1/2` applies Mathlib's functional equation `riemannZeta_one_sub` together with `hz (1 - s) ht h1`, `Complex.Gamma_ne_zero_of_re_pos`, and `Complex.cos_eq_zero_iff` to derive a contradiction with the trivial-zero exclusion `htriv`.
- **Compiler check**: `~/rh-audit/agents3/leanc.sh ~/rh-audit/src/omega/src/Formalism/GammaFactorNonvanishing/RhOfRight.lean` exited with code `0` and no errors or warnings (elaborates against Mathlib alone).

#### Level 2b — `allChi`
- **Location**: `src/Supplements/Kernels/MainTheorems.lean:7`
- **Full statement**:
  ```lean
  theorem allChi : UpperTheory.EveryCharacter
  ```
  where `UpperTheory.EveryCharacter` is defined at `src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:13-14`:
  ```lean
  def UpperTheory.EveryCharacter : Prop :=
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
  ```
- **Head of proof term**: `UpperTheory.FinalTheorems.everyCharacter` (applied to no arguments).

#### Level 3 — `UpperTheory.FinalTheorems.everyCharacter`
- **Location**: `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:10-11`
- **Full statement**:
  ```lean
  theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter
  ```
- **Head of proof term**: applies `UpperTheory.FinalTheorems.everyCharacter_of_row` to `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`.

#### Level 4a — `UpperTheory.FinalTheorems.everyCharacter_of_row`
- **Location**: `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7-8`
- **Full statement**:
  ```lean
  theorem UpperTheory.FinalTheorems.everyCharacter_of_row
      (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) :
      UpperTheory.EveryCharacter
  ```
- **Head of proof term**: applies `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` to:
  1. `⟨h, UpperTheory.Zero.LLC.recTExists, h⟩` (an `OpenLiteratureStatements` structure value), and
  2. `UpperTheory.One.vwin_of_row h`.

#### Level 4b (non-L-zero branch) — `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`
- **Location**: `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6` (inside `namespace UpperTheory.Gal.Int`)
- **Full statement**:
  ```lean
  theorem galoisLocalGlobalStrong_recParameter : UpperTheory.GalStar.Row0b recT
  ```
- **Head of proof term**: applies `galoisRepresentations_of_thetaLift` (`GaloisRepresentationsOfThetaLift.lean:6`) to `UpperTheory.TP.K.tLiftK` (`TLiftK.lean:4-5`).
- **Why this branch stops mentioning zeros of zeta / L-functions**: `UpperTheory.GalStar.Row0b` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:69-73`) asserts existence of `l`-adic Galois representations `r : G E Ω →* GL (Fin a) (Qbar l)` for polarized regular algebraic cuspidal automorphic representations `(π, χ)` satisfying `PropsB`; it does not mention zeros of `riemannZeta` or `DirichletCharacter.LFunction`.

#### Level 4c (non-L-zero branch) — `UpperTheory.Zero.LLC.recTExists`
- **Location**: `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20-21`
- **Full statement**:
  ```lean
  theorem UpperTheory.Zero.LLC.recTExists : UpperTheory.Zero.LLC.RecTExists
  ```
- **Head of proof term**: tactic proof (`RecTExists.lean:22-66`) applying `UpperTheory.Zero.LLC.artEx`, `cuspEx`, `GlobalTheory.LocLanglands.exists_isLExt`, `extDim`, `extTw`, `extDual`, `extInj`, `extDepth`, and `typeIff`.
- **Why this branch stops mentioning zeros of zeta / L-functions**: `UpperTheory.Zero.LLC.RecTExists` (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:78-80`) asserts existence of local Langlands maps `rc : IrrGL (w.adicCompletion E) → WD h` satisfying `LawsT`; it does not mention zeros of `riemannZeta` or `DirichletCharacter.LFunction`.

#### Level 4d (non-L-zero branch) — `UpperTheory.One.vwin_of_row`
- **Location**: `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4-5`
- **Full statement**:
  ```lean
  theorem UpperTheory.One.vwin_of_row
      (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) :
      UpperTheory.Top.VWin
  ```
- **Head of proof term**: applies `UpperTheory.One.Join.automorphic_window_of_inputs` (`TopMainZj.lean:71-74`) to `(UpperTheory.LiteratureTheorems.OpenImageCondition.mk h)`, `UpperTheory.BaseChangeIdentities.baseChangeN`, and `h`.
- **Why this branch stops mentioning zeros of zeta / L-functions**: `UpperTheory.Top.VWin` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:44-49`) is `∀ ψ : PChar, VWinAt ψ 401`, which asserts bounds `VVle` on sums of `Formalism.GaloisCohomology.shaLen` over number fields `E` satisfying `IsChiField ψ e q d E` (`ExistsPageN.lean:12-49`); it does not mention zeros of `riemannZeta` or `DirichletCharacter.LFunction`.

#### Level 5 — `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin`
- **Location**: `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810-813`
- **Full statement**:
  ```lean
  theorem UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin
      (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements)
      (hV : UpperTheory.Top.VWin) : UpperTheory.EveryCharacter
  ```
  where `OpenLiteratureStatements` (`EveryCharacterOfLiteratureOfVWin.lean:215-218`) is a `Prop` structure with three fields: `caraianiLocalGlobalDual : _root_.UpperTheory.One.M.Row`, `localLanglandsExists : _root_.UpperTheory.Zero.LLC.RecTExists`, and `galoisRepOfPolarizedPairLit : _root_.UpperTheory.One.M.Row`.
- **Head of proof term**: applies `_root_.UpperTheory.Lit.every_character_of_theta_integrals_local_matching` to seven arguments:
  1. `published_results_eigen O`,
  2. `published_results_first O`,
  3. `(theta_integrals_agree_and_local_matching_of_literature O).1`,
  4. `(theta_integrals_agree_and_local_matching_of_literature O).2`,
  5. `_root_.SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt ...` (applied to 15 literature bundles/theorems built from `O`),
  6. `local_langlands_gl_recT_exists_of_literature O`,
  7. `hV`.

#### Level 6 — `UpperTheory.Lit.every_character_of_theta_integrals_local_matching`
- **Location**: `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69-73` (inside `namespace UpperTheory.Lit`)
- **Full statement**:
  ```lean
  theorem every_character_of_theta_integrals_local_matching
      (P : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses)
      (F : _root_.GlobalTheory.FunPr.ThetaLocalInputs)
      (hA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
      (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
      (hX : _root_.GlobalTheory.CovTop.CovolumeBoundOfX)
      (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
      (hV : VWin) :
      UpperTheory.EveryCharacter
  ```
- **Head of proof term**: applies `_root_.UpperTheory.Top.every_character_of_green_v_win` to:
  1. `GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters`,
  2. `hV`,
  3. `_root_.UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound P F hA hM hX hL (fun cDep => _root_.UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep))`.

#### Level 7 — `UpperTheory.Top.every_character_of_green_v_win`
- **Location**: `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:16-18`
- **Full statement**:
  ```lean
  theorem UpperTheory.Top.every_character_of_green_v_win
      (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
      (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) :
      UpperTheory.EveryCharacter
  ```
- **Head of proof term**: applies `UpperTheory.Top.imprimitive` to `_root_.UpperTheory.Top.zero_free_all_of_green_v_win hG hV h`.

#### Level 8a — `UpperTheory.Top.imprimitive`
- **Location**: `src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:5-35`
- **Full statement**:
  ```lean
  theorem UpperTheory.Top.imprimitive :
      ZeroFreeAll → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
        1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
  ```
  where `Formalism.HC.ZeroFreeAll` (`ExplicitFormulaErrorOfHostConditions.lean:11-18`) is `ZeroFreeOn fun _ => True`, i.e., `∀ ψ : PChar, True → ∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0`.
- **Head of proof term**: tactic proof (`Imprimitive.lean:8-35`) applying `h (PChar.of χ) trivial s hs` to obtain `DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0`, rewriting via Mathlib's `DirichletCharacter.LFunction_changeLevel`, and showing each Euler factor `(1 : ℂ) - χ.primitiveCharacter p * (p : ℂ) ^ (-s)` is nonzero for `1 / 2 < s.re`.

#### Level 8b — `UpperTheory.Top.zero_free_all_of_green_v_win`
- **Location**: `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12-15`
- **Full statement**:
  ```lean
  theorem UpperTheory.Top.zero_free_all_of_green_v_win
      (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
      (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) :
      Formalism.HC.ZeroFreeAll
  ```
- **Head of proof term**: `h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)` applied to:
  1. `_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (_root_.UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h` (which produces `UpperTheory.Top.TopG`; `ShapeOf.lean:31-32`, `TopShape.lean:33-55`, `DesWin.lean:11-31` — none of these mention zeros of zeta / L-functions; `TopG` asserts `FamilyClassConnected (G.cls la)` at `ZeroFreeAllOfTopG.lean:12-14`), and
  2. `fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)` (which produces `∀ ψ : PChar, HostExW (3 / 2) (GChi ψ).req`; `SupplyChi.lean:8-16` -> `HostOfField.lean:17-23` -> `supplyOfAdmOf.lean:13` + `QH.pairEx` at `pairEx.lean:112-170`, which uses only a zero-free box `1 - 1 / 400 < s.re, |s.im| ≤ Q` from `PairGood.lean:12-26`, proved unconditionally via `QH.pair_exists` / `QH.pair_share` / `QH.stage1` / `QH.stage2`).

#### Level 9 — `UpperTheory.Top.zeroFreeAll_of_topG`
- **Location**: `src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:26-34` (inside `namespace UpperTheory.Top`)
- **Full statement**:
  ```lean
  theorem zeroFreeAll_of_topG {la : ℝ} (hla : 1 < la) (h : TopG)
      (hS : ∀ ψ : PChar, HostExW la (GChi ψ).req) : ZeroFreeAll
  ```
- **Head of proof term**: applies `Formalism.HC.zeroFreeOn_of_tiedWin_cyc (Fam := FamP) (core := fun Fm => Fm.toFamCore) (Tied := fun Fm => ChainTied Fm) hla` (`ZeroFreeAllOfTopG.lean:28`) to:
  1. `fun ψ _ => UpperTheory.Comparison₂.level_gm_le_on_family_scales _` (`LevelGmLeOnFamilyScales.lean:28-30` -> `WindowInequalityOfArtinInputs.lean:17-25` -> `CoreGm.lean:12-74`, proving the Chebyshev inequality `Λ.Gm x ≤ x ^ (1/2 + (eD + eL + 7) * eps)` on windows without mentioning zeros of zeta / L-functions),
  2. `fun ψ _ => UpperTheory.Comparison₂.formB _`, and
  3. `fun ψ _ => ...` (combining `h la (GChi ψ) hla (hS ψ) (hypV_of_cls ψ la)` with `eFamC_of_cls`).

#### Level 10 — `Formalism.HC.zeroFreeOn_of_tiedWin_cyc`, `level_of_tiedWin`, and `UpperTheory.Comparison₂.formB`
- **`Formalism.HC.zeroFreeOn_of_tiedWin_cyc`** (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean:90-93`, with enclosing section `variable {Fam : ℝ → Type 1} {core : ∀ {eps : ℝ}, Fam eps → FamCore eps} {Tied : ∀ {eps : ℝ}, Fam eps → (eD eL K cHH eK CL x : ℝ) → Prop}` at `TopWin.lean:20-21, 48`):
  ```lean
  theorem zeroFreeOn_of_tiedWin_cyc {Q : PChar → Prop} {la : ℝ} (hla : 1 < la)
      (h112 : ∀ ψ, Q ψ → ChebyshevInequalityOnWindows @core @Tied (Level.cyc ψ))
      (hB : ∀ ψ, Q ψ → (Level.cyc ψ).FormB)
      (h : ∀ ψ, Q ψ → ChebyshevInequalityAtWindowScale @core @Tied la (Level.cyc ψ)) : ZeroFreeOn Q
  ```
  - **Head of proof term**: applies `zeroFreeOn_of_tiedWin` (`TopWin.lean:83-88`), which applies `zeroFreeOn_of_levels` (`ExplicitFormulaErrorOfHostConditions.lean:45-48`) to `level_of_tiedWin` (`TopWin.lean:68-81`). `level_of_tiedWin` takes `h112`, `hB : Λ.FormBAt la`, and `h : ChebyshevInequalityAtWindowScale ...`, picks a small `ε` so `1/2 + (eD + eL + 7) * ε < s.re`, and applies `hB` to conclude `Λ.ZeroFreeLevel`.
- **`UpperTheory.Comparison₂.formB`** (`src/Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean:8-19`):
  ```lean
  theorem UpperTheory.Comparison₂.formB : ∀ Λ : Level, Λ.FormB
  ```
  where `Level.FormB` (`Window.lean:30-33`) is `∀ la : ℝ, 1 < la → ∀ θ : ℝ, 0 < θ → θ < 1 → HasWindows {x | Λ.Gm x ≤ x ^ θ} la → Λ.ZeroFreeAbove θ`.
  - **Head of proof term**: obtains `⟨F, hG, hZ⟩ := UpperTheory.Comparison₂.level_family Λ` (`LevelFamily.lean:41-52`), rewrites `← hZ`, and applies `Deduction.zeroFree_of_rpow_window F (δ := la - 1) (C := 1) hθ0 hθ1 (by linarith)`.

#### Level 11 — `Deduction.zeroFree_of_rpow_window`
- **Location**: `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean:11-14` (inside `namespace Deduction`)
- **Full statement**:
  ```lean
  theorem zeroFree_of_rpow_window (F : CharFamily) {θ δ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
      (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ θ) :
      ZeroFree F θ
  ```
  where `Deduction.ZeroFree F θ` (`CharFamily.lean:38-39`) is `∀ i, ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction (F.χ i) s ≠ 0`.
- **Head of proof term**: applies `lemmaL F hθ hθ1 hδ` to `windowHyp_of_rpow F hδ h`.

#### Level 12 — `Deduction.lemmaL` (and its Landau/pole-data ingredients)
- **Location**: `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/lemmaL.lean:13-22` (inside `namespace Deduction`)
- **Full statement**:
  ```lean
  theorem lemmaL (F : CharFamily) {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (h : WindowHyp F θ δ) :
      ZeroFree F θ
  ```
- **Head of proof term**: obtains `⟨Φ, hP⟩ := poleData F` (`poleData.lean:248`, constructing the meromorphic Laplace transform of `gm F` whose poles in `{Re s > 0}` are `zeroSet F`), applies `landau_window hP hθ hθ1 hδ (windowHypU_of_windowHyp F hδ h)` (`landauWindow.lean:83-84`, a general complex-analytic theorem proving `∀ ρ ∈ Z, ρ.re ≤ θ` from `PoleData g Φ Z` and `WindowHypU g θ δ`, mentioning no zeta or L-functions), and rules out `1 ≤ s.re` via `charFamily_LFunction_ne_zero_of_one_le_re` (`CharFamilyLFunctionNeZeroOfOneLeRe.lean:9-20`, applying Mathlib's `riemannZeta_ne_zero_of_one_le_re` and `DirichletCharacter.LFunction_ne_zero_of_one_le_re`).

---

## 2. Every Occurrence of `RiemannHypothesis` in the Release Source

Command executed inside `~/rh-audit/src/omega`:
```sh
git grep -n -w -F RiemannHypothesis
```
Total hits: **51 lines** across 29 files (48 lines in `.lean` files and 3 lines in `.md` documentation files).

### 2.1 Classification counts

| Class | Description | Count (all files) | Count (`.lean` only) |
|---|---|---:|---:|
| **(a)** | Conclusion of a statement (`theorem`/`example` type [10], or consequent/conjunct of a `def ... : Prop` statement definition [37]) | 47 | 47 |
| **(b)** | Hypothesis / binder type of a statement | **0** | **0** |
| **(c)** | Inside a proof | 1 | 1 |
| **(d)** | Comment or docstring (in Lean files) | 0 | 0 |
| **(e)** | Other (Markdown documentation files) | 3 | 0 |
| **Total** | | **51** | **48** |

**Occurrences in class (b)**: **None (0 occurrences).**

*(Note: I also checked every occurrence of `GrowthBoundAndRiemannHypothesis` — defined at `FixedEpsilonConcreteGrowthBound.lean:105-108` as a conjunction ending in `RiemannHypothesis` — via `git grep -n -w -F GrowthBoundAndRiemannHypothesis`: all 10 hits are its own definition or the consequent of an implication; it never appears as a hypothesis.)*

### 2.2 Complete list of all 51 occurrences

1. `README.md:13` — **(e)** Markdown prose: ``On 21 November 2026 the Lean and Mathlib communities certified Alpöge’s proof of Mathlib’s `RiemannHypothesis`...``
2. `README.md:141` — **(e)** Markdown prose: `` `riemannHypothesis : RiemannHypothesis` uses Mathlib's own definition. The other four theorems ``
3. `ci/Audit.lean:3` — **(a)** `example : RiemannHypothesis := riemannHypothesis`
4. `src/Challenge.lean:19` — **(a)** `theorem riemannHypothesis : RiemannHypothesis := by sorry` (external comparator challenge stub, not imported by `Main.lean`)
5. `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:102` — **(a)** `theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl` (RHS of `↔` conclusion)
6. `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:13` — **(a)** `theorem UpperTheory.FinalTheorems.riemannHypothesis : RiemannHypothesis :=`
7. `src/Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean:215` — **(a)** `theorem UpperTheory.riemannHypothesis_of_everyCharacter (h : UpperTheory.EveryCharacter) : RiemannHypothesis := by`
8. `src/Formalism/GammaFactorNonvanishing/CritLine.lean:29` — **(a)** `theorem Formalism.VW.rh_of_every (h : UpperTheory.EveryCharacter) : RiemannHypothesis :=`
9. `src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:5` — **(a)** `theorem Formalism.VW.rh_of_right (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by`
10. `src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:6` — **(c)** `  unfold RiemannHypothesis`
11. `src/Formalism/HalfLinks/Statement.lean:149` — **(a)** consequent of `def RiemannHypothesisOfHalfLinks : Prop` (`Statement.lean:144-149`)
12. `src/Formalism/JacobiWeightFamilies/Statement.lean:71` — **(a)** consequent of `def WeightedSieveImpliesRH : Prop` (`Statement.lean:57-71`)
13. `src/Formalism/LocalToGlobal/GlobalTheory/ConcTop.lean:104` — **(a)** consequent of `def ConcreteMainReduction : Prop` (`ConcTop.lean:98-104`)
14. `src/Formalism/SharpRestriction/GlobalSchurBounds/RamificationTwoAndConjugationAtQAndD.lean:1004` — **(a)** conclusion of `theorem rh_of ... : RiemannHypothesis := by` (`RamificationTwoAndConjugationAtQAndD.lean:1003-1004`)
15. `src/Formalism/SharpRestriction/GlobalSchurBounds/ZetaZeroFreeRegion.lean:267` — **(a)** consequent of `def SlopeLemmaFamily (Fm : DFamP) : Prop := (∃ ε0 : ℝ, 0 < ε0 ∧ AdmFe Fm ε0 ∧ SizesFe Fm ε0) → RiemannHypothesis`
16. `src/Formalism/SizeWindowBrackets/Chain2aCoreNoAnalytic.lean:396` — **(a)** consequent of `def Chain2a : Prop` (`392-396`)
17. `src/Formalism/SizeWindowBrackets/Chain2aCoreNoAnalytic.lean:402` — **(a)** consequent of `def Chain2 : Prop` (`398-402`)
18. `src/Formalism/SizeWindowBrackets/Chain2aCoreNoAnalytic.lean:508` — **(a)** consequent of `def Chain2c : Prop` (`504-508`)
19. `src/Formalism/SizeWindowBrackets/Chain2aCoreNoAnalytic.lean:578` — **(a)** consequent of `def Chain2d : Prop` (`574-578`)
20. `src/Formalism/SizeWindowBrackets/FixedEpsilonConcreteGrowthBound.lean:108` — **(a)** final conjunct of `def GrowthBoundAndRiemannHypothesis : Prop` (`105-108`)
21. `src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean:134` — **(a)** consequent of `def RiemannHypothesisOfBalanceAndGrowthData : Prop` (`131-134`)
22. `src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean:141` — **(a)** consequent of `def GrowthBoundGivesRiemannHypothesis : Prop` (`139-141`)
23. `src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean:181` — **(a)** consequent of `def RiemannHypothesisOfReducedGrowthData : Prop` (`179-181`)
24. `src/Formalism/SizeWindowBrackets/Losses5OfLossHypD.lean:112` — **(a)** consequent of `def Chain6_7 : Prop` (`108-112`)
25. `src/Formalism/SizeWindowBrackets/Losses5OfLossHypD.lean:123` — **(a)** consequent of `def Chain6_7Closed : Prop` (`119-123`)
26. `src/Formalism/SizeWindowBrackets/Losses5OfLossHypD.lean:196` — **(a)** consequent of `def Chain6_7' : Prop` (`192-196`)
27. `src/Formalism/SizeWindowBrackets/Losses5OfLossHypD.lean:207` — **(a)** consequent of `def Chain6_7'Closed : Prop` (`203-207`)
28. `src/Formalism/SizeWindowBrackets/PowerBoundGivesRiemannHypothesis.lean:15` — **(a)** consequent of `def PowerBoundGivesRiemannHypothesis : Prop` (`12-15`)
29. `src/Formalism/SizeWindowBrackets/SChain.lean:95` — **(a)** consequent of `def ChainGivesRiemannHypothesis : Prop` (`92-95`)
30. `src/Formalism/SizeWindowBrackets/SChain.lean:101` — **(a)** consequent of `def ChainEventualGivesRiemannHypothesis : Prop` (`97-101`)
31. `src/Formalism/SizeWindowBrackets/SChain.lean:250` — **(a)** consequent of `def ChainWeakLogDerivGivesRiemannHyp : Prop` (`246-250`)
32. `src/Formalism/SizeWindowBrackets/SlopesFromSizeAndCount.lean:143` — **(a)** consequent of `def Chain6a : Prop` (`139-143`)
33. `src/Formalism/SizeWindowBrackets/SlopesFromSizeAndCount.lean:290` — **(a)** consequent of `def Chain6b : Prop` (`286-290`)
34. `src/Formalism/SizeWindowBrackets/SlopesFromSizeAndCount.lean:525` — **(a)** consequent of `def Chain6c : Prop` (`521-525`)
35. `src/Formalism/SizeWindowBrackets/SlopesFromSizeAndCount.lean:663` — **(a)** consequent of `def Chain6 : Prop` (`659-663`)
36. `src/Formalism/SizeWindowBrackets/SlopesFromSizeAndCount.lean:674` — **(a)** consequent of `def Chain6Closed : Prop` (`670-674`)
37. `src/Formalism/SizeWindowBrackets/SlopesFromSizeAndCount.lean:781` — **(a)** consequent of `def Chain6' : Prop` (`777-781`)
38. `src/Formalism/SizeWindowBrackets/SmoothedRemainderRealIntegralFormula.lean:383` — **(a)** consequent of `def Chain3 : Prop` (`379-383`)
39. `src/Formalism/SizeWindowBrackets/SmoothedRemainderRealIntegralFormula.lean:406` — **(a)** consequent of `def Chain4 : Prop` (`401-406`)
40. `src/Formalism/SizeWindowBrackets/SmoothedRemainderRealIntegralFormula.lean:431` — **(a)** consequent of `def Chain3c : Prop` (`427-431`)
41. `src/Formalism/SizeWindowBrackets/SmoothedRemainderRealIntegralFormula.lean:449` — **(a)** consequent of `def Chain5 : Prop` (`445-449`)
42. `src/Formalism/SizeWindowBrackets/SmoothedRemainderRealIntegralFormula.lean:470` — **(a)** consequent of `def Chain5c : Prop` (`466-470`)
43. `src/Formalism/Statement.lean:48` — **(a)** left conjunct of consequent of `def RHofG : Prop` (`46-48`)
44. `src/Formalism/StatementOC.lean:71` — **(a)** consequent of `def RiemannHypothesisOfLowerBounds : Prop` (`65-71`)
45. `src/Formalism/ThickAverageLoss/Statement.lean:139` — **(a)** consequent of `def EstimateImpliesRHDirichlet : Prop` (`129-139`)
46. `src/Formalism/ThickAverageLoss/Statement.lean:172` — **(a)** consequent of `def EstimateImpliesRHWeighted : Prop` (`158-172`)
47. `src/Formalism/WideWeightTheorem/Statement.lean:83` — **(a)** consequent of `def WeightedSieveImpliesRHThreeParameter : Prop` (`66-83`)
48. `src/Formalism/ZetaRealNonvanish.lean:74` — **(a)** `def RHofHalfPlane : Prop := (∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0) → RiemannHypothesis`
49. `src/Main.lean:4` — **(a)** `theorem riemannHypothesis : RiemannHypothesis := rhOfAll`
50. `src/Supplements/Kernels/MainTheorems.lean:9` — **(a)** `theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi`
51. `verification/NOTES.md:62` — **(e)** Markdown prose: ``- Mathlib's `RiemannHypothesis` excludes the trivial zeros −2(n+1) and the point s = 1, where``

### 2.3 Mathlib's `RiemannHypothesis` vs. release declarations

The release does **not** define its own `RiemannHypothesis`. Checking both `~/rh-audit/index/decls.txt` via:
```sh
grep -E ":(def|abbrev|structure|inductive|opaque|axiom) ([^ ]*\.)?(RiemannHypothesis|riemannZeta|LFunction)([ :({]|$)" ~/rh-audit/index/decls.txt
```
and `git grep -n -F "def RiemannHypothesis" -- src/` returned **zero** definitions of `RiemannHypothesis` anywhere in `src/` (only longer names such as `RiemannHypothesisOfHalfLinks`, `RiemannHypothesisOfLowerBounds`, etc.).

Mathlib's definition is at `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185-186`:
```lean
@[wikidata Q205966]
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```
Confirmed by `leanc.sh` on `~/rh-audit/agents3/work/J/CheckStatements.lean` (`#print RiemannHypothesis` output: `def RiemannHypothesis : Prop := ∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n, s = -2 * (↑n + 1)) → s ≠ 1 → s.re = 1 / 2`).

---

## 3. The Other Four Statement Names Used in `src/Main.lean`

### 3.1 Definitions (`src/Statements.lean:1-16`)

All four statement names in `src/Main.lean:6, 8, 10, 12` are defined in `src/Statements.lean:1-16`, which imports only `Mathlib`:
```lean
import Mathlib

def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```
Verbatim copies of these four definitions also appear in `src/Challenge.lean:3-16` (not imported by `Main.lean`).

### 3.2 Every occurrence across the repository

Command executed inside `~/rh-audit/src/omega`:
```sh
git grep -n -w -F "RiemannZetaZerosOnLine"
git grep -n -w -F "DirichletLNonvanishingRightOfHalf"
git grep -n -w -F "DirichletLZerosOnLine"
git grep -n -w -F "PrimitiveDirichletLZerosOnLine"
```

Each of the four identifiers occurs **exactly 4 times** in the entire repository (16 lines total), with **0 occurrences in class (b)**:

| Identifier | Total | (a) conclusion | (b) hyp/binder | (c) proof | (d) comment | (e) other (`def`) | Exact locations |
|---|---:|---:|---:|---:|---:|---:|---|
| `RiemannZetaZerosOnLine` | 4 | 2 | **0** | 0 | 0 | 2 | `src/Statements.lean:3` (e), `src/Challenge.lean:3` (e), `src/Main.lean:6` (a), `src/Challenge.lean:21` (a) |
| `DirichletLNonvanishingRightOfHalf` | 4 | 2 | **0** | 0 | 0 | 2 | `src/Statements.lean:6` (e), `src/Challenge.lean:6` (e), `src/Main.lean:8` (a), `src/Challenge.lean:23` (a) |
| `DirichletLZerosOnLine` | 4 | 2 | **0** | 0 | 0 | 2 | `src/Statements.lean:10` (e), `src/Challenge.lean:10` (e), `src/Main.lean:10` (a), `src/Challenge.lean:25` (a) |
| `PrimitiveDirichletLZerosOnLine` | 4 | 2 | **0** | 0 | 0 | 2 | `src/Statements.lean:14` (e), `src/Challenge.lean:14` (e), `src/Main.lean:12` (a), `src/Challenge.lean:27` (a) |

### 3.3 Mathlib's `riemannZeta` and `DirichletCharacter.LFunction` (no release shadowing)

Because `src/Statements.lean:1` imports **only** `Mathlib`, all four statements necessarily refer to **Mathlib's** `riemannZeta` and `DirichletCharacter.LFunction`, not release-defined objects:
- Mathlib `riemannZeta` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:121`):
  ```lean
  def riemannZeta := hurwitzZetaEven 0
  ```
- Mathlib `DirichletCharacter.LFunction` (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:61`):
  ```lean
  noncomputable def LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := ZMod.LFunction χ s
  ```
- Checking `~/rh-audit/index/decls.txt` and `git grep -n -F "def riemannZeta" -- src/` / `git grep -n -F "def LFunction" -- src/` shows **zero** definitions of `riemannZeta` in `src/` and only two unrelated `def LFunction` declarations in `src/`, both inside distinct namespaces (`GroundTheory.Global.HeckeCharacter.LFunction` at `src/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean:363` and `GroundTheory.Automorphic.GodementJacquet.LFunction` at `src/GroundTheory/AutomorphicForms/GL2/GJLocalZeta.lean:431`), neither shadowing `DirichletCharacter.LFunction`.
- Elaborating `~/rh-audit/agents3/work/J/CheckStatements.lean` via `~/rh-audit/agents3/leanc.sh` (exit code `0`) verified definitional equalities by `rfl`:
  - `RiemannZetaZerosOnLine = RiemannHypothesis`
  - `Claim.Zeta = RiemannHypothesis`
  - `UpperTheory.EveryCharacter = DirichletLNonvanishingRightOfHalf`
  - `Claim.HalfPlane = DirichletLNonvanishingRightOfHalf`
  - `Claim.Strip = DirichletLZerosOnLine`

---

## 4. Hidden-Hypotheses Audit on the Chain (and Repository-Wide Scan)

### 4.1 Repository-wide scan of `src/` for escape hatches

Commands executed inside `~/rh-audit/src/omega`:
```sh
git grep -n -w -F "sorry" -- src/
git grep -n -w -F "axiom" -- src/
git grep -n -w -F "opaque" -- src/
git grep -n -F "implemented_by" -- src/
git grep -n -w -F "native_decide" -- src/
git grep -n -w -F "sorryAx" -- src/
git grep -n -w -F "unsafe" -- src/
```
Results:
- **`sorry`**: 5 hits, **all** in `src/Challenge.lean:19, 21, 23, 25, 27` (the Comparator challenge file, not imported by `Main.lean`). **0 hits** in all other files under `src/`.
- **`axiom`**: **0 hits** in `src/`.
- **`opaque`**: **0 hits** in `src/`.
- **`implemented_by`**: **0 hits** in `src/`.
- **`native_decide`**: **0 hits** in `src/`.
- **`sorryAx`**: **0 hits** in `src/`.
- **`unsafe`**: **0 hits** in `src/`.

### 4.2 Scan of all enclosing files on the chain of Item 1

Every file inspected along the chain (53 files spanning `Main.lean`, `Statements.lean`, `MainTheoremsAll.lean`, `MainTheoremsCritical.lean`, `MainTheorems.lean`, `CritLine.lean`, `RhOfRight.lean`, `MainConclusion.lean`, `EveryCharacter.lean`, `HalfPlane.lean`, `ClaimStrip.lean`, `Imprimitive.lean`, `ZeroFreeAllOfTopG.lean`, `DesWin.lean`, `SupplyChi.lean`, `Supply.lean`, `ExistsPageN.lean`, `HostOfField.lean`, `DivinNOfHypV.lean`, `RiemannHypothesisOfEveryCharacter.lean`, `EveryCharacterOfLiteratureOfVWin.lean`, `SiegelEisensteinSecondTermHypotheses.lean`, `TopPlug.lean`, `ShapeOf.lean`, `TopShape.lean`, `TopShapeAlt.lean`, `Hyps.lean`, `HypothesesNonemptyOfUnramifiedExponents.lean`, `VwinOfRow.lean`, `TopMainZj.lean`, `WindowBoundOfLiteratureLevel.lean`, `RowSrc.lean`, `GaloisRepresentationsOfThetaLift.lean`, `RecTExists.lean`, `IsRecTOfIsRec.lean`, `WeightsConjBis.lean`, `LevelGmLeOnFamilyScales.lean`, `WindowInequalityOfArtinInputs.lean`, `Imports.lean`, `LevelFamily.lean`, `CoreGm.lean`, `ZeroFreeOfRpowWindow.lean`, `lemmaL.lean`, `poleData.lean`, `landauWindow.lean`, `CharFamily.lean`, `LandauZeroFreeCriterion.lean`, `ExplicitFormulaErrorOfHostConditions.lean`, `TopWin.lean`, `TopDefs.lean`, `Window.lean`, `supplyOfAdmOf.lean`, `pairEx.lean`) was grepped for:
`axiom`, `opaque`, `implemented_by`, `native_decide`, `sorry`, `local instance`, `local notation`, `macro`, `elab`, `variable`, `include`, `omit`, `notation`, `syntax`.

Findings:
- **`axiom`, `opaque`, `implemented_by`, `native_decide`, `sorry`, `include`, `omit`, `local notation`, `macro`, `elab`, `notation`, `syntax`**: **0 hits** across all 53 files.
- **`attribute [local instance]`**: 3 hits, all identical in kind:
  - `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:18`:
    `attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField`
  - `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:12`:
    `attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField`
  - `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:9`:
    `attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField`
  Looking up `complRel` and `isLocalField` in `~/rh-audit/index/decls.txt` shows they are `ValuativeRel (p.adicCompletion F)` (`ExistsContinuousPadic.lean:191`) and `IsNonarchimedeanLocalField (Fv F v)` typeclass instances on nonarchimedean completions of number fields; they do not add propositional assumptions or alter the meaning of `RiemannHypothesis`, `riemannZeta`, or `DirichletCharacter.LFunction`.
- **`variable` declarations**: found only in 8 helper files (`Supply.lean:14`, `WindowInequalityOfArtinInputs.lean:14-15`, `ExplicitFormulaErrorOfHostConditions.lean:22, 131`, `TopDefs.lean:20-21, 32`, `TopWin.lean:20-21, 38, 48`, `Window.lean:22, 35`, `IsRecTOfIsRec.lean:18, 30-31, 33, 74`, `WeightsConjBis.lean:23-24, 36-37`). Every one of these declares ordinary data/type parameters (`G : FReq`, `Λ : Level`, `φ : Frame`, `Fam`, `core`, `Tied`, `P`, `HypV`, field/place parameters `k`, `E`, `Ω`, `A`, `w`, `h`, `Rc`). None introduces a propositional hypothesis, none is paired with `include`, and `Main.lean`, `Statements.lean`, `MainTheorems.lean`, `CritLine.lean`, `RhOfRight.lean`, `MainConclusion.lean`, `EveryCharacterOfLiteratureOfVWin.lean`, `SiegelEisensteinSecondTermHypotheses.lean`, and `TopPlug.lean` have **zero** `variable` declarations.

---

## 5. Search for Unfolded-Form RH / GRH Hypotheses on the Chain and Its Helpers

Targeted searches across the chain directories (`Main.lean`, `Statements.lean`, `Supplements/`, `Formalism/GammaFactorNonvanishing/`, `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`, `Development/AutomorphicArithmetic/{CharacterBoxes,PrimitiveCosets,DedekindLFunctions,ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries,AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases}/`) using:
- `git grep -n -F "1 / 2 <"`
- `git grep -n -F "s.re = 1 / 2"`
- `git grep -n -w -F "EveryCharacter"` (repo-wide)
- `git grep -n -w -F "ZeroFreeAll"` (repo-wide)
- `git grep -n -w -F "HalfPlane"` (in `CharacterBoxes/`, `Supplements/`, `Main.lean`)
- `git grep -n -F "LFunction"` (in chain directories)

Every hit where a statement of the shape "all nontrivial zeros of $\zeta$ have $\operatorname{Re}(s) = 1/2$" or "$L(\chi, s) \neq 0$ for $\operatorname{Re}(s) > 1/2$" appears as a **hypothesis** is listed below, along with how it is discharged:

1. **`Formalism.VW.rh_of_right`** (`src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:5`):
   - Hypothesis: `(hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)`
   - Status: **DISCHARGED** inside `Formalism.VW.rh_of_every` (`CritLine.lean:29-32`) from `(h : UpperTheory.EveryCharacter)`.

2. **`Formalism.VW.rh_of_every`** (`src/Formalism/GammaFactorNonvanishing/CritLine.lean:29`):
   - Hypothesis: `(h : UpperTheory.EveryCharacter)` (unfolded: `∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0`)
   - Status: **DISCHARGED** in `rhOfAll` (`src/Supplements/Kernels/MainTheorems.lean:9`) by `allChi : UpperTheory.EveryCharacter` (`MainTheorems.lean:7`), whose proof is `UpperTheory.FinalTheorems.everyCharacter` (`MainConclusion.lean:10-11`).

3. **`Formalism.VW.critLine`** (`src/Formalism/GammaFactorNonvanishing/CritLine.lean:11-12`):
   - Hypothesis: `(h : UpperTheory.EveryCharacter)`
   - Status: **DISCHARGED** in `critAll` (`src/Supplements/Kernels/MainTheorems.lean:11-13`) by `allChi : UpperTheory.EveryCharacter`.

4. **`Claim.strip` and `Claim.zeta`** (`src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:59, 75`):
   - Hypothesis: `(h : HalfPlane)` where `Claim.HalfPlane` (`HalfPlane.lean:3-4`) is definitionally equal to `UpperTheory.EveryCharacter`.
   - Status: **DISCHARGED** in `claimAll` (`src/Supplements/Kernels/MainTheorems.lean:15-16`: `theorem claimAll : Claim.HalfPlane ∧ Claim.Strip ∧ Claim.Zeta := ⟨allChi, Claim.strip allChi, Claim.zeta allChi⟩`) by `allChi`.

5. **`UpperTheory.zeta_ne_zero_of_everyCharacter` and `UpperTheory.riemannHypothesis_of_everyCharacter`** (`src/Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean:211, 215`):
   - Hypothesis: `(h : UpperTheory.EveryCharacter)`
   - Status: **DISCHARGED** in `UpperTheory.FinalTheorems.riemannHypothesis` (`MainConclusion.lean:13-14`) by `UpperTheory.FinalTheorems.everyCharacter` (not even used by `Main.lean`, which routes via `rhOfAll`).

6. **`UpperTheory.Top.imprimitive`** (`src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:5-7`):
   - Hypothesis: `ZeroFreeAll` (unfolded: `∀ ψ : PChar, True → ∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0`)
   - Status: **DISCHARGED** in `UpperTheory.Top.every_character_of_green_v_win` (`TopPlug.lean:16-18`) by `UpperTheory.Top.zero_free_all_of_green_v_win` (`TopPlug.lean:12-15`):
     ```lean
     theorem UpperTheory.Top.zero_free_all_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
         (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) : Formalism.HC.ZeroFreeAll
     ```

7. **`Formalism.HC.zeroFreeOn_of_levels`** (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:45`):
   - Hypothesis: `(h : ∀ ψ, Q ψ → ∃ Λ : Level, ψ ∈ Λ.KEPT ∧ Λ.ZeroFreeLevel)` where `Λ.ZeroFreeLevel` (`ExplicitFormulaErrorOfHostConditions.lean:24-26`) unfolds to `∀ ψ ∈ Λ.KEPT, ∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0`.
   - Status: **DISCHARGED** in `Formalism.HC.zeroFreeOn_of_tiedWin` (`TopWin.lean:83-88`) by `Formalism.HC.level_of_tiedWin` (`TopWin.lean:68-81`):
     ```lean
     theorem level_of_tiedWin {Λ : Level} {la : ℝ} (h112 : ChebyshevInequalityOnWindows @core @Tied Λ)
         (hB : Λ.FormBAt la) (h : ChebyshevInequalityAtWindowScale @core @Tied la Λ) : Λ.ZeroFreeLevel
     ```
   - In turn, `level_of_tiedWin` proves `Λ.ZeroFreeLevel` from `ChebyshevInequalityOnWindows`, `Λ.FormBAt la` (discharged by `UpperTheory.Comparison₂.formB` -> `Deduction.zeroFree_of_rpow_window` -> `Deduction.lemmaL` -> `Deduction.landau_window` + `Deduction.poleData`), and `ChebyshevInequalityAtWindowScale` (discharged from `TopG` and `supplyChi`).

8. **Non-RH zero-free box in `PairGood` (for completeness)**:
   - `UpperTheory.Top.ZeroBox` (`PairGood.lean:12-13`: `∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → DirichletCharacter.LFunction χ s ≠ 0`) and `RealBox` (`PairGood.lean:32-34`: `1 - 1 / 400 < β`) restrict zeros only in a classical narrow region near $\operatorname{Re}(s) = 1$ (width $1/400$), not $\operatorname{Re}(s) > 1/2$, and `PairEx` (`PairGood.lean:28-30`) is discharged by `theorem pairEx : UpperTheory.Top.PairEx` (`src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:112-170`).

**None of these hypotheses is left open at the top level.** Every theorem in `src/Main.lean:4-12` has **zero** binders / hypotheses.

---

## 6. Conclusion

**NO** (within the depth examined — 12 levels from `src/Main.lean:4` down to `Deduction.lemmaL` / `Deduction.landau_window`, plus a repository-wide scan of `src/` for `RiemannHypothesis`, `EveryCharacter`, `ZeroFreeAll`, `sorry`, `axiom`, `opaque`, `implemented_by`, and `native_decide`).
Unlike Nielsen's `theorem claimed_rh (hRH : RiemannHypothesis)` (`NielsenMinimal.lean:35`), `Main.lean`'s `theorem riemannHypothesis : RiemannHypothesis` (`src/Main.lean:4`) takes **no** hypotheses and references Mathlib's `RiemannHypothesis` directly.
Across the entire repository, `RiemannHypothesis` appears **0 times** as a hypothesis or binder type (`git grep -n -w -F RiemannHypothesis`: 51 hits total, 0 in class (b)).
Every intermediate lemma on the chain whose hypothesis is RH or GRH in folded or unfolded form (`rh_of_right`, `rh_of_every`, `imprimitive`, `zeroFreeOn_of_levels`, `Claim.strip`, `Claim.zeta`) is discharged upstream, terminating in Landau's window criterion (`Deduction.lemmaL`) applied to Chebyshev inequalities derived from `TopG` and `VWin`.
No `axiom`, `opaque`, `implemented_by`, `native_decide`, `unsafe`, `sorryAx`, or non-`Challenge.lean` `sorry` exists anywhere under `src/`.

---

## Summary Table

| Check | Scope | Result |
|---|---|---|
| `Main.lean` top-level binders | `src/Main.lean:4-12` (all 5 theorems) | 0 hypotheses / binders |
| `RiemannHypothesis` in class (b) | Entire repo (`51` word hits) | `0` hits (47 concl, 1 proof, 3 docs) |
| Other 4 `Main.lean` statement names in class (b) | Entire repo (`4` hits each) | `0` hits; all defined in `Statements.lean` via Mathlib |
| Shadowing of `RiemannHypothesis` / `riemannZeta` / `LFunction` | `decls.txt` (1.06M lines) & `src/` | None (`Statements.lean` imports only `Mathlib`) |
| `sorry` / `axiom` / `opaque` / `implemented_by` / `native_decide` | All of `src/` (~175k files) | Only 5 `sorry` in `src/Challenge.lean`; `0` elsewhere |
| Hidden `variable` / `include` / `macro` / `elab` / `local notation` | 53 chain files | None adding hypotheses (`3` benign local field instances) |
| Unfolded RH/GRH hypotheses on chain | Levels 0–12 (`Main.lean` to `lemmaL`) | All 7 helper-lemma hypotheses discharged upstream |
| Lean 4.33.1 elaboration checks (`leanc.sh`) | `CheckStatements.lean`, `NielsenMinimal.lean`, `RhOfRight.lean` | All 3 elaborated cleanly (`exit 0`) |
| Counterpart to Nielsen's `hRH` on route to `riemannHypothesis` | Levels 0–12 + repo-wide scans | **NO** |

---

## What I Could Not Verify

1. **Full Lean 4 kernel elaboration / axiom replay of `src/Main.lean` and the ~175k release modules**: **NOT VERIFIED**, because the release itself is not built in this environment and the rules forbid building or modifying anything outside `work/J/` and the report file. Consequently, while textual inspection shows zero `axiom`, `opaque`, `sorry`, `implemented_by`, `native_decide`, `unsafe`, or `sorryAx` under `src/` (outside `src/Challenge.lean`), I did not independently verify via Lean's kernel (`#print axioms riemannHypothesis`, `leanchecker`, or Comparator) that `Main.lean` and all transitive imports compile cleanly or emit only `[propext, Classical.choice, Quot.sound]`.
2. **Transitive inspection below Level 12 across all ~175k modules**: **NOT VERIFIED** exhaustively. I traced the chain from `Main.lean:4` down 12 levels until the statements stopped mentioning zeros of `riemannZeta` / `DirichletCharacter.LFunction` (`Row0b`, `RecTExists`, `VWin`, `TopG`, `HypsAlt`, `landau_window`), and audited all 53 chain files for hidden-hypothesis constructs. I did not read the interior of the deeper automorphic, Galois-representation, Arakelov-height, or mean-square subtrees (including whether any deep internal object such as `anyGeometry` at `SiegelEisensteinSecondTermHypotheses.lean:60` / `OverIx.lean:19` is vacuous or non-vacuous — that question is outside whether an `hRH` assumption exists on the route to `riemannHypothesis`, and is **NOT VERIFIED** here).
3. **Complete repo-wide scan for `macro`, `elab`, `local notation`, or `local instance`**: **NOT VERIFIED** across all 175k files; verified across all 53 files on the traced chain (0 `macro`/`elab`/`local notation`/`syntax`/`notation`, 3 benign `local instance` lines for nonarchimedean local-field structures on `adicCompletion`).
