# Independent Review (Task K): Faithfulness of Nielsen's Minimal Example

Target materials examined:
- Posted example (indentation-restored): `~/rh-audit/agents3/input/NielsenMinimal.lean` (verbatim flush-left copy at `~/rh-audit/agents3/input/posted_verbatim.txt`).
- Critic's paper: `~/rh-audit/nielsen/paper.txt` (Abstract, Sections 1–13, Appendix A).
- Release source checkout: `~/rh-audit/src/omega` (Lean sources under `~/rh-audit/src/omega/src`).
- Mathlib v4.33.1 checkout: `~/rh-audit/challenge-rebuild/.lake/packages/mathlib`.
- Lean 4.33.1 elaboration check on `NielsenMinimal.lean`:
  - Command: `~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/input/NielsenMinimal.lean`
  - Output (exit code `0`):
    ```text
    'claimed_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
    ```

---

## 1. Ingredient-by-Ingredient Mapping: Example vs. Release Source

| Ingredient in `NielsenMinimal.lean` | Claimed Counterpart in Release Source (with `file:line` and quoted code) |
|---|---|
| `anyGeometry := fun _ => True` (`NielsenMinimal.lean:7`: `def anyGeometry : ∀ (_ : Nat), Prop := fun _ => True`) | **FOUND.** Nielsen's paper (§2, `paper.txt:90–135`) points to `GlobalTheory.Mem.Top.Bl.anyGeometry` in `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean:14,19`:<br>`abbrev GeoP : Type 1 := ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop`<br>`def anyGeometry : GeoP := fun _ _ _ => True`<br>Wrapped in `GeoCl` / `geoCl` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotGeoClFalse.lean:21–28`: `inductive GeoCl (Γ : GeoP) : ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop \| base ... : Γ D J X → GeoCl Γ D J X \| step ...`, `def geoCl (Γ : GeoP) : GeoP := GeoCl Γ`). Verified via `git grep -n -w -F 'anyGeometry' \| wc -l` (`118` lines) and `git grep -l -w -F 'anyGeometry' \| wc -l` (`24` files), and `git grep -n -w -F 'GeoCl' src/` (`6` lines total: `NotGeoClFalse.lean:21,22,24,26,28` and `DivisionGeometryScalarsTransferSetDivision.lean:106`). Passed as `geoCl anyGeometry` in `nonempty_hyps_definite_side_of_closed_bound` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:60,63,67`). |
| `targetFormula` (`NielsenMinimal.lean:9`: `def targetFormula : Nat := 42`) | **FOUND (schematic counterpart).** Nielsen's paper (§7–§8, `paper.txt:355–399, 488–496`) points to the explicit real-valued height formula `Formalism.BasicNotions.DV.hExpl6` in `src/Formalism/LocalRingCardinality/KernelPlaceMeanBound.lean:25–27`:<br>`def hExpl6 (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ) (u : D.what₂.Word) : ℝ :=`<br>`  SZbP D L C u + (∑ j ∈ SizeData₂.lifts D, kernelPlaceMeanBound D L C u j) - (∑ j ∈ SizeData₂.lifts D, L6lo D L C j) -`<br>`    meanE D (fun e => Real.log (X.kapR e))`<br>(Unlike the constant `42`, `hExpl6` is a nontrivial real formula in `D`, `L`, `X.kapR`, `C`, `u`, which is later subjected to norm/matrix bounds in `RecBridge.lean` and `ConstantGeTwentyEight.lean`.) |
| `DegenerateModel` with `vol : Nat := 0`, `height : Nat`, `h_eq : height = targetFormula` (`NielsenMinimal.lean:11–14`) | **FOUND (composite of two distinct layers in the release).**<br>1. *Degenerate geometric model (`vol := 0`, etc.):* `paper.txt:144–185` points to `geoDegenerate` (`src/Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean:241–306`: `Var := ℕ`, `Eff := fun _ _ => True`, `H0 := fun _ _ => ⊤`, `nef := fun _ _ => True`, `big := fun _ _ => True`, `vol := fun _ _ => 0`, `pn := fun _ _ _ _ _ _ => 0`, `arVol := fun _ _ => 0`), `divXFl` (`Inhabited.lean:829–861`: `geo := geoDegenerate ...`, `degHH := fun _ _ _ => 0`, `iMj := fun j _ => (0 : (X0.MjH j).V →ₗ[D.what₂.LL] D.what₂.LL)`, `iMj_mem := fun _ _ _ => Submodule.mem_top`), and seed `x0` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:57–122`: `Lev := Empty`, `Comp := fun _ => Empty`, `Surf := Empty`, `kapR := fun _ => kapSharp D`).<br>2. *Height field and `h_eq := rfl`:* `paper.txt:376–414` points to `DivData.h : Words → ℝ` (`src/Formalism/LocalRingCardinality/DataArith.lean:148`), initialized to `fun _ => 0` in `exists_divStage_of_pk` callers (`StartStateUntwistedEmptyLocal.lean:54–55`, `BareStatementOfDiscreteSeries.lean:252–254`) and `exists_divStage` (`ExistsDivStage.lean:348`), then overwritten via `setDiv` (`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/SetUnipotentTranslate.lean:25–31`: `h := h`) with `def ht : D.what₂.Word → ℝ := DV.hExpl6 D p.L Y.X C.Csz` (`SetUnipotentTranslate.lean:379`), so that `ExtraAt.h_eq : ∀ u, D.div.h u = DV.hExpl6 D L X C.Csz u` (`src/Formalism/SharpRestriction/InertJacobiLevels/AsmIface.lean:163`) is proved by `h_eq := fun _ => rfl` (`SetUnipotentTranslate.lean:400`) and propagated to `FamP.h_eq` (`src/Formalism/SharpRestriction/ParConsts.lean:73`, copied in `FamRaise.lean:36`). *(Correction to `paper.txt:397–398`: `DisjointSplitLevelPlaces.lean:331,501` sets a different field `RawDat.h_eq : h = hP * k`, not the divisor height equation.)* |
| `Bundle` (`NielsenMinimal.lean:16–18`: `structure Bundle where geoOk : anyGeometry 0; model : DegenerateModel`) | **FOUND (composite schematic counterpart).** `paper.txt:17–22, 110–135, 381–401, 480–488` groups several release structures under this role: `OAt` (`OverIx.lean:44–47`: `geo : Γ (w.st Z).toD7 t.r.z.core.toCore X; lam : LamAre t.r.Z X`), `DivX` (`src/Formalism/LocalRingCardinality/DataDIV.lean:418–544`), `Pt` / `ExtraAt` (`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/DisjointExceptional.lean:15–20`, `AsmIface.lean:157–164`), and the 50+-field hypothesis bundle `HypsAlt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean:22–90`) and `Hyps` (`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/APerTw.lean:23–91`). |
| `buildBundle` (`NielsenMinimal.lean:20–25`: `{ geoOk := trivial; model := { vol := 0; height := 42; h_eq := rfl } }`) | **FOUND (composite schematic counterpart).** Constructed across multiple release definitions/theorems cited in `paper.txt:110–166, 378–401`: `divEx_prov` (`TupPinsOfMuIsW.lean:204–209`: `exact ⟨⟨trivial, lamAre_heq hp ht (hX ▸ h4)⟩⟩`), `geoOver_stages` and `exists_divT` (`TupPinsOfMuIsW.lean:155–166, 178–192`: builds `x0`, grafts `divXFl`, proves `MjAre` by `rfl`/`HEq.rfl`, `kapR` by `fun _ => rfl`, `LamAre` by `rfl`), `LedPart.pt` (`SetUnipotentTranslate.lean:381–401`: `D := setDiv D (nPrime p.L) p.ht`, `h_eq := fun _ => rfl`), and `nonempty_hyps_definite_side_of_closed_bound` (`SiegelEisensteinSecondTermHypotheses.lean:44–68`, constructing `Nonempty (HypsAlt ...)` using `geoCl anyGeometry` on lines 60, 63, 67 via `hypotheses_nonempty_of_unramified_exponents_alt` in `HypothesesNonemptyOfUnramifiedExponents.lean:41–61` and `nonempty_hyps_of_allRows_alt` in `NonemptyHypsOfAllRows.lean:19–101`). |
| `valid_bundle_of_manufactured` (`NielsenMinimal.lean:29–31`: `private lemma valid_bundle_of_manufactured (b : Bundle) : anyGeometry 0 ∧ b.model.height = targetFormula := ⟨b.geoOk, b.model.h_eq⟩`) | **PARTIAL COUNTERPART.** The trivial field-extraction / `rfl`-projection pattern mirrors: `divEx_prov` (`TupPinsOfMuIsW.lean:204–209`), `exists_divT` (`TupPinsOfMuIsW.lean:178–192`), `tiedDataS_assemble_alt` (`TiedDataSAssemble.lean:20–53`, asserting `HEq S.geo geo` by `HEq.rfl`), and the reading of `Fm.h_eq` in `linkDIVt_of_rows` / `linkDIVt_of_rowsF` (`src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:565, 687`: `have hhx : ∀ u, (Fm.D x i).div.h u = hExpl6 (Fm.D x i) (Fm.L x i) (Fm.X x i) Fm.Csz u := Fm.h_eq x hx1 i`). In addition, `zero_free_all_of_green_v_win` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:14–15`) supplies `trivial, trivial` for the two `True` parameters `V, NR` of `forall_goal_of_shape_of_hyps` (`ShapeOf.lean:31–32`, `TopShape.lean:33`). However, unlike `valid_bundle_of_manufactured` (which returns only its own bundle fields), `RecBridge.lean:566–573, 688–695` and `ConstantGeTwentyEight.lean:184–210` (`divClausesR_of`) establish matrix/operator-norm inequalities (`WordFacts`, `LinkDIV_at`) that enter `topDesWin` (`DesWin.lean:11–31`) and `zeroFreeAll_of_topG` (`ZeroFreeAllOfTopG.lean:26–34`). |
| The hypothesis `(hRH : RiemannHypothesis)` (`NielsenMinimal.lean:35`: `theorem claimed_rh (hRH : RiemannHypothesis) :`) | **NO COUNTERPART FOUND.** Searched `src/Main.lean`, `src/Supplements/Kernels/MainTheorems.lean`, `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`, the entire live proof chain down to `zeroFreeOn_of_tiedWin_cyc`, and ran `git grep -n -w -F 'RiemannHypothesis'`, `git grep -n -w -F 'RiemannZetaZerosOnLine'`, and `git grep -n -w -F 'sorry'` / `axiom` / `native_decide` / `unsafe` / `opaque` across the full repo (details in Section 2). Every top-level theorem in `src/Main.lean` has **zero hypotheses**, and no declaration in `src/` takes `RiemannHypothesis` as an assumption. |
| The final conjunction `(∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis` (`NielsenMinimal.lean:36–38`) | **NO COUNTERPART FOUND.** In `src/Main.lean:4–12`, the headline theorem is `theorem riemannHypothesis : RiemannHypothesis := rhOfAll` (plain `RiemannHypothesis`, no bundle conjunct). The other four theorems in `Main.lean` are `RiemannZetaZerosOnLine`, `DirichletLNonvanishingRightOfHalf`, `DirichletLZerosOnLine`, and `PrimitiveDirichletLZerosOnLine` (`Statements.lean:3–16`). `MainConclusion.lean:13–14` also has type plain `RiemannHypothesis`. `claimAll` (`MainTheorems.lean:15–16`) is `Claim.HalfPlane ∧ Claim.Strip ∧ Claim.Zeta` (`HalfPlane.lean:3–10`), a conjunction of three analytic L-function/zeta statements, not a conjunction with an existential vacuous bundle. Searched all 47 occurrences of `RiemannHypothesis` in `src/` (Section 2); none conjoins `RiemannHypothesis` with an existential bundle witness. |

---

## 2. Detailed Search for Any Counterpart to `(hRH : RiemannHypothesis)`

### 2.1 Top-level chain from `src/Main.lean`

Every theorem in the release entry point `src/Main.lean:1–12` is a closed term with **no hypotheses**:
```lean
-- src/Main.lean:4-12
theorem riemannHypothesis : RiemannHypothesis := rhOfAll
theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi
theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1
theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
```
Here `RiemannHypothesis` is Mathlib's definition (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185–186`):
```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```
Tracing the exact chain of definitions from `riemannHypothesis` downward:
1. `src/Supplements/Kernels/MainTheorems.lean:7,9`:
   ```lean
   theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter
   theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi
   ```
   (`Formalism.VW.rh_of_every` at `src/Formalism/GammaFactorNonvanishing/CritLine.lean:29–32` derives `RiemannHypothesis` from `UpperTheory.EveryCharacter` via `Formalism.VW.rh_of_right` at `src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:5–62`, using Mathlib's functional equation `riemannZeta_one_sub`.)
2. `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7–11`:
   ```lean
   theorem UpperTheory.FinalTheorems.everyCharacter_of_row (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) : UpperTheory.EveryCharacter :=
     UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩ (UpperTheory.One.vwin_of_row h)

   theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=
     UpperTheory.FinalTheorems.everyCharacter_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
   ```
   All arguments are closed terms: `galoisLocalGlobalStrong_recParameter` (`RowSrc.lean:6`, 0 hypotheses), `recTExists` (`RecTExists.lean:20–66`, 0 hypotheses), `vwin_of_row` (`VwinOfRow.lean:4–5`, applied to `h`).
3. `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810–813` calls `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (`SiegelEisensteinSecondTermHypotheses.lean:69–73`), which calls `UpperTheory.Top.every_character_of_green_v_win` (`TopPlug.lean:16–18`), which calls `UpperTheory.Top.zero_free_all_of_green_v_win` (`TopPlug.lean:12–15`), which calls `UpperTheory.Top.zeroFreeAll_of_topG` (`ZeroFreeAllOfTopG.lean:26–34`), which calls `Formalism.HC.zeroFreeOn_of_tiedWin_cyc` (`TopWin.lean:90–93`).

Nowhere on this chain is `RiemannHypothesis` (or `RiemannZetaZerosOnLine`, `EveryCharacter`, or `ZeroFreeAll`) passed as an undischarged hypothesis. Even Nielsen's own paper agrees on this point:
- `paper.txt:14–16`: [quotation from the paper omitted]
- `paper.txt:842`: [quotation from the paper omitted]

### 2.2 Repository-wide search for `RiemannHypothesis`, `sorry`, `axiom`, and `Challenge`

- Command: `cd ~/rh-audit/src/omega && git grep -n -w -F 'RiemannHypothesis'`
  - Total matches across the entire repository: **51 lines** (4 non-`src/` lines: `README.md:13,141`, `ci/Audit.lean:3`, `verification/NOTES.md:62`; and **47 lines** in `src/`).
  - Inspected all 47 lines in `src/` with surrounding context (`git grep -n -C 3 -w -F 'RiemannHypothesis' src/Formalism/ src/Development/ src/Supplements/ src/Main.lean src/Statements.lean`):
    - **1 line** is `src/Challenge.lean:19` (`theorem riemannHypothesis : RiemannHypothesis := by sorry`), a standalone Comparator challenge file not imported anywhere in `src/` (verified by `git grep -n -w -F 'Challenge'`, which returned only `.github/workflows/checks.yml`, `README.md`, `comparator.json`, `lakefile.toml`, and `verification/NOTES.md`).
    - **1 line** is `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:102`: `theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl`.
    - **1 line** is `src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:6`: `unfold RiemannHypothesis` inside the proof of `rh_of_right`.
    - All remaining **44 lines** in `src/` place `RiemannHypothesis` exclusively in **conclusion** position (either `: RiemannHypothesis` or `... → RiemannHypothesis` or `... → RiemannHypothesis ∧ ...`).
    - **Zero occurrences** in `src/` take `RiemannHypothesis` as a hypothesis/parameter.
- Command: `cd ~/rh-audit/src/omega && git grep -n -w -F 'sorry' src/ ; git grep -n -E '^[[:space:]]*axiom[[:space:]]' src/ ; git grep -n -w -F 'native_decide' src/ ; git grep -n -E '^[[:space:]]*(unsafe|opaque|implemented_by)[[:space:]]' src/`
  - Output: the **only** matches across all of `src/` are the 5 `:= by sorry` challenge targets in `src/Challenge.lean:19,21,23,25,27`. Excluding `src/Challenge.lean`, there are **0** matches for `sorry`, `axiom`, `native_decide`, `unsafe`, `opaque`, or `implemented_by` (consistent with `verification/static-scan.txt:1–8`).

---

## 3. Steelman Experiment: Can the Example Prove `RiemannHypothesis` Without `(hRH : RiemannHypothesis)`?

Six genuinely different attempts were constructed in `~/rh-audit/agents3/work/K/` preserving all vacuous ingredients of `NielsenMinimal.lean` (`anyGeometry := fun _ => True`, `targetFormula := 42`, `DegenerateModel` with `vol := 0`, `height := 42`, `h_eq := rfl`, `Bundle`, `buildBundle`, `valid_bundle_of_manufactured`), zero `sorry`, zero custom axioms, and zero hypotheses on the target theorem of type `RiemannHypothesis` (or `(∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis`). Every file was checked with `~/rh-audit/agents3/leanc.sh`.

**Result: 0 of 6 attempts succeeded. Every attempt failed to compile (`EXIT_CODE=1`).**

### Attempt 1: Extract `RiemannHypothesis` directly from the manufactured bundle
- **File:** `~/rh-audit/agents3/work/K/steelman_1_extract_from_bundle.lean`
- **Strategy:** Drop `(hRH : RiemannHypothesis)` and try to supply `hb.1 : anyGeometry 0` or `buildBundle.model.h_eq : buildBundle.model.height = targetFormula` as the proof of `RiemannHypothesis`.
- **Exact compiler output (`EXIT_CODE=1`):**
  ```text
  ~/rh-audit/agents3/work/K/steelman_1_extract_from_bundle.lean:35:18: error: Application type mismatch: The argument
    hb.left
  has type
    anyGeometry 0
  but is expected to have type
    RiemannHypothesis
  in the application
    ⟨Exists.intro b hb, hb.left⟩
  ~/rh-audit/agents3/work/K/steelman_1_extract_from_bundle.lean:38:2: error: Type mismatch
    buildBundle.model.h_eq
  has type
    buildBundle.model.height = targetFormula
  but is expected to have type
    RiemannHypothesis
  ```
- **Why it fails:** `anyGeometry 0` reduces definitionally to `True`, and `buildBundle.model.h_eq` has type `42 = 42`. Neither is definitionally equal to, nor logically implies, Mathlib's `RiemannHypothesis`.

### Attempt 2: Add a `rh : RiemannHypothesis` field to `Bundle`
- **File:** `~/rh-audit/agents3/work/K/steelman_2_bundle_carries_rh.lean`
- **Strategy:** Add `rh : RiemannHypothesis` to `structure Bundle`, so `claimed_rh` takes no hypothesis and simply extracts `b.rh`. Populate `buildBundle` with `rh := trivial`.
- **Exact compiler output (`EXIT_CODE=1`):**
  ```text
  ~/rh-audit/agents3/work/K/steelman_2_bundle_carries_rh.lean:26:10: error: Type mismatch
    trivial
  has type
    True
  but is expected to have type
    RiemannHypothesis
  ```
- **Why it fails:** Moving `RiemannHypothesis` into a structure field only shifts the proof obligation from `claimed_rh` to `buildBundle`. Without an actual proof of `RiemannHypothesis`, `buildBundle` cannot be inhabited.

### Attempt 3: Close `RiemannHypothesis` with `rfl`, `trivial`, `decide`, or `RiemannHypothesis = RiemannHypothesis`
- **File:** `~/rh-audit/agents3/work/K/steelman_3_rfl_trivial_decide.lean`
- **Strategy:** Keep all vacuous ingredients; try to prove `RiemannHypothesis` via `rfl`, `trivial`, `decide`, and via `Eq.mp rh_eq_rh trivial` where `theorem rh_eq_rh : RiemannHypothesis = RiemannHypothesis := rfl` (testing the claim in `paper.txt:29–30, 510–511` about certifying the tautology `"RiemannHypothesis = RiemannHypothesis"`).
- **Exact compiler output (`EXIT_CODE=1`):**
  ```text
  ~/rh-audit/agents3/work/K/steelman_3_rfl_trivial_decide.lean:34:2: error: Tactic `rfl` failed: Expected the goal to be a binary relation

  Hint: Reflexivity tactics can only be used on goals of the form `x ~ x` or `R x x`

  ⊢ RiemannHypothesis
  ~/rh-audit/agents3/work/K/steelman_3_rfl_trivial_decide.lean:37:2: error: Tactic `assumption` failed

  ⊢ RiemannHypothesis
  ~/rh-audit/agents3/work/K/steelman_3_rfl_trivial_decide.lean:40:2: error: failed to synthesize
    Decidable RiemannHypothesis

  Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
  ~/rh-audit/agents3/work/K/steelman_3_rfl_trivial_decide.lean:43:14: error: Application type mismatch: The argument
    trivial
  has type
    True
  but is expected to have type
    RiemannHypothesis
  in the application
    Eq.mp rh_eq_rh trivial
  ```
- **Why it fails:** `RiemannHypothesis` is a universally quantified proposition over `ℂ` about `riemannZeta`, not an equality (so `rfl` fails), not `True` (so `trivial` fails), and has no `Decidable` instance (so `decide` fails). Proving `rh_eq_rh : RiemannHypothesis = RiemannHypothesis` by `rfl` succeeds, but `Eq.mp rh_eq_rh` still has type `RiemannHypothesis → RiemannHypothesis` and requires a proof of `RiemannHypothesis`.

### Attempt 4: Universally quantified consumer (`∀ V NR G, TopShape V NR G → ...`)
- **File:** `~/rh-audit/agents3/work/K/steelman_4_polymorphic_consumer.lean`
- **Strategy:** Mirror the release's `TopShapeAlt` / `forall_goal_of_shape_of_hyps` (`TopShapeAlt.lean:24–99`, `ShapeOf.lean:31–32`, `TopPlug.lean:15`): define `TopShape (V NR G : Prop) := V → NR → (∀ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula → G)` and `goal_of_shape`, pass `trivial`, `trivial`, and `buildBundle`, and attempt to construct `shape_for_rh : TopShape True True RiemannHypothesis`.
- **Exact compiler output (`EXIT_CODE=1`):**
  ```text
  ~/rh-audit/agents3/work/K/steelman_4_polymorphic_consumer.lean:40:18: error: Type mismatch
    hb.left
  has type
    anyGeometry 0
  but is expected to have type
    RiemannHypothesis
  ```
- **Why it fails:** `goal_of_shape` compiles cleanly for arbitrary `V, NR, G : Prop`, and `trivial, trivial, buildBundle` satisfy the vacuous slots. However, specializing `G := RiemannHypothesis` requires supplying `shape_for_rh : True → True → ∀ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula → RiemannHypothesis`. Because `True`, `Bundle`, `anyGeometry 0`, and `42 = 42` are all inhabited (consistent), any proof of `shape_for_rh` requires proving `RiemannHypothesis` unconditionally.

### Attempt 5: Structure fields mentioning `RiemannHypothesis` vacuously (`Empty`, unsatisfiable hypothesis, `Iff.rfl`, `rfl`)
- **File:** `~/rh-audit/agents3/work/K/steelman_5_structure_field_mentions_rh.lean`
- **Strategy:** Mirror the release's `Empty`-indexed fields (`TupPinsOfMuIsW.lean:59–122`) and unsatisfiable-hypothesis fields such as `degHH_def` (`PlaceRankTwoOne.lean:142–146`): add fields `vacEmpty : Empty → RiemannHypothesis`, `vacUnsat : ∀ r : Nat, 0 < r → 0 = r * r → RiemannHypothesis`, `tautIff : RiemannHypothesis ↔ RiemannHypothesis`, and `tautEq : RiemannHypothesis = RiemannHypothesis` to `Bundle`. Populate `buildBundle` cleanly with zero `sorry`/axioms, then try to eliminate those fields to obtain `RiemannHypothesis`.
- **Exact compiler output (`EXIT_CODE=1`):**
  ```text
  'buildBundle' depends on axioms: [propext, Classical.choice, Quot.sound]
  ~/rh-audit/agents3/work/K/steelman_5_structure_field_mentions_rh.lean:47:27: error: Tactic `assumption` failed

  ⊢ Empty
  ~/rh-audit/agents3/work/K/steelman_5_structure_field_mentions_rh.lean:50:41: error: Application type mismatch: The argument
    rfl
  has type
    ?m.4 = ?m.4
  but is expected to have type
    0 = 1 * 1
  in the application
    buildBundle.vacUnsat 1 Nat.zero_lt_one rfl
  ~/rh-audit/agents3/work/K/steelman_5_structure_field_mentions_rh.lean:53:25: error: Application type mismatch: The argument
    trivial
  has type
    True
  but is expected to have type
    RiemannHypothesis
  in the application
    buildBundle.tautIff.mp trivial
  ```
- **Why it fails:** `buildBundle` itself compiles with only standard axioms, showing that vacuous fields mentioning `RiemannHypothesis` are easily inhabited. Yet none of them can be eliminated to produce a closed term of `RiemannHypothesis`: eliminating `vacEmpty` requires a term of `Empty`; eliminating `vacUnsat` requires a proof of `0 = r * r` for `0 < r`; eliminating `tautIff` requires a proof of `RiemannHypothesis`.

### Attempt 6: Redefine or shadow `RiemannHypothesis` as `True`
- **File:** `~/rh-audit/agents3/work/K/steelman_6_redefine_rh.lean`
- **Strategy:** Attempt (6a) to redefine `def RiemannHypothesis : Prop := True` at root scope after importing Mathlib, and (6b) to define `Fake.RiemannHypothesis := True` inside a namespace and pass `Fake.claimed_rh.2` to `example : _root_.RiemannHypothesis`.
- **Exact compiler output (`EXIT_CODE=1`):**
  ```text
  ~/rh-audit/agents3/work/K/steelman_6_redefine_rh.lean:27:4: error: `RiemannHypothesis` has already been declared
  ~/rh-audit/agents3/work/K/steelman_6_redefine_rh.lean:40:38: error: Type mismatch
    Fake.claimed_rh.right
  has type
    Fake.RiemannHypothesis
  but is expected to have type
    RiemannHypothesis
  ```
- **Why it fails:** Lean forbids redeclaring `_root_.RiemannHypothesis`, and a namespaced redefinition is not definitionally equal to Mathlib's `_root_.RiemannHypothesis`.

---

## 4. Converse Experiment: Vacuous Bundle Passed to a Consumer Proving a Non-Trivial Mathlib Fact

- **File:** `~/rh-audit/agents3/work/K/converse_vacuous_bundle.lean`
- **Construction:** Keeps every vacuous ingredient of `NielsenMinimal.lean` verbatim (`anyGeometry := fun _ => True`, `targetFormula := 42`, `DegenerateModel` with `vol := 0`, `height := 42`, `h_eq := rfl`, `Bundle`, `buildBundle`, `valid_bundle_of_manufactured`), then defines a consumer stated for **all** bundles (and two `True` shape inputs):
  ```lean
  theorem consumer_all_bundles (b : Bundle)
      (_hvalid : anyGeometry 0 ∧ b.model.height = targetFormula)
      (_hShape1 : True) (_hShape2 : True) :
      Irrational (Real.sqrt 2) :=
    irrational_sqrt_two

  theorem sqrt_two_irrational_via_vacuous_bundle : Irrational (Real.sqrt 2) := by
    let b := buildBundle
    exact consumer_all_bundles b (valid_bundle_of_manufactured b) trivial trivial
  ```
  as well as the conjunction `conj_sqrt_two_irrational : (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ Irrational (Real.sqrt 2)`.
- **Exact command and compiler output (`EXIT_CODE=0`):**
  - Command: `~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/K/converse_vacuous_bundle.lean`
  - Output:
    ```text
    theorem sqrt_two_irrational_via_vacuous_bundle : Irrational √2 :=
    let b := buildBundle;
    consumer_all_bundles b (valid_bundle_of_manufactured b) trivial trivial
    'sqrt_two_irrational_via_vacuous_bundle' depends on axioms: [propext, Classical.choice, Quot.sound]
    'conj_sqrt_two_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
    ```
- **Assessment:**
  1. **Is the final theorem valid?** Yes. `sqrt_two_irrational_via_vacuous_bundle` is a closed, hypothesis-free, `sorry`-free proof of Mathlib's `Irrational (Real.sqrt 2)` using only Lean's three standard axioms `[propext, Classical.choice, Quot.sound]`.
  2. **Does the vacuity of the bundle affect it?** No. As `#print sqrt_two_irrational_via_vacuous_bundle` shows, `buildBundle`, `valid_bundle_of_manufactured`, `trivial`, and (transitively) `anyGeometry`, `DegenerateModel`, `targetFormula`, and `rfl` all appear in the elaborated proof term and transitive constant dependencies of `sqrt_two_irrational_via_vacuous_bundle`. Yet none of that vacuity undermines the validity of the conclusion, because `consumer_all_bundles` had to prove `Irrational (Real.sqrt 2)` uniformly for **every** `Bundle` (including vacuous ones), which forces the consumer itself to carry an independent proof. Conversely, if a consumer is proved for every bundle matching a vacuous specification, supplying a vacuous bundle is logically harmless—and can only succeed if the consumer's proof does not depend on non-vacuous content from those slots.

---

## 5. Conclusion

1. `NielsenMinimal.lean` accurately models real vacuous patterns present in the release source: `anyGeometry := fun _ _ _ => True` (`OverIx.lean:19`) passed via `geoCl anyGeometry` (`SiegelEisensteinSecondTermHypotheses.lean:60,63,67`), degenerate geometric data with zero volumes/norms (`Inhabited.lean:241–306, 829–861`), `Empty`-indexed seed fields and copied lattice data (`TupPinsOfMuIsW.lean:57–122, 178–209`), and an assigned divisor height `setDiv` making `ExtraAt.h_eq` hold by `rfl` (`SetUnipotentTranslate.lean:25–31, 379–400`).
2. However, `NielsenMinimal.lean` adds two crucial elements not found anywhere in the release: the undischarged hypothesis `(hRH : RiemannHypothesis)` and a final conjunction attaching `(∃ b : Bundle, ...)` to `RiemannHypothesis`.
3. In the release, `src/Main.lean:4` proves plain `RiemannHypothesis` with **zero hypotheses**, and across all 175,187 files (excluding the unimported `src/Challenge.lean`), `RiemannHypothesis` never appears as a hypothesis and there are zero `sorry`/`axiom`/`native_decide` declarations.
4. All six steelman attempts to remove `(hRH : RiemannHypothesis)` while retaining only vacuous ingredients fail to typecheck in Lean 4.33.1; vacuous definitions and `rfl` assignments alone cannot produce a closed term of Mathlib's `RiemannHypothesis`.
5. The converse experiment confirms that passing a vacuous bundle and `trivial` inputs through a polymorphic consumer can produce a completely valid, hypothesis-free theorem whose proof term transitively references `anyGeometry` and `buildBundle`—provided the consumer proves the conclusion independently.
6. Therefore, `NielsenMinimal.lean` is **not** a faithful model of "how the code compiles": it compiles only because it assumes `hRH : RiemannHypothesis`, leaving unexplained how a hypothesis-free term of `RiemannHypothesis` could compile in the release.

---

## Summary Table

| Aspect | `NielsenMinimal.lean` | Release (`src/omega`) | Match? |
|---|---|---|---|
| Geometry predicate | `anyGeometry := fun _ => True` | `anyGeometry := fun _ _ _ => True` (`OverIx.lean:19`) | Yes |
| Degenerate geometry | `vol := 0` | `geoDegenerate` / `divXFl` (`Inhabited.lean:241,829`) | Yes |
| Assigned height + `rfl` | `height := 42`, `h_eq := rfl` | `setDiv ... p.ht`, `h_eq := fun _ => rfl` (`SetUnipotentTranslate.lean:382,400`) | Yes (formula nontrivial) |
| Hypothesis `(hRH : RH)` | Present (`NielsenMinimal.lean:35`) | **NO COUNTERPART FOUND** (`Main.lean:4` has 0 hypotheses) | **No** |
| Final statement | `(∃ b, ...) ∧ RiemannHypothesis` | `RiemannHypothesis` (`Main.lean:4`) | **No** |
| Steelman (drop `hRH`) | 6/6 attempts fail (`EXIT_CODE=1`) | Compiles only if consumer proves RH without vacuity (or kernel bug) | — |
| Converse (`√2` irrational) | Vacuous bundle + `trivial` → valid `Irrational √2` | Demonstrates vacuous deps do not invalidate a closed proof | — |
| Shows "how code compiles"? | Compiles only via added `hRH` | Unfaithful on the decisive hypothesis-free feature | **No** |

---

## What I Could Not Verify

- **Full build and kernel/checker replay of the release (`NOT VERIFIED`):** The release under `~/rh-audit/src/omega` is not built locally, and modifying or building it is prohibited. Accordingly, I did not run `lake build Main`, `#print axioms riemannHypothesis`, `transitivelyUsedConstants`, Comparator, `nanoda`, `con-leche`, or `lean4lean` on `Main.lean`. Whether `src/Main.lean` actually elaborates and passes Lean 4.33.1 or independent checkers is **NOT VERIFIED** from local execution here.
- **Transitive dependency closure of `riemannHypothesis` (`NOT VERIFIED` by compiler):** Because the release is unbuilt, I could not run Lean's `transitivelyUsedConstants` to confirm whether `geoDegenerate`, `divXFl`, `setDiv`, `LedPart.pt`, or `divEx_prov` lie in the compiled proof term of `Main.riemannHypothesis`. (I directly verified in source that `nonempty_hyps_definite_side_of_closed_bound` passes `geoCl anyGeometry` at `SiegelEisensteinSecondTermHypotheses.lean:60,63,67` and is called on the syntactic call chain from `Main.lean:4` -> `rhOfAll` -> `allChi` -> `everyCharacter` -> `everyCharacter_of_row` -> `every_character_of_literature_of_vWin` -> `every_character_of_theta_integrals_local_matching` -> `every_character_of_green_v_win` -> `zero_free_all_of_green_v_win`.)
- **Complete audit of all 175,187 files and downstream algebra (`NOT VERIFIED`):** I did not read all 175,187 files, nor did I verify the mathematical proof carried out inside `shape_closed_link_n_of_green`, `zeroFreeAll_of_topG`, `zeroFreeOn_of_tiedWin_cyc`, `galoisLocalGlobalStrong_recParameter`, or `vwin_of_row`. The absence of `sorry`, `axiom`, `native_decide`, `unsafe`, `opaque`, and `implemented_by` in `src/` (outside `src/Challenge.lean`) was verified by `git grep` text search only, not by kernel replay.
- **Kernel soundness of Lean 4.33.1 (`NOT VERIFIED`):** All steelman and converse tests were run against Lean 4.33.1 via `leanc.sh`; I did not audit the Lean 4.33.1 C++ kernel for soundness bugs (such as those noted in `verification/NOTES.md:100–104`).
