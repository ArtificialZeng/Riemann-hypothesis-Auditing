# Independent Review (Task O): Where Does the Conclusion Come From in the Release?

All source paths under the release root refer to `~/rh-audit/src/omega/`; Mathlib paths refer to `~/rh-audit/challenge-rebuild/.lake/packages/mathlib/`. In the example posted by Nielsen (`~/rh-audit/agents3/input/NielsenMinimal.lean:35-38`), `theorem claimed_rh (hRH : RiemannHypothesis)` takes `RiemannHypothesis` as a hypothesis and returns it unchanged in a conjunction with a manufactured bundle. Below is what the release code actually does at the end of its proof chain.

---

## 1. `src/Main.lean` and the Declarations It Refers To

### Full text of `src/Main.lean` (`src/Main.lean:1-12`)

```lean
import Statements
import Supplements.Kernels.MainTheoremsAll

theorem riemannHypothesis : RiemannHypothesis := rhOfAll

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi

theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
```

### Target proposition definitions referenced by `src/Main.lean`

- `RiemannHypothesis` (Mathlib, `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185-186`):
  ```lean
  def RiemannHypothesis : Prop :=
    ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
  ```
- `src/Statements.lean:3-16`:
  ```lean
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
  (Note: `RiemannZetaZerosOnLine = RiemannHypothesis` holds by `rfl`; verified with `leanc.sh` on `~/rh-audit/agents3/work/O/VerifyLastSteps.lean`.)

### Import chain from `MainTheoremsAll` to `MainTheorems`

- `src/Supplements/Kernels/MainTheoremsAll.lean:1-2`:
  ```lean
  import Supplements.Kernels.MainTheoremsCritical
  import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.CorGKOf
  ```
- `src/Supplements/Kernels/MainTheoremsCritical.lean:1-4`:
  ```lean
  import Supplements.Kernels.MainTheorems
  import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.ClassNumberThree
  import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.LenEqZeroIff
  import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.OnePoint
  ```

### `allChi`, `rhOfAll`, `critAll`, `claimAll` (`src/Supplements/Kernels/MainTheorems.lean:1-16`)

```lean
import Formalism.GammaFactorNonvanishing.CritLine
import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
import Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion

open Complex DirichletCharacter

theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter

theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi

theorem critAll (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) : s.re = 1 / 2 :=
  Formalism.VW.critLine allChi N χ hχ s h0 h1 hz

theorem claimAll : Claim.HalfPlane ∧ Claim.Strip ∧ Claim.Zeta :=
  ⟨allChi, Claim.strip allChi, Claim.zeta allChi⟩
```

### Declarations directly referenced by `allChi`, `rhOfAll`, `critAll`, `claimAll`

- `UpperTheory.EveryCharacter` (`src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:13-14`):
  ```lean
  def UpperTheory.EveryCharacter : Prop :=
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
  ```
- `UpperTheory.FinalTheorems.everyCharacter` (`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:10-11`):
  ```lean
  theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=
    UpperTheory.FinalTheorems.everyCharacter_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  ```
- `Formalism.VW.rh_of_every` (`src/Formalism/GammaFactorNonvanishing/CritLine.lean:29-32`):
  ```lean
  theorem Formalism.VW.rh_of_every (h : UpperTheory.EveryCharacter) : RiemannHypothesis :=
    Formalism.VW.rh_of_right fun s hs hs1 => by
      have := h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
      rwa [LFunction_modOne_eq] at this
  ```
- `Formalism.VW.critLine` (`src/Formalism/GammaFactorNonvanishing/CritLine.lean:11-12`):
  ```lean
  theorem Formalism.VW.critLine (h : UpperTheory.EveryCharacter) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ)
      (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) : s.re = 1 / 2 := by
  ```
- `Claim.HalfPlane`, `Claim.Strip`, `Claim.Zeta` (`src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean:3-10`):
  ```lean
  def Claim.HalfPlane : Prop :=
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

  def Claim.Strip : Prop :=
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

  def Claim.Zeta : Prop :=
    ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2
  ```
- `Claim.strip` and `Claim.zeta` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:59, 75, 102`):
  ```lean
  theorem strip (h : HalfPlane) : Strip := by
  ...
  theorem zeta (h : HalfPlane) : Zeta := by
  ...
  theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl
  ```

---

## 2. Turning All-Characters Non-Vanishing into `RiemannHypothesis` (`Formalism.VW.rh_of_every` and `Formalism.VW.rh_of_right`)

### Full statement and proof of `Formalism.VW.rh_of_every` (`src/Formalism/GammaFactorNonvanishing/CritLine.lean:29-32`)

```lean
theorem Formalism.VW.rh_of_every (h : UpperTheory.EveryCharacter) : RiemannHypothesis :=
  Formalism.VW.rh_of_right fun s hs hs1 => by
    have := h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
    rwa [LFunction_modOne_eq] at this
```

### Full statement and proof of `Formalism.VW.rh_of_right` (`src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:1-62`)

```lean
import Mathlib

open Complex

theorem Formalism.VW.rh_of_right (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by
  unfold RiemannHypothesis
  intro s hs htriv hs1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hs
      norm_num at hs
    have ht : 1 / 2 < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have h1 : (1 - s) ≠ 1 := by
      intro h
      apply hs0
      linear_combination -h
    have hnat : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
      intro n h
      have hr := congrArg Complex.re h
      rw [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hr
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have key := riemannZeta_one_sub hnat h1
    rw [sub_sub_cancel, hs] at key
    have hz' := hz (1 - s) ht h1
    have h2pi : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.2 (Or.inl (mul_ne_zero two_ne_zero hpi)))
    have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) ≠ 0 := by
      rw [Ne, Complex.cos_eq_zero_iff]
      rintro ⟨k, hk⟩
      have h3 : ((1 - s) - (2 * (k : ℂ) + 1)) * (Real.pi : ℂ) = 0 := by
        linear_combination 2 * hk
      rcases mul_eq_zero.1 h3 with h | h
      · have hsk : s = -2 * (k : ℂ) := by linear_combination -h
        have hre : s.re = -2 * (k : ℝ) := by
          rw [hsk, Complex.mul_re]
          simp
        rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
        · have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
          linarith
        · apply hs0
          rw [hsk, hk0]
          simp
        · apply htriv
          refine ⟨(k - 1).toNat, ?_⟩
          have hnk : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
          have h' : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
            have := congrArg (fun m : ℤ => (m : ℂ)) hnk
            push_cast at this
            exact this
          rw [hsk, h']
          ring
      · exact hpi h
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero h2pi hG) hcos) hz') key.symm
  · exact heq
  · exact absurd hs (hz s hgt hs1)
```

### Assessment and Mathlib lemmas used

This proof is genuine mathematics on Mathlib objects and does **not** assume its conclusion `RiemannHypothesis`: it deduces `RiemannHypothesis` from non-vanishing of `DirichletCharacter.LFunction` on `{s : ℂ | 1 / 2 < s.re}` (excluding `(χ = 1, s = 1)`). Specifically:

1. `rh_of_every` specializes `h : UpperTheory.EveryCharacter` to `N = 1`, `χ = 1`, and rewrites via Mathlib's `DirichletCharacter.LFunction_modOne_eq` (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:67-68`: `LFunction χ = riemannZeta` for `χ : DirichletCharacter ℂ 1`).
2. `rh_of_right` handles `1 / 2 < s.re` directly by `hz` (which already covers `Re s ≥ 1` with `s ≠ 1`, so `riemannZeta_ne_zero_of_one_le_re` is not needed here, though `Claim.zeta` in `ClaimStrip.lean:75-100` uses it together with `completedRiemannZeta_one_sub` and `riemannZeta_def_of_ne_zero`), `s.re = 1 / 2` trivially, and `s.re < 1 / 2` via the functional equation `riemannZeta_one_sub` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:178-179`), excluding `s = 0` via `riemannZeta_zero` (`RiemannZeta.lean:151`, `ζ(0) = -1/2`), proving non-vanishing of the archimedean prefactors with `Real.pi_ne_zero`, `Complex.cpow_ne_zero_iff`, `Complex.Gamma_ne_zero_of_re_pos`, and `Complex.cos_eq_zero_iff` (the zeros of `cos(π(1-s)/2)` with `s.re < 1/2` and `s ≠ 0` are precisely the trivial zeros `s = -2(n+1)` excluded by `htriv`). Other Mathlib/core lemmas used: `lt_trichotomy`, `Complex.sub_re`, `Complex.one_re`, `Complex.neg_re`, `Complex.natCast_re`, `Complex.mul_re`, `Nat.cast_nonneg`, `sub_sub_cancel`, `mul_ne_zero`, `two_ne_zero`, `mul_eq_zero`, `Int.toNat_of_nonneg`, `absurd`.

### Independent compiler verification

Copied verbatim into `~/rh-audit/agents3/work/O/VerifyLastSteps.lean` and elaborated with Lean 4.33.1 against official Mathlib:
- Command: `~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/O/VerifyLastSteps.lean`
- Output (exit 0):
  ```
  'Formalism.VW.rh_of_right' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Formalism.VW.rh_of_every' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Formalism.VW.critLine' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
- Similarly, `Claim.strip` and `Claim.zeta` (verbatim from `ClaimStrip.lean`) were elaborated via `~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/O/VerifyClaimStrip.lean` (exit 0), depending only on `[propext, Classical.choice, Quot.sound]`.

---

## 3. Definition and Unfolding of `UpperTheory.EveryCharacter`

### Quoted definition (`src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:1-14`)

```lean
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ShapeOf
import Development.AutomorphicArithmetic.CharacterBoxes.ShapeWin
import Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi
import Development.AutomorphicArithmetic.CharacterBoxes.Imprimitive

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc
...
def UpperTheory.EveryCharacter : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
```

### Unfolding release-defined identifiers

**There are zero release-defined identifiers inside the body of `UpperTheory.EveryCharacter`.** Every symbol (`ℕ`, `NeZero`, `DirichletCharacter`, `ℂ`, `1 / 2`, `<`, `Complex.re`, `≠`, `1`, `∨`, `DirichletCharacter.LFunction`, `0`) is a Lean core or Mathlib identifier:

- `DirichletCharacter` is Mathlib's `abbrev DirichletCharacter (R : Type*) [CommMonoidWithZero R] (n : ℕ) := MulChar (ZMod n) R` (`Mathlib/NumberTheory/DirichletCharacter/Basic.lean:40`).
- `DirichletCharacter.LFunction` is Mathlib's `noncomputable def LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := ZMod.LFunction χ s` (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:61`).
- Searching the entire declaration-head index `~/rh-audit/index/decls.txt` (1.06M lines) via Python regex for any `def`/`abbrev`/`structure`/`class`/`inductive`/`opaque`/`axiom` redefining `RiemannHypothesis`, `riemannZeta`, `DirichletCharacter`, or `LFunction` returned only two unrelated `LFunction` defs (`src/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean:363` and `src/GroundTheory/AutomorphicForms/GL2/GJLocalZeta.lean:431`) and zero redefinitions of `RiemannHypothesis`, `riemannZeta`, `DirichletCharacter`, or `DirichletCharacter.LFunction`.
- `UpperTheory.EveryCharacter` is definitionally identical (`rfl`) to `DirichletLNonvanishingRightOfHalf` (`src/Statements.lean:6-8`) and `Claim.HalfPlane` (`src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean:3-4`).

For completeness, its immediate internal predecessor in the proof chain is `Formalism.HC.ZeroFreeAll`, lifted to `UpperTheory.EveryCharacter` by `UpperTheory.Top.imprimitive` (`src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:5-35`, using Mathlib's `DirichletCharacter.LFunction_changeLevel`). Unfolding `ZeroFreeAll` to Mathlib identifiers:
- `def ZeroFreeAll : Prop := ZeroFreeOn fun _ => True` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:18`)
- `def ZeroFreeOn (Q : PChar → Prop) : Prop := ∀ ψ : PChar, Q ψ → ψ.ZeroFreeAbove (1 / 2)` (same file, line 14)
- `def PChar.ZeroFreeAbove (ψ : PChar) (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0` (same file, lines 11-12)
- `structure PChar where N : ℕ; [ne : NeZero N]; χ : DirichletCharacter ℂ N; prim : χ.IsPrimitive` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean:7-11`).

Thus `UpperTheory.EveryCharacter` is a genuine statement about Mathlib's `DirichletCharacter.LFunction`, not `True` and not stated about release-defined stand-ins.

---

## 4. `UpperTheory.FinalTheorems.everyCharacter`, Its Call Chain, Vacuous Objects, and Binders

### Level 0: `UpperTheory.FinalTheorems.everyCharacter` (`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7-11`)

```lean
theorem UpperTheory.FinalTheorems.everyCharacter_of_row (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) : UpperTheory.EveryCharacter :=
  UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩ (UpperTheory.One.vwin_of_row h)

theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=
  UpperTheory.FinalTheorems.everyCharacter_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
```

It applies `everyCharacter_of_row` to `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter : UpperTheory.GalStar.Row0b recT` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`), whose type `Row0b` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:69-73`) asserts existence of compatible `l`-adic Galois representations for regular algebraic polarized cuspidal automorphic representations over CM fields.

### Level 1: `everyCharacter_of_row` (`MainConclusion.lean:7-8`)

Applies `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` to two arguments:
1. `⟨h, UpperTheory.Zero.LLC.recTExists, h⟩ : UpperTheory.LiteratureTheorems.OpenLiteratureStatements` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215-218`), packaging `Row` (twice) and `RecTExists` (local Langlands correspondence existence, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/RecTExists.lean:77-79`, proved at `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20-66`).
2. `UpperTheory.One.vwin_of_row h : UpperTheory.Top.VWin` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4-5`), where `VWin : Prop := ∀ ψ : PChar, VWinAt ψ 401` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:44-49`) is a substantive statement bounding Galois-cohomology `shaLen` sums over cyclotomic fields.

### Level 2: `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` (`EveryCharacterOfLiteratureOfVWin.lean:810-813`)

```lean
theorem UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) (hV : UpperTheory.Top.VWin) : UpperTheory.EveryCharacter :=
  _root_.UpperTheory.Lit.every_character_of_theta_integrals_local_matching (_root_.UpperTheory.LiteratureTheorems.published_results_eigen O) (_root_.UpperTheory.LiteratureTheorems.published_results_first O) (_root_.UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature O).1 (_root_.UpperTheory.LiteratureTheorems.theta_integrals_agree_and_local_matching_of_literature O).2
    (_root_.SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt (_root_.UpperTheory.LiteratureTheorems.resolution_char_zero_of_literature O) ... (_root_.UpperTheory.LiteratureTheorems.grothendieck_deformation_of_literature O))
    (_root_.UpperTheory.LiteratureTheorems.local_langlands_gl_recT_exists_of_literature O) hV
```

It applies `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` to 7 arguments:
1. `published_results_eigen O : GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses` (60-field `Prop` structure at `ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean:22-82`; 59 fields are named mathematical propositions, while field `siegelEisensteinSimplePole : GlobalTheory.Published.UnusedSlot72` is `True` by `abbrev GlobalTheory.Published.UnusedSlot72 : Prop := True` at `LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:7`, proved by `trivial` at `EveryCharacterOfLiteratureOfVWin.lean:505-506`).
2. `published_results_first O : GlobalTheory.FunPr.ThetaLocalInputs` (53-field `Prop` structure at `LocalTypeDictionary/BernsteinUnitaryProductIrreducible.lean:6-60`).
3. `(theta_integrals_agree_and_local_matching_of_literature O).1 : ThetaIntegralsAgree` (`Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:585-592`).
4. `(theta_integrals_agree_and_local_matching_of_literature O).2 : LocalMatching` (`WeilTensorModels.lean:581-583`).
5. `topCovolSlim2_use_alt_alt ... : GlobalTheory.CovTop.CovolumeBoundOfX` (`ThirdPlaceSeries/LiftLambdaBound.lean:60-61`).
6. `local_langlands_gl_recT_exists_of_literature O : UpperTheory.Zero.LLC.RecTExists`.
7. `hV : UpperTheory.Top.VWin`.

### Level 3: `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (`ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69-73`)

```lean
theorem every_character_of_theta_integrals_local_matching (P : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses) (F : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hX : _root_.GlobalTheory.CovTop.CovolumeBoundOfX) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hV : VWin) :
    UpperTheory.EveryCharacter :=
  _root_.UpperTheory.Top.every_character_of_green_v_win (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) hV
    (_root_.UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound P F hA hM hX hL fun cDep => _root_.UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep))
```

This splits into two branches:
- **Consumer branch (`ThirdPlaceSeries/TopPlug.lean:12-18`)**:
  ```lean
  theorem UpperTheory.Top.zero_free_all_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
      (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) : Formalism.HC.ZeroFreeAll :=
    h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
      (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (_root_.UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h) fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)
  theorem UpperTheory.Top.every_character_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
      (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) : UpperTheory.EveryCharacter :=
    UpperTheory.Top.imprimitive (_root_.UpperTheory.Top.zero_free_all_of_green_v_win hG hV h)
  ```
  Its substantive theorem arguments are `hG : GlobalTheory.GLq.Green` (`Definitions/NonGaloisDescent/LabelDatum.lean:108-112`, Green's parameterization of cuspidal characters of `GL_d(𝔽_g)`), `hV : VWin`, `shape_closed_link_n_of_green hG`, `zeroFreeAll_of_topG`, `supplyChi`, and `imprimitive`. It also passes `trivial trivial` for the two unused `Prop` slots `V := True`, `NR := True` in `TopShapeAlt True True ...`.
- **Producer branch (`SiegelEisensteinSecondTermHypotheses.lean:44-68`)**: `nonempty_hyps_definite_side_of_closed_bound` constructs `Nonempty (HypsAlt S0.NL DefiniteSideCondition)` (a bundle of family class `𝒜`, raw bundle selection `σ`, and ~40 analytic/algebraic hypotheses, `ThirdPlaceSeries/Hyps.lean:22-90`).

### Where the "vacuous" objects criticised by Nielsen appear on this active route

1. **Geometry predicate equal to `True`**:
   - `def anyGeometry : GeoP := fun _ _ _ => True` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean:19`), wrapped in `geoCl anyGeometry` (`NotGeoClFalse.lean:21-26`), and `def SExt.none : SExt := fun _ _ _ _ _ _ _ _ _ _ _ => PUnit` (`ThetaChr.lean:22`).
   - Passed directly inside `SiegelEisensteinSecondTermHypotheses.lean:59-67`, `Prm1.lean:20-21` (`parametersOfDependence`), `HypothesesNonemptyOfUnramifiedExponents.lean:41-52`, `MemberBundlesLargeUnramifiedExponents.lean:34-63`, and `ExistsBaseLatticeOfPrime.lean:36-72`.
   - Used to discharge `OAt.geo : Γ ...` by `trivial` in `divEx_prov` (`Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:204-209`: `theorem divEx_prov (𝒮 : Slots) (hOx : 𝒮.Ox = OX anyGeometry) : DivEx 𝒮 := ... exact ⟨⟨trivial, ...⟩⟩`), lifted to `geoCl anyGeometry` by `divEx_geoCl` (`PublishedInputsImplyConclusion.lean:39-49`), which is called at `ThirdPlaceSeries/MemberEClosing.lean:21, 24` inside `exists_baseLattice_of_pair_alt` (`ExistsBaseLatticeOfPrime.lean:53`).
2. **Degenerate geometric models (`vol := 0`, intersection/height defined to equal target formula)**:
   - Inside `divEx_prov` → `exists_divT` (`TupPinsOfMuIsW.lean:178-192`) → `geoOver_stages` (`TupPinsOfMuIsW.lean:155-166`), the proof builds `divXFl` and `famFlJ` from `src/Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean`:
     - `geoDegenerate` (`Inhabited.lean:241-306`): `vol := fun _ _ => 0` (line 271), `arTop := fun _ _ => 0` (line 293), `arVol := fun _ _ => 0` (line 294), `nef := fun _ _ => True` (line 262), `big := fun _ _ => True` (line 263), and `inter := fun N v => if h : 0 < dimFl Tau N then flagDegZ Tau N (v ⟨0, h⟩) else flagDegZ Tau N 0` (line 261) — defining `inter` directly to be the target polynomial `flagDegZ`.
     - `padDegenerate` (`Inhabited.lean:352-388`): `Xg := PUnit`, `DivG := fun _ => PUnit`, `Pt := PUnit`, `arDeg := fun _ _ => 0`, `arMix := fun _ _ _ => 0`, `degM := fun _ _ _ _ _ => 0`.
     - `algDegenerate` (`Inhabited.lean:390-402`): `degA := fun _ L => ((geoDegenerate ...).inter N (fun _ => L) : ℝ)`, `semipos := fun _ => True`, `nefFib := fun _ => True`.
     - `shimUFl` (`Inhabited.lean:404-409`) and `divXFl` (`Inhabited.lean:829-861`) assemble these; `mumfordU_fl` (`Inhabited.lean:411-416`) proves `MumfordU (shimUFl ...)` from `geoFl_inter` (`Inhabited.lean:308-318`), which holds because `geoDegenerate.inter` was defined to be `flagDegZ`.
3. **Unused `True` slots**: `GlobalTheory.Published.UnusedSlot72 := True` (`DiscreteSpectrumResidualClassification.lean:7`, passed as `trivial` at `EveryCharacterOfLiteratureOfVWin.lean:505-506`), and `V = NR = True` in `TopShapeAlt True True ...` (`TopPlug.lean:15`, `TopShape.lean:33`).

### Are the consumers of the vacuous objects stated for ONE specific bundle or universally?

**Every consumer along this route is stated universally (for all predicates `Γ : GeoP`, all `S : SExt`, all `𝒮 : Slots`, all `p : Parameters hL`, and all `HypsAlt` / family classes `𝒜` / bundle selections `selB`)** — only the *producers* instantiate those universal slots with `anyGeometry`, `SExt.none`, and `divXFl` to witness `Nonempty (HypsAlt ...)`. Quoted binders of the consumers:

- `GlobalTheory.T.exists_member_of_construction_steps_secondPass` (`ExistsMemberOfConstructionStepsSecondPassStatement.lean:12`, consumes `divEx_geoCl`):
  ```lean
  ... → ∀ 𝒮 𝒮' : Slots, StepW Start (Has3 𝒮) → ... → DivEx 𝒮 → ... → MemberE 𝒮
  ```
- `GlobalTheory.Glob.open_and_linked_of_stronger_extension_alt` (`ThirdPlaceSeries/OpenAndLinkedOfStrongerExtension.lean:28`):
  ```lean
  ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), ...
  ```
- `GlobalTheory.Fc.StageOne.rowFun_at_gridA_alt` (`ThirdPlaceSeries/RowFunAtGridA.lean:32`):
  ```lean
  ... → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), ...
  ```
- `GlobalTheory.Glob.CovolRow.linked_bundles_l3_of_open_alt` (`ThirdPlaceSeries/LinkedBundlesL3OfOpen.lean:31`):
  ```lean
  ... → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), ...
  ```
- `GlobalTheory.Fc.AllAtMemberStage0.allRows_of_open0_alt` (`ThirdPlaceSeries/LinkROfIsLinked.lean:50`):
  ```lean
  ... → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (NN : FamClass → Prop), ...
  ```
- `GlobalTheory.Fc.nonempty_hyps_of_allRows_alt` (`ThirdPlaceSeries/NonemptyHypsOfAllRows.lean:19`) and `UpperTheory.Top.classSel` (`CharacterBoxes/ClassSel.lean:14`):
  ```lean
  ... → ∀ (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) (N : FamClass → Prop) (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType), ... → Nonempty (_root_.GlobalTheory.Fc.HypsAlt N DR)
  ```
- `GlobalTheory.Fc.forall_goal_of_shape_of_hyps` (`ThirdPlaceSeries/ShapeOf.lean:31`):
  ```lean
  ∀ (V NR : Prop) (N : FamClass → Prop) (G : Prop), _root_.GlobalTheory.Fc.TopShapeAlt V NR N G → V → NR → _root_.GlobalTheory.Fc.HypsAlt N _root_.GlobalTheory.Fc.DefiniteSideCondition → G
  ```
- `GlobalTheory.Fc.TopShapeAlt` (`ThirdPlaceSeries/TopShapeAlt.lean:24-35, 98-99`, returned by `UpperTheory.Top.shape_closed_link_n_of_green` at `TopShape.lean:33`):
  ```lean
  def TopShapeAlt (V NR : Prop) (N : FamClass → Prop) (G : Prop) : Prop :=
    ∀ (𝒜 : FamClass) (cT : ℝ → ℝ → ℝ) (hEx : MinkDiv → UpperTheory.Top.ExS 𝒜 cT)
      (sel : _root_.Formalism.L2.TwistSelection 𝒜) (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm)
      ... (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC) ...
      (hG : ∀ D, GenusMassVolumes.GenusMassAt D 2), G
  ```
- `UpperTheory.Top.zero_free_all_of_green_v_win` (`ThirdPlaceSeries/TopPlug.lean:12-15`) eliminates `Nonempty (HypsAlt ...)` via `h.elim` into `forall_goal_of_shape_of_hyps`, so **any** `HypsAlt` (regardless of how `OAt` or `DivX` was constructed) yields `TopG`, then `ZeroFreeAll` via `zeroFreeAll_of_topG` (`CharacterBoxes/ZeroFreeAllOfTopG.lean:26-34`) → `zeroFreeOn_of_tiedWin_cyc` (`TopWin.lean:90-93`) → `formB` (`PrimitiveCosets/Imports.lean:8-19`) → `Deduction.zeroFree_of_rpow_window` (`ZeroFreeOfRpowWindow.lean:11-14`) → `Deduction.lemmaL` (`lemmaL.lean:13-22`) → `Deduction.landau_window` (`landauWindow.lean:83-166`).

---

## 5. Any Undischarged RH or Critical-Strip Non-Vanishing Hypothesis on This Route?

**None found within the depth examined.**

- Every declaration on the route that has `UpperTheory.EveryCharacter`, `Claim.HalfPlane`, `ZeroFreeAll`, or `∀ s, 1 / 2 < s.re → ... → riemannZeta s ≠ 0` as a hypothesis (`rh_of_every`, `rh_of_right`, `critLine`, `Claim.strip`, `Claim.zeta`, `imprimitive`) has that hypothesis discharged by a closed theorem (`allChi := UpperTheory.FinalTheorems.everyCharacter`, `zero_free_all_of_green_v_win`, etc.).
- Beyond `imprimitive`, the hypotheses of `zero_free_all_of_green_v_win`, `zeroFreeAll_of_topG`, `zeroFreeOn_of_tiedWin_cyc`, `level_of_tiedWin`, `formB`, `zeroFree_of_rpow_window`, `lemmaL`, and `landau_window` are upper bounds on Chebyshev/Mellin sums `Λ.Gm x ≤ x ^ θ` on windows, analytic pole data (`PoleData`, proved at `DedekindLFunctions/LandauTheorems/poleData.lean:248-400`), and Mathlib's classical non-vanishing on `1 ≤ s.re` (`CharFamilyLFunctionNeZeroOfOneLeRe.lean:9-20` using `riemannZeta_ne_zero_of_one_le_re` and `DirichletCharacter.LFunction_ne_zero_of_one_le_re`). None of these assumes non-vanishing in `0 < s.re < 1`.
- In `EveryCharacterOfLiteratureOfVWin.lean` and `SiegelEisensteinSecondTermHypotheses.lean`, the hypotheses are automorphic, Galois-representation, representation-theoretic, and Arakelov-height packages (all discharged by closed declarations in the same route); the only L-function non-vanishing field noticed in `ThetaLocalInputs` (`LocalTypeDictionary/BernsteinUnitaryProductIrreducible.lean:35`) is `HeckeLEntireAndNonzeroAtOne` (at `s = 1`, not in the open critical strip).
- Across the entire 1.06M-line declaration-head index (`~/rh-audit/index/decls.txt`), `RiemannHypothesis` appears in only 9 declaration heads: `Main.lean:4`, `MainTheorems.lean:9`, `RhOfRight.lean:5`, `CritLine.lean:29`, `MainConclusion.lean:13`, `RiemannHypothesisOfEveryCharacter.lean:215`, `ClaimStrip.lean:102`, `ZetaRealNonvanish.lean:74`, and `Challenge.lean:19` (a `sorry` template not imported by `Main.lean`).

---

## 6. Conclusion

In the release, `RiemannHypothesis` is **not** handed back from a hypothesis as in Nielsen's `claimed_rh`: `Main.lean:4` is a closed theorem derived by genuine Mathlib analysis (`rh_of_every`/`rh_of_right`) from `UpperTheory.EveryCharacter` on Mathlib's `DirichletCharacter.LFunction`.
The vacuous objects Nielsen highlights (`anyGeometry := fun _ _ _ => True`, `SExt.none`, and degenerate models `geoDegenerate`/`divXFl` with `vol := 0`, `inter := flagDegZ`) **do** appear on the active route producing `Nonempty (HypsAlt ...)`.
However, every consumer examined along this route is universally quantified over all predicates, slots, and bundles—so modus ponens permits any valid witness, unlike `NielsenMinimal.lean` where the witness is conjoined with an assumed `hRH`.
Because the ~175k-file release is not compiled here, circularity, vacuity, `sorry`, custom axioms, or an inconsistency (`False`) could still hide inside the uninspected upstream proofs (`galoisLocalGlobalStrong_recParameter`, `vwin_of_row`, `topCovolSlim2_use_alt_alt`, `shape_closed_link_n_of_green`, `nonempty_hyps_of_allRows_alt`, and the literature bundles).

---

## Summary Table

| Item | Release object / location | Finding |
|---|---|---|
| Entry point | `src/Main.lean:4-12`, `MainTheorems.lean:7-16` | Closed theorems; no `RiemannHypothesis` hypothesis |
| Final RH step | `CritLine.lean:29-32`, `RhOfRight.lean:5-62` | Genuine Mathlib proof (`LFunction_modOne_eq`, `riemannZeta_one_sub`); `leanc.sh` verified |
| `EveryCharacter` | `EveryCharacter.lean:13-14` | Pure Mathlib statement on `DirichletCharacter.LFunction`; zero release stand-ins |
| Chain head | `MainConclusion.lean:7-11`, `EveryCharacterOfLiteratureOfVWin.lean:810-813` | Applies literature/automorphic/height theorems + `VWin` to get `EveryCharacter` |
| Vacuous objects | `OverIx.lean:19`, `ThetaChr.lean:22`, `Inhabited.lean:241-416,829-861` | Present on active route (`anyGeometry := True`, `SExt.none`, `geoDegenerate`/`divXFl`, `UnusedSlot72`) |
| Consumer binders | `OpenAndLinkedOfStrongerExtension.lean:28`, `LinkROfIsLinked.lean:50`, `ShapeOf.lean:31`, `TopShapeAlt.lean:24-99` | Universal (`∀ Γ : GeoP`, `∀ S : SExt`, `∀ 𝒮 : Slots`, `∀ 𝒜 ... selB`, `HypsAlt → G`) |
| Strip non-vanishing hyps | Route examined + `decls.txt` scan | None undischarged found; `RiemannHypothesis` only in 9 decl heads (all wrappers / `Challenge.lean`) |
| Comparison to Nielsen | `NielsenMinimal.lean:35-38` vs `TopPlug.lean:12-18` | Vacuous witnesses exist, but conclusion is NOT passed in as an argument |

---

## What I Could Not Verify

1. **Full compilation and axiom audit of `Main.lean` — NOT VERIFIED**: Per the task material, the ~175k-file release is not built and cannot be imported into `leanc.sh`. Therefore I could not run `#print axioms riemannHypothesis` on the release's `Main.lean` to rule out `sorry`, custom axioms, `implemented_by`, `native_decide`, or elaboration failures anywhere in the transitive import graph. (My scan of `decls.txt` found 0 `axiom` lines, but `decls.txt` is a prebuilt index of declaration heads and may not list `axiom` declarations, `sorry` inside proof bodies, or metaprogramming hacks.)
2. **Leaves of the upstream mathematical proofs — NOT VERIFIED**: Beyond the inspected layers around `Main.lean`, `CritLine.lean`, `RhOfRight.lean`, `ClaimStrip.lean`, `Imprimitive.lean`, `TopPlug.lean`, `ZeroFreeAllOfTopG.lean`, `TopWin.lean`, `landauWindow.lean`, `poleData.lean`, `SiegelEisensteinSecondTermHypotheses.lean`, `EveryCharacterOfLiteratureOfVWin.lean`, `HypothesesNonemptyOfUnramifiedExponents.lean`, `MemberBundlesLargeUnramifiedExponents.lean`, `ExistsBaseLatticeOfPrime.lean`, `MemberEClosing.lean`, `PublishedInputsImplyConclusion.lean`, `TupPinsOfMuIsW.lean`, and `Inhabited.lean`, I did not inspect the proofs of `galoisLocalGlobalStrong_recParameter`, `vwin_of_row`, `topCovolSlim2_use_alt_alt`, `published_results_eigen`/`published_results_first`, `shape_closed_link_n_of_green`'s sub-lemmas, `classSel`, or `open_orbit_of_unramified_exponents_alt`'s sub-lemmas. I therefore cannot verify whether those upstream branches are mathematically sound, free of subtle vacuity/contradiction (`False`), or free of `sorry`.
3. **Why `divXFl` / `anyGeometry` suffice inside `nonempty_hyps_of_allRows_alt` and `TopShapeAlt` — NOT VERIFIED**: While the consumer binders are demonstrably universal, tracing every field of `HypsAlt` (45 fields in `ThirdPlaceSeries/Hyps.lean:22-90`) to verify whether `divXFl`'s degenerate fields (`vol := 0`, `arDeg := 0`, etc.) are genuinely irrelevant to the analytic bound in `TopShapeAlt` or whether some intermediate invariant is vacuously satisfied/contradictory was outside the depth examined.
