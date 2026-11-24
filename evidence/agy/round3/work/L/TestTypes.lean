import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
Mechanical tests comparing the types in NielsenMinimal.lean against Main.lean / Statements.lean.
-/

namespace NielsenCopy

def anyGeometry : ∀ (_ : Nat), Prop := fun _ => True

def targetFormula : Nat := 42

structure DegenerateModel where
  vol : Nat := 0
  height : Nat
  h_eq : height = targetFormula

structure Bundle where
  geoOk : anyGeometry 0
  model : DegenerateModel

def buildBundle : Bundle :=
  { geoOk := trivial
    model :=
      { vol := 0
        height := 42
        h_eq := rfl } }

private lemma valid_bundle_of_manufactured (b : Bundle) :
    anyGeometry 0 ∧ b.model.height = targetFormula :=
  ⟨b.geoOk, b.model.h_eq⟩

theorem claimed_rh (hRH : RiemannHypothesis) :
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis := by
  let b := buildBundle
  exact ⟨⟨b, valid_bundle_of_manufactured b⟩, hRH⟩

/-- The identical proof term works for ANY proposition `P : Prop`, including `False` or `¬RiemannHypothesis`. -/
theorem claimed_any (P : Prop) (hP : P) :
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ P := by
  let b := buildBundle
  exact ⟨⟨b, valid_bundle_of_manufactured b⟩, hP⟩

theorem claimed_false (hF : False) :
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ False :=
  claimed_any False hF

theorem claimed_not_rh (hNRH : ¬RiemannHypothesis) :
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ ¬RiemannHypothesis :=
  claimed_any (¬RiemannHypothesis) hNRH

/-- Even with `claimed_rh` in scope, deriving `RiemannHypothesis` unconditionally requires a hypothesis;
    `claimed_rh` has implication type `RiemannHypothesis → ...`, not `RiemannHypothesis`. -/
example : (RiemannHypothesis →
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis) :=
  claimed_rh

/-- The bundle witness exists unconditionally, completely independent of `RiemannHypothesis`. -/
theorem bundle_alone : ∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula :=
  ⟨buildBundle, valid_bundle_of_manufactured buildBundle⟩

end NielsenCopy

namespace StatementsCheck

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

/-- Check definitional equality between Mathlib's `RiemannHypothesis` and `RiemannZetaZerosOnLine`. -/
example : RiemannHypothesis = RiemannZetaZerosOnLine := rfl

/-- Check that `RiemannHypothesis` is NOT definitionally equal to `True` (it implies nontrivial consequences,
    and is equivalent to the explicit Mathlib statement). -/
example : RiemannHypothesis ↔
    ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2 :=
  Iff.rfl

end StatementsCheck

#check @NielsenCopy.claimed_rh
#check @NielsenCopy.claimed_false
#check @NielsenCopy.bundle_alone
#print axioms NielsenCopy.claimed_rh
#print axioms NielsenCopy.claimed_any
#print axioms NielsenCopy.claimed_false
#print axioms NielsenCopy.bundle_alone
#print RiemannHypothesis
