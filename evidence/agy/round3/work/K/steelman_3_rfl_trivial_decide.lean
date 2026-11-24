import Mathlib.NumberTheory.LSeries.RiemannZeta

-- Steelman Attempt 3: Keep all vacuous ingredients and attempt to prove
-- `RiemannHypothesis` directly via `rfl`, `trivial`, `decide`, or from the
-- reflexivity tautology `RiemannHypothesis = RiemannHypothesis`.

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

theorem rh_eq_rh : RiemannHypothesis = RiemannHypothesis := rfl

theorem claimed_rh_rfl : RiemannHypothesis := by
  rfl

theorem claimed_rh_trivial : RiemannHypothesis := by
  trivial

theorem claimed_rh_decide : RiemannHypothesis := by
  decide

theorem claimed_rh_from_taut : RiemannHypothesis :=
  rh_eq_rh.mp trivial
