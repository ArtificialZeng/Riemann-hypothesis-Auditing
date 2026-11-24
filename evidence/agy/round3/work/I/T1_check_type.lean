import Mathlib.NumberTheory.LSeries.RiemannZeta

-- Minimal Mathlib example with zero `sorry` and no custom axioms:
-- `anyGeometry` is `True`, `height` is assigned `targetFormula`, and `h_eq` is `rfl`.
-- No `sorry` or custom axiom appears anywhere.

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

-- The "geometric comparison" theorem: proves that the bundle's height matches
-- `targetFormula` and is valid, with zero `sorry` and no custom axioms.
private lemma valid_bundle_of_manufactured (b : Bundle) :
    anyGeometry 0 ∧ b.model.height = targetFormula :=
  ⟨b.geoOk, b.model.h_eq⟩

-- Downstream step: if `RiemannHypothesis` is combined with the bundle's
-- geometric certificate, the certificate adds zero independent evidence.
theorem claimed_rh (hRH : RiemannHypothesis) :
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis := by
  let b := buildBundle
  exact ⟨⟨b, valid_bundle_of_manufactured b⟩, hRH⟩

#print axioms claimed_rh
#check @claimed_rh
