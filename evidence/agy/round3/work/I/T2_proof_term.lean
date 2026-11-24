import Mathlib.NumberTheory.LSeries.RiemannZeta

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

#print claimed_rh

set_option pp.explicit true in
#print claimed_rh

example (hRH : RiemannHypothesis) : (claimed_rh hRH).2 = hRH := rfl

-- Proof-irrelevance caveat in Lean: for ANY Prop and ANY two proofs, h1 = h2 holds by rfl.
example (P : Prop) (h1 h2 : P) : h1 = h2 := rfl

-- Non-Prop analogue (where proof irrelevance does not apply) showing the second field is literally x:
def claimed_type {α : Type} (x : α) :
    PProd (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) α :=
  let b := buildBundle
  ⟨⟨b, valid_bundle_of_manufactured b⟩, x⟩

example {α : Type} (x : α) : (claimed_type x).2 = x := rfl
example : (claimed_type true).2 ≠ false := by decide
