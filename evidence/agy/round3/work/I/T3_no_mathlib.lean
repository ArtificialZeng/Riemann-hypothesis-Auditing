-- Same example with NO imports at all (replacing Mathlib's `lemma` keyword with core `theorem`),
-- for arbitrary P : Prop and for False.

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

private theorem valid_bundle_of_manufactured (b : Bundle) :
    anyGeometry 0 ∧ b.model.height = targetFormula :=
  ⟨b.geoOk, b.model.h_eq⟩

theorem claimed_P (P : Prop) (hP : P) :
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ P := by
  let b := buildBundle
  exact ⟨⟨b, valid_bundle_of_manufactured b⟩, hP⟩

theorem claimed_false (hF : False) :
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ False := by
  let b := buildBundle
  exact ⟨⟨b, valid_bundle_of_manufactured b⟩, hF⟩

#check @claimed_P
#print axioms claimed_P
#check @claimed_false
#print axioms claimed_false
