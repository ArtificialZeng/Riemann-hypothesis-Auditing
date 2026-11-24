import Mathlib.NumberTheory.Real.Irrational

-- Converse experiment: pass the exact vacuous bundle from NielsenMinimal.lean
-- (True predicate, vol := 0, height := 42, h_eq := rfl) together with two `trivial`
-- shape inputs into a consumer stated for ALL bundles whose conclusion is a
-- non-trivial Mathlib theorem (`Irrational (Real.sqrt 2)`), proved independently
-- of the vacuous bundle.

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

-- Consumer stated for ALL bundles (and two `True` shape inputs), mirroring the
-- polymorphic consumer pattern `forall_goal_of_shape_of_hyps`.
theorem consumer_all_bundles (b : Bundle)
    (_hvalid : anyGeometry 0 ∧ b.model.height = targetFormula)
    (_hShape1 : True) (_hShape2 : True) :
    Irrational (Real.sqrt 2) :=
  irrational_sqrt_two

-- Hypothesis-free final theorem passing the vacuous bundle to the consumer:
theorem sqrt_two_irrational_via_vacuous_bundle : Irrational (Real.sqrt 2) := by
  let b := buildBundle
  exact consumer_all_bundles b (valid_bundle_of_manufactured b) trivial trivial

theorem conj_sqrt_two_irrational :
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ Irrational (Real.sqrt 2) := by
  let b := buildBundle
  exact ⟨⟨b, valid_bundle_of_manufactured b⟩,
    consumer_all_bundles b (valid_bundle_of_manufactured b) trivial trivial⟩

#print sqrt_two_irrational_via_vacuous_bundle
#print axioms sqrt_two_irrational_via_vacuous_bundle
#print axioms conj_sqrt_two_irrational
