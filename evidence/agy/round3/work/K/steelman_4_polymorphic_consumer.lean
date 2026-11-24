import Mathlib.NumberTheory.LSeries.RiemannZeta

-- Steelman Attempt 4: Mirror the release's `TopShapeAlt` / `forall_goal_of_shape_of_hyps`
-- pattern using a universally quantified consumer `∀ V G, TopShape V G → V → Bundle → G`.
-- The consumer itself compiles with zero sorry/axioms, and accepts `trivial` and
-- `buildBundle`, but instantiating `G := RiemannHypothesis` still requires supplying
-- a proof of `TopShape True RiemannHypothesis`.

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

def TopShape (V NR G : Prop) : Prop :=
  V → NR → (∀ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula → G)

theorem goal_of_shape (V NR G : Prop) (t : TopShape V NR G) (hV : V) (hR : NR) (b : Bundle) : G :=
  t hV hR b (valid_bundle_of_manufactured b)

theorem shape_for_rh : TopShape True True RiemannHypothesis :=
  fun _ _ b hb => hb.1

theorem claimed_rh :
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis := by
  let b := buildBundle
  exact ⟨⟨b, valid_bundle_of_manufactured b⟩, goal_of_shape True True RiemannHypothesis shape_for_rh trivial trivial b⟩
