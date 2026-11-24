import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
Part 1. The example posted by J. L. Nielsen on X on 24 November 2026
(https://x.com/QualiaQuanta/status/2125008805310222352), reproduced with its indentation
restored (the post shows it flush left) and otherwise unchanged. See `NielsenMinimal.lean`.
-/

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

/-!
Part 2. What the example states, and what it would take to turn it into the
statement that the release proves.
-/

-- (a) the statement of the example: an implication whose hypothesis is RH
#check @claimed_rh

-- (b) the proof term: the RH conjunct is the hypothesis `hRH`, handed back unchanged.
--     (An equation `(claimed_rh hRH).2 = hRH := rfl` would prove nothing here: any two proofs
--     of a proposition are definitionally equal. Printing the term is the honest check.
--     This correction is due to the independent review by Gemini 4 Neon, agent I.)
#print claimed_rh

-- (c) the example is not specific to RH: the same text proves `P → (… ∧ P)` for every `P`
theorem claimed_anything (P : Prop) (hP : P) :
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ P :=
  ⟨⟨buildBundle, valid_bundle_of_manufactured buildBundle⟩, hP⟩

example (h : False) :
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ False :=
  claimed_anything False h

-- (d) the statement checked for the release has no hypothesis:
--     `theorem riemannHypothesis : RiemannHypothesis`.
--     The example does not yield a term of that type; the next line must fail.
theorem rh_from_example : RiemannHypothesis := (claimed_rh _).2
