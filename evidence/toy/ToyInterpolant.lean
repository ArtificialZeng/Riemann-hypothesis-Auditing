/-!
# Toy model 2: an "assigned" intermediate quantity

A squeeze argument proves `A ≤ C` by exhibiting some `h` with `A ≤ h` and `h ≤ C`.
Nothing in the logic asks where `h` came from.  Below, `h` is *defined* by a formula, the
equation "height = formula" holds by `rfl` because the slot was just assigned, and the
conclusion is still a closed theorem that uses no axioms beyond Lean's standard ones.

This mirrors, in a dozen lines, the pattern that Nielsen's paper calls "assigned, not derived":
`setDiv` overwrites the height slot, `h_eq := fun _ => rfl`, and two inequalities are then proved
about the installed formula.
-/
namespace Toy2

/-- A record with a "height" slot, like the release's divisor datum. -/
structure Datum where
  h : Nat → Int

/-- The explicit formula. -/
def formula (u : Nat) : Int := 2 * u + 1

/-- Overwrite the height slot (the analogue of `setDiv`). -/
def setH (D : Datum) (f : Nat → Int) : Datum := { D with h := f }

/-- "height = formula" holds by `rfl`. -/
theorem h_eq (D : Datum) (u : Nat) : (setH D formula).h u = formula u := rfl

/-- The two quantities the argument really wants to compare. -/
def pairing (u : Nat) : Int := u
def mainTerm (u : Nat) : Int := 3 * u + 5

/-- Lower bound: a genuine (here: easy) inequality about the formula.  Not `le_refl`. -/
theorem lower (u : Nat) : pairing u ≤ formula u := by unfold pairing formula; omega

/-- Upper bound: another genuine inequality about the formula. -/
theorem upper (u : Nat) : formula u ≤ mainTerm u := by unfold formula mainTerm; omega

/-- A generic consumer, stated for ANY datum whose height satisfies the two bounds. -/
theorem squeeze (D : Datum) (u : Nat) (h1 : pairing u ≤ D.h u) (h2 : D.h u ≤ mainTerm u) :
    pairing u ≤ mainTerm u := Int.le_trans h1 h2

/-- The closed conclusion.  The height has cancelled; it never had to be "geometric". -/
theorem target (u : Nat) : pairing u ≤ mainTerm u :=
  squeeze (setH ⟨fun _ => 0⟩ formula) u (by rw [h_eq]; exact lower u) (by rw [h_eq]; exact upper u)

#print axioms target

/-- What does NOT work: installing a value without proving the bounds.  Before the overwrite the
slot is `0`, and for that value the lower bound is simply false, so no proof term exists. -/
theorem zero_height_fails : ¬ (∀ u : Nat, pairing u ≤ (⟨fun _ => 0⟩ : Datum).h u) := fun h => by
  have h1 := h 1
  simp only [pairing] at h1
  omega

#print axioms zero_height_fails

/-- "Remove" versus "replace".  Deleting an argument of `squeeze` leaves an ill-typed term; that
is true of every argument of every theorem and says nothing about soundness.  REPLACING the datum
by any other datum whose height equals the formula leaves a valid proof: -/
theorem target' (D : Datum) (hD : ∀ u, D.h u = formula u) (u : Nat) : pairing u ≤ mainTerm u :=
  squeeze D u (by rw [hD u]; exact lower u) (by rw [hD u]; exact upper u)

#print axioms target'

end Toy2
