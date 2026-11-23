/-!
# Toy model of the pattern criticised by Nielsen

A proof development with a "geometry" slot `Γ` that downstream lemmas carry around
but never inspect.  We show:

1. instantiating the slot with the always-true predicate yields a perfectly valid,
   axiom-free, hypothesis-free theorem (Part A);
2. it is *not* a free lunch: as soon as a consumer really needs the content of the
   slot, the `True` instantiation makes the consumer's side condition unprovable
   (Part B);
3. what genuine "reward hacking" looks like in Lean, and how each form is detected
   (Part C).
-/

namespace Toy

/-! ## Part A — the pattern in the Riemann-hypothesis repository -/

/-- The type of "geometry predicates" (cf. `GeoP`). -/
abbrev GeoP : Type := Nat → Prop

/-- A demanding predicate (cf. `geoOf`). -/
def geoOf : GeoP := fun n => ∃ c, 0 < c ∧ n = c * c

/-- The trivial predicate (cf. `anyGeometry`). -/
def anyGeometry : GeoP := fun _ => True

/-- Closure of a predicate under a step (cf. `GeoCl`); never eliminated below. -/
inductive GeoCl (Γ : GeoP) : Nat → Prop
  | base {n : Nat} : Γ n → GeoCl Γ n
  | step {n : Nat} : GeoCl Γ n → GeoCl Γ (n + 1)

/-- A certified point: a `geo` certificate plus a field that is really used (cf. `OAt`). -/
structure OAt (Γ : GeoP) (n : Nat) : Prop where
  geo : Γ n
  lam : n % 2 = 0

/-- The hypothesis bundle handed to the final theorem.  Note: it does not mention `Γ`
(cf. `HypsAlt`). -/
structure Hyps : Prop where
  even : ∃ n, 10 < n ∧ n % 2 = 0

/-- Consumer lemma, proved uniformly in `Γ` (cf. `open_and_linked_of_stronger_extension_alt`,
`linkedAt_geometricWeakTies_of_tie`, …).  It never looks inside `geo`. -/
theorem hyps_of_point (Γ : GeoP) (n : Nat) (hn : 10 < n) (o : OAt Γ n) : Hyps :=
  ⟨n, hn, o.lam⟩

/-- Producer: with `Γ := anyGeometry` the `geo` field is filled by `trivial`
(cf. `divEx_prov`: `exact ⟨⟨trivial, lamAre_heq …⟩⟩`). -/
theorem point_exists : OAt anyGeometry 12 := ⟨trivial, rfl⟩

/-- The final theorem's statement is fixed in advance and mentions none of the above. -/
def Target : Prop := ∃ n : Nat, 10 < n ∧ n % 2 = 0

theorem plug (h : Hyps) : Target := h.even

/-- Closed, hypothesis-free, and its proof term runs through `anyGeometry`. -/
theorem target : Target := plug (hyps_of_point anyGeometry 12 (by decide) point_exists)

#print axioms target   -- expected: does not depend on any axioms

/-! ## Part B — no free lunch -/

/-- A consumer that really needs the geometric content must *eliminate* it, and then it
needs a side condition tying `Γ` to the conclusion. -/
theorem consumer (Γ : GeoP) (hΓ : ∀ n, Γ n → 0 < n) (n : Nat) (g : Γ n) : 0 < n := hΓ n g

/-- For the trivial predicate that side condition is simply false, so the "hack" gains
nothing: the burden moves from the producer to the consumer. -/
theorem trivial_predicate_fails_consumer : ¬ (∀ n, anyGeometry n → 0 < n) :=
  fun h => absurd (h 0 trivial) (by decide)

/-- For the demanding predicate it is provable. -/
theorem geoOf_pos : ∀ n, geoOf n → 0 < n := by
  intro n ⟨c, hc, hn⟩
  subst hn
  exact Nat.mul_pos hc hc

/-! ## Part C — what real reward hacking looks like -/

/-- (C1) An extra axiom.  Typechecks, but `#print axioms` exposes it. -/
axiom cheat : ∀ n : Nat, n = 0

theorem bad₁ : (1 : Nat) = 0 := cheat 1
#print axioms bad₁     -- expected: [Toy.cheat]

/-- (C2) A hypothesis left in the *final* statement: vacuously true, proves nothing. -/
theorem bad₂ (h : ∀ n : Nat, n = 0) : (1 : Nat) = 0 := h 1

/-- (C3) Changing the target: proving a home-made "RH" instead of the real one. -/
def MyTarget : Prop := True
theorem bad₃ : MyTarget := trivial

end Toy
