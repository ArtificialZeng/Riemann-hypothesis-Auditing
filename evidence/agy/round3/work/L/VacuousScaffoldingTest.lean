/-!
Minimal self-contained Lean 4 file (no Mathlib imports; only standard Lean axioms `[propext, Quot.sound]`,
no `sorry`, no custom axioms, not even `Classical.choice`) demonstrating that containing vacuous
definitions (`fun _ => True`) and `rfl`-proved equations—even inside the proof term itself—is NOT
sufficient to make a closed proof "prove nothing".
-/

namespace VacuousScaffolding

-- Exact vacuous ingredients from NielsenMinimal.lean:
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

-- Standard, non-vacuous arithmetic predicate: primality on `Nat`.
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

private def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

private theorem fact_pos : ∀ n : Nat, 0 < fact n
  | 0 => Nat.zero_lt_one
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

private theorem dvd_fact {k n : Nat} (hk0 : 0 < k) (hkn : k ≤ n) : k ∣ fact n := by
  induction n with
  | zero => omega
  | succ m ih =>
    if h : k = m + 1 then
      subst h; exact ⟨fact m, rfl⟩
    else
      exact Nat.dvd_trans (ih (by omega)) (Nat.dvd_mul_left (fact m) (m + 1))

private theorem exists_prime_dvd : ∀ m : Nat, 2 ≤ m → ∃ p : Nat, IsPrime p ∧ p ∣ m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm
    -- Constructive bounded search for a proper divisor `2 ≤ d < m` of `m`:
    have aux : ∀ k : Nat, (∃ d : Nat, 2 ≤ d ∧ d < k ∧ d ∣ m) ∨ (∀ d : Nat, 2 ≤ d → d < k → ¬(d ∣ m)) := by
      intro k
      induction k with
      | zero => exact Or.inr (fun _ _ h => absurd h (Nat.not_lt_zero _))
      | succ j ihj =>
        rcases ihj with h | h
        · rcases h with ⟨d, h1, h2, h3⟩
          exact Or.inl ⟨d, h1, Nat.lt_succ_of_lt h2, h3⟩
        · if hj2 : 2 ≤ j then
            if hdj : j ∣ m then
              exact Or.inl ⟨j, hj2, Nat.lt_succ_self j, hdj⟩
            else
              exact Or.inr (fun d hd2 hdlt => by
                if hdj' : d = j then
                  subst hdj'; exact hdj
                else
                  exact h d hd2 (by omega))
          else
            exact Or.inr (fun d hd2 hdlt => h d hd2 (by omega))
    rcases aux m with ⟨d, hd2, hdlt, hdm⟩ | hno
    · rcases ih d hdlt hd2 with ⟨p, hpp, hpd⟩
      exact ⟨p, hpp, Nat.dvd_trans hpd hdm⟩
    · refine ⟨m, ⟨hm, fun d hd => ?_⟩, Nat.dvd_refl m⟩
      if hd0 : d = 0 then
        subst hd0
        rcases hd with ⟨q, hq⟩
        omega
      else if hd1 : d = 1 then
        exact Or.inl hd1
      else if hdm : d = m then
        exact Or.inr hdm
      else
        have hle : d ≤ m := Nat.le_of_dvd (by omega) hd
        exact False.elim (hno d (by omega) (by omega) hd)

/--
A genuinely non-trivial theorem (Euclid's theorem: infinitely many primes), whose proof term
explicitly invokes the vacuous `buildBundle` and `valid_bundle_of_manufactured` and a `True`
side-condition parameter, yet whose conclusion is completely non-vacuous and uses only
standard Lean axioms `[propext, Quot.sound]` (no `sorry`, no custom axioms, no `Classical.choice`).
-/
theorem euclid_with_vacuous_scaffolding (n : Nat) : ∃ p : Nat, n < p ∧ IsPrime p := by
  -- Vacuous scaffolding present inside the proof term (as in NielsenMinimal.lean):
  let b : Bundle := buildBundle
  have hvac : anyGeometry 0 ∧ b.model.height = targetFormula :=
    valid_bundle_of_manufactured b
  -- Use a lemma taking a vacuous `True` hypothesis (like `TopShape True True`):
  have helper : anyGeometry 0 → b.model.height = targetFormula →
      ∃ p : Nat, n < p ∧ IsPrime p := by
    intro _ _
    have hm : 2 ≤ fact n + 1 := Nat.succ_le_succ (fact_pos n)
    rcases exists_prime_dvd (fact n + 1) hm with ⟨p, hp, hpd⟩
    refine ⟨p, ?_, hp⟩
    if hgt : n < p then
      exact hgt
    else
      exfalso
      have hle : p ≤ n := by omega
      have hp0 : 0 < p := by have := hp.1; omega
      have hpf : p ∣ fact n := dvd_fact hp0 hle
      have hp1 : p ∣ 1 := (Nat.dvd_add_right hpf).mp hpd
      have hple1 : p ≤ 1 := Nat.le_of_dvd Nat.zero_lt_one hp1
      have := hp.1
      omega
  exact helper hvac.1 hvac.2

end VacuousScaffolding

#check @VacuousScaffolding.euclid_with_vacuous_scaffolding
#print axioms VacuousScaffolding.euclid_with_vacuous_scaffolding
