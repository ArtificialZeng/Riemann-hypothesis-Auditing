# Task I: What the Posted Example States and Proves

All Lean elaborations below were run using Lean 4.33.1 via `~/rh-audit/agents3/leanc.sh` (which passes `~/rh-audit/tools/lean-4.33.1-darwin_aarch64/bin/lean` with `LEAN_PATH` pointing to the official Mathlib v4.33.1 build under `~/rh-audit/challenge-rebuild/.lake/packages`). Scratch test files were placed strictly in `~/rh-audit/agents3/work/I/`.

---

## 1. Elaboration of the Example and Exact Type of `claimed_rh`

### Whitespace relationship between `posted_verbatim.txt` and `NielsenMinimal.lean`

Command:
```sh
diff -u -w ~/rh-audit/agents3/input/posted_verbatim.txt ~/rh-audit/agents3/input/NielsenMinimal.lean && echo "(no non-whitespace diff)"
```
Output (exit code `0`):
```text
(no non-whitespace diff)
```

Elaborating the flush-left verbatim text directly fails to parse due to indentation:
```sh
~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/input/posted_verbatim.txt 2>&1
```
Output (exit code `1`):
```text
~/rh-audit/agents3/input/posted_verbatim.txt:21:18: error: unexpected identifier; expected '}'
~/rh-audit/agents3/input/posted_verbatim.txt:36:86: error: unsolved goals
hRH : RiemannHypothesis
⊢ (∃ b, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis
~/rh-audit/agents3/input/posted_verbatim.txt:37:0: error: unexpected token 'let'; expected command
'claimed_rh' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

### Elaboration of `NielsenMinimal.lean`

Command:
```sh
~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/input/NielsenMinimal.lean 2>&1
```
Exact output (exit code `0`):
```text
'claimed_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
```
There are no errors, no warnings, no `sorryAx`, and no custom axioms (only Lean's three standard axioms `propext`, `Classical.choice`, and `Quot.sound`).

### Exact type of `claimed_rh`

A copy of `NielsenMinimal.lean` was saved to `~/rh-audit/agents3/work/I/T1_check_type.lean` with line 41 appended:
```lean
#check @claimed_rh
```

Command:
```sh
~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/I/T1_check_type.lean 2>&1
```
Exact output (exit code `0`):
```text
'claimed_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
claimed_rh : RiemannHypothesis → (∃ b, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis
```

### Does the type of `claimed_rh` have hypotheses? Which?

**Yes.** The type of `claimed_rh` is an implication with **one explicit hypothesis**:
- `(hRH : RiemannHypothesis)` (`~/rh-audit/agents3/input/NielsenMinimal.lean:35`: `theorem claimed_rh (hRH : RiemannHypothesis) :`).

Here `RiemannHypothesis` is Mathlib's proposition from `~/rh-audit/challenge-rebuild/.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185-186` (imported at `NielsenMinimal.lean:1`: `import Mathlib.NumberTheory.LSeries.RiemannZeta`):
```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```
Thus `claimed_rh` does not state `RiemannHypothesis`; it states the conditional implication `RiemannHypothesis → (∃ b, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis`.

---

## 2. Provenance of the `RiemannHypothesis` Conjunct Inside the Proof Term

In `~/rh-audit/agents3/input/NielsenMinimal.lean:35-38`:
```lean
theorem claimed_rh (hRH : RiemannHypothesis) :
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis := by
  let b := buildBundle
  exact ⟨⟨b, valid_bundle_of_manufactured b⟩, hRH⟩
```

### Kernel proof term and elaboration tests

In `~/rh-audit/agents3/work/I/T2_proof_term.lean`, `#print claimed_rh` (line 32), `set_option pp.explicit true in #print claimed_rh` (lines 34–35), and definitional-equality checks (lines 37–49) were elaborated:
```lean
example (hRH : RiemannHypothesis) : (claimed_rh hRH).2 = hRH := rfl
example (P : Prop) (h1 h2 : P) : h1 = h2 := rfl
def claimed_type {α : Type} (x : α) :
    PProd (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) α :=
  let b := buildBundle
  ⟨⟨b, valid_bundle_of_manufactured b⟩, x⟩
example {α : Type} (x : α) : (claimed_type x).2 = x := rfl
example : (claimed_type true).2 ≠ false := by decide
```

Command:
```sh
~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/I/T2_proof_term.lean 2>&1
```
Exact output (exit code `0`):
```lean
theorem claimed_rh : RiemannHypothesis → (∃ b, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis :=
fun hRH =>
  let b := buildBundle;
  ⟨Exists.intro b (valid_bundle_of_manufactured b), hRH⟩
theorem claimed_rh : RiemannHypothesis →
  And
    (∃ b,
      And (anyGeometry (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Eq Nat b.model.height targetFormula))
    RiemannHypothesis :=
fun hRH =>
  let b := buildBundle;
  @And.intro
    (∃ b,
      And (anyGeometry (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Eq Nat b.model.height targetFormula))
    RiemannHypothesis
    (@Exists.intro Bundle
      (fun b =>
        And (anyGeometry (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Eq Nat b.model.height targetFormula))
      b (valid_bundle_of_manufactured b))
    hRH
```

### Answer and Lean proof-irrelevance caveat

- Inside the elaborated proof term, the conjunct `RiemannHypothesis` comes **solely and verbatim from the bound hypothesis `hRH`**, passed directly as the fourth (second proof) argument to `@And.intro`.
- `buildBundle` and `valid_bundle_of_manufactured b` appear **only** in the left conjunct (`@Exists.intro Bundle ... b (valid_bundle_of_manufactured b)`). No lemma from Mathlib is invoked anywhere in the proof term.
- `(claimed_rh hRH).2 = hRH := rfl` elaborates with exit code `0` (`T2_proof_term.lean:37`). However, because `RiemannHypothesis : Prop` (`RiemannZeta.lean:185`), Lean's definitional proof irrelevance makes `h1 = h2 := rfl` hold for *any* two proofs of *any* proposition (`T2_proof_term.lean:40`, exit code `0`), so `rfl` on a `Prop` equality does not by itself rule out an independent derivation.
- Two additional checks confirm the provenance beyond proof irrelevance:
  1. The explicit term printed by `set_option pp.explicit true in #print claimed_rh` directly displays `hRH` as the right proof argument of `@And.intro`, and the non-`Prop` analogue `claimed_type` (`T2_proof_term.lean:43-49`, where proof irrelevance does not apply) returns its argument `x` verbatim (`(claimed_type x).2 = x := rfl` and `(claimed_type true).2 ≠ false`).
  2. Removing `hRH` and leaving the second conjunct as a placeholder (`T2_no_hRH_fail.lean:28-31`: `exact ⟨⟨b, valid_bundle_of_manufactured b⟩, _⟩`) fails to elaborate:

Command:
```sh
~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/I/T2_no_hRH_fail.lean 2>&1
```
Exact output (exit code `1`):
```text
~/rh-audit/agents3/work/I/T2_no_hRH_fail.lean:31:46: error: don't know how to synthesize placeholder for argument `right`
context:
b : Bundle := buildBundle
⊢ RiemannHypothesis
~/rh-audit/agents3/work/I/T2_no_hRH_fail.lean:29:90: error: unsolved goals
b : Bundle := buildBundle
⊢ (∃ b, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis
```

---

## 3. Specificity to the Riemann Hypothesis (`P : Prop` and `False`)

The example is **not** specific to `RiemannHypothesis`.

### Test A: Arbitrary `P : Prop` (keeping the Mathlib import)

In `~/rh-audit/agents3/work/I/T3_arbitrary_P.lean`, the entire text of `NielsenMinimal.lean` was kept identical except for adding `variable (P : Prop)` before `claimed_rh`, replacing `RiemannHypothesis` with `P` in `claimed_rh`, and appending `#check @claimed_rh` and `#print axioms claimed_rh`.

Command:
```sh
~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/I/T3_arbitrary_P.lean 2>&1
```
Exact output (exit code `0`):
```text
claimed_rh : ∀ (P : Prop), P → (∃ b, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ P
'claimed_rh' does not depend on any axioms
```

### Test B: `False` (keeping the Mathlib import)

In `~/rh-audit/agents3/work/I/T3_false.lean`, the entire text of `NielsenMinimal.lean` was kept identical except for replacing `RiemannHypothesis` with `False` in `claimed_rh` and appending `#check @claimed_rh` and `#print axioms claimed_rh`.

Command:
```sh
~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/I/T3_false.lean 2>&1
```
Exact output (exit code `0`):
```text
claimed_rh : False → (∃ b, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ False
'claimed_rh' does not depend on any axioms
```

### Test C: Removing `import Mathlib.NumberTheory.LSeries.RiemannZeta`

- With `import Mathlib.NumberTheory.LSeries.RiemannZeta` removed and `private lemma` kept unchanged, elaboration fails at `T3_no_mathlib.lean:23:7` (`error: unexpected identifier; expected ... 'theorem'`) only because the `lemma` keyword is provided by Mathlib/Batteries rather than core Lean 4.
- Replacing `private lemma` with core Lean's `private theorem` (`~/rh-audit/agents3/work/I/T3_no_mathlib.lean`), both `claimed_P` and `claimed_false` elaborate with **no imports at all**:

Command:
```sh
~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/I/T3_no_mathlib.lean 2>&1
```
Exact output (exit code `0`):
```text
claimed_P : ∀ (P : Prop), P → (∃ b, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ P
'claimed_P' does not depend on any axioms
claimed_false : False → (∃ b, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ False
'claimed_false' does not depend on any axioms
```

Notice that both `T3_arbitrary_P.lean` and `T3_false.lean` report `'claimed_rh' does not depend on any axioms`. The axioms `[propext, Classical.choice, Quot.sound]` reported for the original `claimed_rh` in `NielsenMinimal.lean` come exclusively from the definition of `RiemannHypothesis` (via `riemannZeta`) appearing in the theorem's *type*, not from anything in the proof.

---

## 4. Attempting to Obtain an Unconditional Term of Type `RiemannHypothesis`

**No.** As it stands, `NielsenMinimal.lean` does not yield a term of type `RiemannHypothesis` with no hypothesis; any attempt to project `(claimed_rh _).2` still demands a proof of `RiemannHypothesis` as input.

In `~/rh-audit/agents3/work/I/T4_no_hyp.lean` (exact copy of `NielsenMinimal.lean` plus line 42):
```lean
theorem t : RiemannHypothesis := (claimed_rh _).2
```

Command:
```sh
~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/I/T4_no_hyp.lean 2>&1
```
Exact output (exit code `1`):
```text
'claimed_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
~/rh-audit/agents3/work/I/T4_no_hyp.lean:42:45: error: don't know how to synthesize placeholder for argument `hRH`
context:
⊢ RiemannHypothesis
```

---

## 5. Inspection of `~/rh-audit/src/omega/src/Main.lean` and Side-by-Side Type Comparison

### Full contents of `~/rh-audit/src/omega/src/Main.lean`

`~/rh-audit/src/omega/src/Main.lean:1-12` (entire file verbatim):
```lean
import Statements
import Supplements.Kernels.MainTheoremsAll

theorem riemannHypothesis : RiemannHypothesis := rhOfAll

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi

theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
```

### Hypotheses check for every theorem in `Main.lean`

`Main.lean` contains **no** `variable`, `section`, `include`, `open`, `open ... in`, `omit`, `namespace`, or `universe` declarations (lines 1–2 are solely `import` statements; lines 4, 6, 8, 10, 12 are the five theorems). In Lean 4, `variable`, `section`, `include`, `open`, and `omit` are file-local and do not cross `import` boundaries.

Every theorem in `Main.lean` has **zero** explicit binders and **zero** file-local implicit hypotheses:

1. `Main.lean:4`: `theorem riemannHypothesis : RiemannHypothesis := rhOfAll` — no explicit binders, no file-local implicit hypotheses.
2. `Main.lean:6`: `theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll` — no explicit binders, no file-local implicit hypotheses.
3. `Main.lean:8`: `theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi` — no explicit binders, no file-local implicit hypotheses.
4. `Main.lean:10`: `theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1` — no explicit binders, no file-local implicit hypotheses.
5. `Main.lean:12`: `theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll` — no explicit binders, no file-local implicit hypotheses.

### Verification of the referenced proposition definitions in source

- **Toolchain:** `~/rh-audit/src/omega/lean-toolchain:1` is `leanprover/lean4:v4.33.1`.
- **`RiemannHypothesis`:** Repository-wide search `cd ~/rh-audit/src/omega && git grep -n -w -F 'RiemannHypothesis' -- src/` (exit code `0`) returned 40 lines across `src/`, none of which defines, shadows, or introduces syntax/notation for `RiemannHypothesis`. `Main.lean:1` imports `Statements`, whose line 1 (`~/rh-audit/src/omega/src/Statements.lean:1`) is `import Mathlib`; `~/rh-audit/challenge-rebuild/.lake/packages/mathlib/Mathlib.lean:5812` is `public import Mathlib.NumberTheory.LSeries.RiemannZeta`; and `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185-186` defines:
  ```lean
  def RiemannHypothesis : Prop :=
    ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
  ```
  Elaborating `~/rh-audit/agents3/work/I/T5_check_rh_type.lean` (`#check @RiemannHypothesis` and `#print RiemannHypothesis`, exit code `0`) confirms:
  ```lean
  RiemannHypothesis : Prop
  def RiemannHypothesis : Prop :=
  ∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n, s = -2 * (↑n + 1)) → s ≠ 1 → s.re = 1 / 2
  ```
- **The other four proposition names:** Defined in `~/rh-audit/src/omega/src/Statements.lean:3-16` (each of type `Prop` with no free parameters; `git grep` across `src/` shows they appear only in `Statements.lean`, `Main.lean`, and `Challenge.lean`, and `Main.lean` does not import `Challenge.lean`):
  - `Statements.lean:3-4`: `def RiemannZetaZerosOnLine : Prop := ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2`
  - `Statements.lean:6-8`: `def DirichletLNonvanishingRightOfHalf : Prop := ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0`
  - `Statements.lean:10-12`: `def DirichletLZerosOnLine : Prop := ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2`
  - `Statements.lean:14-16`: `def PrimitiveDirichletLZerosOnLine : Prop := ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2`
- **Important scope note:** Because `~/rh-audit/src/omega` is not built, `Main.lean` itself was **NOT VERIFIED** by Lean elaboration (see "What I could not verify").

### Is the type of `riemannHypothesis` the same as the type of `claimed_rh`?

**No.** The two types are not equal and not logically equivalent: `riemannHypothesis` has an unconditional statement of type `RiemannHypothesis`, whereas `claimed_rh` has a conditional implication type assuming `RiemannHypothesis` as a hypothesis and returning a conjunction with an existential over `Bundle`.

### Side-by-side comparison of the two types

| Release `riemannHypothesis` (`~/rh-audit/src/omega/src/Main.lean:4`, source-level) | Example `claimed_rh` (`~/rh-audit/agents3/input/NielsenMinimal.lean:35-36`, `#check @claimed_rh`) |
|---|---|
| `RiemannHypothesis` | `RiemannHypothesis → (∃ b, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis` |

---

## 6. Deleting the Bundle Entirely

Two scratch files deleted all bundle definitions (`anyGeometry`, `targetFormula`, `DegenerateModel`, `Bundle`, `buildBundle`, `valid_bundle_of_manufactured`):

1. `~/rh-audit/agents3/work/I/T6_minimal.lean`:
   ```lean
   import Mathlib.NumberTheory.LSeries.RiemannZeta

   theorem t (hRH : RiemannHypothesis) : RiemannHypothesis := hRH
   ```
   Command: `~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/I/T6_minimal.lean 2>&1`
   Output: *(empty)*, exit code `0`.

2. `~/rh-audit/agents3/work/I/T6_no_bundle.lean` (adding `#check @t` and `#print axioms t`):
   Command: `~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/I/T6_no_bundle.lean 2>&1`
   Exact output (exit code `0`):
   ```text
   t : RiemannHypothesis → RiemannHypothesis
   't' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

### What this shows

- Deleting the entire bundle still compiles cleanly and produces the exact same `#print axioms` list (`[propext, Classical.choice, Quot.sound]`).
- Therefore, none of the bundle definitions (`anyGeometry`, `targetFormula`, `DegenerateModel`, `Bundle`, `buildBundle`, `valid_bundle_of_manufactured`) contributes to establishing `RiemannHypothesis`. The bundle only supplies the left conjunct `(∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula)`, while the **sole** ingredient carrying the `RiemannHypothesis` conclusion is the assumed hypothesis `(hRH : RiemannHypothesis)` returned unchanged (`fun hRH => hRH`).

---

## 7. Conclusion

- **Demonstrates:** In Lean 4, a file with zero `sorry` and no custom axioms can construct trivial structures (`True` predicates, `rfl` equalities) and conjoin a certificate about them with an assumed hypothesis `(hRH : P)` for any `P : Prop`—including `RiemannHypothesis` or `False`.
- **Demonstrates:** Seeing `#print axioms` report only `[propext, Classical.choice, Quot.sound]` does not distinguish an unconditional proof from a trivial implication `P → (certificate ∧ P)` whose proof ignores the certificate when returning `P`.
- **Does NOT demonstrate:** It does not show how a theorem whose statement is `RiemannHypothesis` *with no hypothesis* can compile without `sorry` or custom axioms, nor can `claimed_rh` yield a closed term of type `RiemannHypothesis` (`(claimed_rh _).2` fails to elaborate).
- Deleting the bundle leaves `theorem t (hRH : RiemannHypothesis) : RiemannHypothesis := hRH`, confirming the hypothesis `hRH`—not the degenerate bundle—carries the `RiemannHypothesis` conclusion.
- In `~/rh-audit/src/omega/src/Main.lean:4`, `theorem riemannHypothesis : RiemannHypothesis := rhOfAll` has no explicit or file-local implicit hypotheses and no bundle conjunct, so its statement type differs fundamentally from `claimed_rh`.
- Consequently, the compilation mechanism exhibited by Nielsen's example (`P → ... ∧ P`) does not explain how an unconditional `: RiemannHypothesis` declaration compiles; whether `Main.lean` itself compiles or is sound is separate and NOT VERIFIED here.

---

## Summary Table

| Item | Question | Verified Result | Key Evidence |
|---|---|---|---|
| 1 | `NielsenMinimal.lean` compiles? Type of `claimed_rh`? | Exit `0`; type has explicit hypothesis `hRH : RiemannHypothesis` | `leanc.sh` on `NielsenMinimal.lean`, `T1_check_type.lean` |
| 2 | Provenance of `RiemannHypothesis` conjunct? | Directly from hypothesis `hRH` (not bundle or Mathlib) | `#print claimed_rh` (`pp.explicit`), `T2_proof_term.lean`, `T2_no_hRH_fail.lean` |
| 3 | Specific to `RiemannHypothesis`? | No; compiles for arbitrary `P : Prop` and `False` (0 axioms) | `T3_arbitrary_P.lean`, `T3_false.lean`, `T3_no_mathlib.lean` |
| 4 | Yields unconditional `RiemannHypothesis`? | No; `(claimed_rh _).2` fails (exit `1`: cannot synthesize `hRH`) | `T4_no_hyp.lean` |
| 5 | `Main.lean` theorems have hypotheses? Same type? | 0 explicit / file-local implicit hypotheses; types are **not** the same | `Main.lean:1-12`, `Statements.lean:1-16`, `RiemannZeta.lean:185-186`, `git grep` |
| 6 | Compiles with bundle deleted? | Yes (exit `0`, same 3 standard axioms); `hRH` alone carries conclusion | `T6_minimal.lean`, `T6_no_bundle.lean` |
| 7 | Explains unconditional `: RiemannHypothesis`? | No; only shows `P → (trivial ∧ P)` passes `#print axioms` | Items 1–6 |

---

## What I Could Not Verify

1. **Compilation, elaborated types, and axioms of `~/rh-audit/src/omega/src/Main.lean` (NOT VERIFIED):** Because the release under `~/rh-audit/src/omega` is not built and the review environment is strictly read-only outside scratch/report paths, `Main.lean` could not be elaborated with Lean 4.33.1. Consequently, I could not verify by Lean compilation whether `Main.lean` compiles, whether `rhOfAll`, `allChi`, `claimAll.2.1`, and `critAll` have the stated types, whether `Main.lean` or its dependencies use `sorryAx` or custom axioms, or whether any transitive import under `Supplements.Kernels.MainTheoremsAll` defines global syntax/macros/notations that alter elaboration of `Main.lean` (other than confirming by `git grep` across `src/` that `RiemannHypothesis` is never defined in `src/` and that the four `Statements.lean` proposition identifiers appear only in `Statements.lean`, `Challenge.lean`, and `Main.lean`).
2. **Soundness or mathematical content of Alpöge's release proof (NOT VERIFIED):** Auditing the proof chain behind `rhOfAll`, `allChi`, `claimAll`, and `critAll` (about 175k files under `~/rh-audit/src/omega/src`) is outside Task I and was not performed.
3. **External publication details (NOT VERIFIED):** Network access is prohibited; dates, authorship, and any surrounding text of the public posts beyond the local files `posted_verbatim.txt` and `NielsenMinimal.lean` were not independently verified.
