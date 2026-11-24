# Independent Logic Review and Mechanical Tests (Review L)

**Subject:** Claim **(C)**: *"The release compiles in the same way as the posted example; therefore the release does not prove the Riemann Hypothesis."*
**Materials reviewed:** `~/rh-audit/agents3/input/posted_verbatim.txt`, `~/rh-audit/agents3/input/NielsenMinimal.lean`, `~/rh-audit/src/omega` (commit `c7d25b3bf`, 175,188 `.lean` files under `src/`), `~/rh-audit/index/decls.txt` (1,061,434 lines), Mathlib `v4.33.1` (`~/rh-audit/challenge-rebuild/.lake/packages/mathlib`), `~/rh-audit/export/challenge.ndjson`, `~/rh-audit/agents3/input/con-leche_compare.stdout.log`, and local Lean `4.33.1` elaborations via `~/rh-audit/agents3/leanc.sh`.

---

## 1. Numbered Conditions Required for (C) to Be a Valid Inference

In `~/rh-audit/agents3/input/NielsenMinimal.lean` (which differs from `~/rh-audit/agents3/input/posted_verbatim.txt` only in leading whitespace; verified in Section 3), the file builds a vacuous predicate and `rfl`-proved structure (`lines 7–31`), and then states:

> `NielsenMinimal.lean:35-38`:
> ```lean
> theorem claimed_rh (hRH : RiemannHypothesis) :
>     (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis := by
>   let b := buildBundle
>   exact ⟨⟨b, valid_bundle_of_manufactured b⟩, hRH⟩
> ```

The example has **two logically distinct components**: (A) vacuous internal ingredients (`True` predicates, `rfl` equations, no `sorry`/custom axioms), and (B) the mechanism by which the `RiemannHypothesis` conclusion is actually produced (`hRH : RiemannHypothesis` is taken as an explicit hypothesis and returned verbatim). For **(C)** to be a valid inference from the example, the following conditions on the release must hold:

### Group A — Conditions about vacuous ingredients (necessary for structural analogy, NOT logically sufficient for "does not prove RH")

1. **Vacuous `True` predicates in the release:** The release defines propositional predicates that reduce definitionally to `True` (such as `fun _ => True` or `: Prop := True`) and discharges obligations with `trivial` (analogous to `NielsenMinimal.lean:7,21`).
2. **Tautological / `rfl`-proved data equations in the release:** The release constructs degenerate structures/models whose fields are assigned directly to target constants so that comparison equations hold by definitional reflexivity `rfl` (analogous to `NielsenMinimal.lean:11-14,20-25`).
3. **Zero `sorry` and standard axioms only (matching the example's axiom profile):** The release compiles without `sorry` and with only Lean's standard axioms `{propext, Quot.sound, Classical.choice}` (analogous to `NielsenMinimal.lean:40` printing `[propext, Classical.choice, Quot.sound]`). *(If the release instead used `sorry` or custom axioms, it would fail to prove RH, but by a different mechanism than the posted example.)*

### Group B — Conditions about where the conclusion `RiemannHypothesis` comes from (logically NECESSARY for "therefore the release does not prove the Riemann Hypothesis")

Because Group A alone cannot derive an unproved closed proposition in a sound kernel (proved formally in Section 4), the inference from the example to "does not prove RH" requires **Condition 4** (the actual mechanism of `claimed_rh`), or else one of the alternative escape hatches **Condition 5** or **Condition 6**:

4. **Headline theorem takes `RiemannHypothesis` (or an equivalent/stronger/contradictory premise) as an undischarged hypothesis (`forallE` type) — the exact mechanism of the posted example:** The release's headline theorem `riemannHypothesis` in `Main.lean` (and its kernel export) does not have bare type `RiemannHypothesis`, but instead has a `forallE` implication type `H → ...` whose premise `H` supplies `RiemannHypothesis` (or an unproved/inconsistent assumption), just as `claimed_rh` has type `RiemannHypothesis → (...) ∧ RiemannHypothesis` (`NielsenMinimal.lean:35-38`).
5. **Alternative conclusion-weakening mechanism (statement substitution/shadowing, NOT exhibited by `NielsenMinimal.lean`):** If Condition 4 is false (the headline theorem is unconditional), then for Group A's vacuous definitions alone to yield a closed term of the headline type without extra axioms or kernel unsoundness, the release must have redefined, shadowed, or weakened `RiemannHypothesis` (or `riemannZeta` / Mathlib's definitions) so that the declared headline type is strictly weaker than—or vacuous relative to—official Mathlib's `RiemannHypothesis`.
6. **Alternative non-example bypass (hidden axiom, `sorryAx`, compiler trust, unsound kernel/checker, or export mismatch, NOT exhibited by `NielsenMinimal.lean`):** If both Conditions 4 and 5 are false, then in a consistent base logic the release can fail to be a proof of official Mathlib's `RiemannHypothesis` only if the proof actually depends on an unpermitted axiom (custom `axiom`, `sorryAx`, `Lean.ofReduceBool`/`Lean.trustCompiler`), exploits a soundness bug in the kernel or external checker (`con-leche`), or does not match the checked export `solution.ndjson`.

**Logical dependency:** Group A (Conditions 1–3) **without** Condition 4 (or Conditions 5–6) cannot validly entail that the release fails to prove the Riemann Hypothesis. Specifically, to infer **(C)** *"in the same way as the posted example"*, **Condition 4** is indispensable.

---

## 2. Mechanical Tests for Each Condition (and Their Scope)

Each test below uses strictly the allowed artefacts: `~/rh-audit/src/omega` (and `~/rh-audit/index/decls.txt`), Mathlib `v4.33.1`, `~/rh-audit/agents3/leanc.sh` on small files, `~/rh-audit/export/challenge.ndjson`, and `~/rh-audit/agents3/input/con-leche_compare.stdout.log`.

| Cond. | Mechanical test design | What the test CAN show | What the test CANNOT show |
|---|---|---|---|
| **1** (`True` predicates) | Search `decls.txt` for `: Prop := True` and `:= fun .*=> True$`; inspect matching source files and trace `trivial` arguments in `Main.lean`'s top-level call chain (`EveryCharacter.lean`, `ShapeWin.lean`, `Imprimitive.lean`, `ExplicitFormulaErrorOfHostConditions.lean`). | Confirms whether literal `True` / `fun _ => True` definitions and `trivial` proofs exist in the source, and inspects their logical polarity (positive conclusion vs negative hypothesis/domain restriction) in read files. | Single-line `decls.txt` grep misses multi-line definitions whose `:= True` is on a following line; reading a subset of the 175,188 files cannot classify every `True` definition across the entire repo or prove which ones lie in the live dependency cone of `Main.lean`. |
| **2** (`rfl` equations) | Count and sample `:= rfl` lines in `decls.txt`, and inspect top-level theorem chains in `Main.lean` / `Supplements/Kernels/`. | Confirms the presence and count of single-line `:= rfl` declarations and distinguishes routine definitional projection lemmas from degenerate constructions in inspected files. | Cannot enumerate multi-line `rfl` proofs or audit all 175,188 files for degenerate intermediate models; crucially, cannot by itself establish vacuity of `Main.lean` (Section 4). |
| **3 & 6** (Axioms, `sorry`, bypasses, checker log) | (a) `git grep` across `omega/src/` for `axiom`, `sorry`, `sorryAx`, `admit`, `unsafe`, `implemented_by`, `native_decide`, `ofReduceBool`, `trustCompiler`, `@[extern`, `addDecl`, `import Challenge`, and grep `decls.txt` for `opaque `; (b) stream-parse `challenge.ndjson` for all `axiom` records and total declaration count; (c) inspect `con-leche_compare.stdout.log`; (d) run `leanc.sh` on `NielsenMinimal.lean` and `TestTypes.lean` (`#print axioms`). | (a) Detects any lexical occurrence of `axiom`/`sorry`/bypass constructs in all 175,188 source files; (b) gives the exact axiom list and declaration count of `challenge.ndjson`; (c) records what `con-leche` printed; (d) confirms exact `#print axioms` output of `claimed_rh` and its variants. | Because `omega` is not built locally and `solution.ndjson` and the `con-leche` binary/source are not audited here: cannot verify that `omega/src` actually elaborates without error into `solution.ndjson`; cannot directly inspect the `axiom` records inside `solution.ndjson` (`con-leche_compare.stdout.log` does not list `solution.ndjson`'s axioms by name); cannot verify `con-leche`'s own soundness or exact `--compare` axiom-checking specification. |
| **4** (Headline type: bare `const` vs `forallE`) | (a) Compare `NielsenMinimal.lean:35-38` against `Main.lean:4-12` and `Challenge.lean:19-27`; (b) compile `TestTypes.lean` with `leanc.sh` to check elaborated types (`#check @claimed_rh`, `claimed_any`, `claimed_false`); (c) stream-parse `challenge.ndjson` to inspect the declaration records and `type` expression records of `riemannHypothesis` and the other four headline theorems; (d) match theorem names against `con-leche_compare.stdout.log`. | Conclusively confirms or refutes whether `claimed_rh` and `Main.lean` / `challenge.ndjson`'s `riemannHypothesis` share the `forallE` hypothesis mechanism: inspecting the kernel NDJSON `type` node directly shows whether it is a bare `const` or a `forallE`. | Does not by itself prove that `solution.ndjson` (not directly inspected) actually inhabits those types without trusting `con-leche_compare.stdout.log` (and does not build `Main.lean` locally). |
| **5** (Statement fidelity / no shadowing) | (a) `diff` `Statements.lean` vs lines 1–16 of `Challenge.lean`; (b) compare Mathlib rev in `omega/lake-manifest.json` against local official Mathlib `v4.33.1`, and Lean commit in `leanc.sh --version` against `challenge.ndjson:1`; (c) grep `omega/src/` for any redefinition of `RiemannHypothesis` or `riemannZeta`; (d) stream-parse `challenge.ndjson` to resolve `RiemannHypothesis` and `riemannZeta` definitions; (e) check `RiemannHypothesis = RiemannZetaZerosOnLine` by `rfl` via `leanc.sh` (`TestTypes.lean`). | Confirms that `Statements.lean`, `Challenge.lean`, `Main.lean`, and `challenge.ndjson` all use official Mathlib `v4.33.1`'s `RiemannHypothesis` and `riemannZeta` without local redefinition or weakening. | Does not audit the internal mathematical correctness of Mathlib's own library definitions of `Complex`, `Real`, `HurwitzZeta.hurwitzZetaEven`, or `DirichletCharacter.LFunction`, and does not directly inspect `solution.ndjson` to verify no name/type mismatch bypassed `con-leche`. |

---

## 3. Executed Mechanical Tests and Results

### 3(i). Type of `claimed_rh` in the Example vs Statement of `riemannHypothesis` in `Main.lean`

1. **Verbatim vs indented example (`diff -u`):**
   - Command: `diff -u ~/rh-audit/agents3/input/posted_verbatim.txt ~/rh-audit/agents3/input/NielsenMinimal.lean`
   - Result: Diffs appear strictly in leading spaces on lines 12–14, 17–18, 21–25, 30–31, 36–38; all tokens are identical.
2. **Elaboration of `NielsenMinimal.lean`:**
   - Command: `~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/input/NielsenMinimal.lean`
   - Output (exit code `0`):
     ```text
     'claimed_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
     ```
3. **Mechanical type inspection via `~/rh-audit/agents3/work/L/TestTypes.lean`:**
   - Command: `~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/L/TestTypes.lean`
   - Output (exit code `0`):
     ```text
     NielsenCopy.claimed_rh : RiemannHypothesis →
       (∃ b, NielsenCopy.anyGeometry 0 ∧ b.model.height = NielsenCopy.targetFormula) ∧ RiemannHypothesis
     NielsenCopy.claimed_false : False →
       (∃ b, NielsenCopy.anyGeometry 0 ∧ b.model.height = NielsenCopy.targetFormula) ∧ False
     NielsenCopy.bundle_alone : ∃ b, NielsenCopy.anyGeometry 0 ∧ b.model.height = NielsenCopy.targetFormula
     'NielsenCopy.claimed_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
     'NielsenCopy.claimed_any' does not depend on any axioms
     'NielsenCopy.claimed_false' does not depend on any axioms
     'NielsenCopy.bundle_alone' does not depend on any axioms
     def RiemannHypothesis : Prop :=
     ∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n, s = -2 * (↑n + 1)) → s ≠ 1 → s.re = 1 / 2
     ```
   - **Finding on `claimed_rh`:** The type of `claimed_rh` is the implication `RiemannHypothesis → (∃ b, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis`. Its identical proof term (`TestTypes.lean:40-47`) proves `∀ P : Prop, P → (∃ b, ...) ∧ P`, including `P = False` (`claimed_false`) and `P = ¬RiemannHypothesis` (`claimed_not_rh`, `TestTypes.lean:49-51`). Moreover, `claimed_any`, `claimed_false`, and `bundle_alone` depend on **no axioms at all**; `claimed_rh` reports `[propext, Classical.choice, Quot.sound]` solely because its *type* mentions Mathlib's `RiemannHypothesis`.
4. **Comparison with `Main.lean`, `Statements.lean`, `Challenge.lean`, and Mathlib `v4.33.1`:**
   - `~/rh-audit/src/omega/src/Main.lean:1-12`:
     ```lean
     import Statements
     import Supplements.Kernels.MainTheoremsAll

     theorem riemannHypothesis : RiemannHypothesis := rhOfAll

     theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll

     theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi

     theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1

     theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
     ```
   - `Main.lean:4` declares `riemannHypothesis` with **no parameters/hypotheses** and type `RiemannHypothesis` (not `RiemannHypothesis → ...` and no bundle conjunct). Its proof body is `rhOfAll`, declared in `~/rh-audit/src/omega/src/Supplements/Kernels/MainTheorems.lean:9` as `theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi`, also with no hypotheses.
   - `Statements.lean:1-16` matches `Challenge.lean:1-16` byte-for-byte:
     - Command: `diff -u ~/rh-audit/src/omega/src/Statements.lean <(head -n 16 ~/rh-audit/src/omega/src/Challenge.lean) && echo "STATEMENTS_MATCH=0"` -> `STATEMENTS_MATCH=0`.
   - Official Mathlib `v4.33.1` (`~/rh-audit/challenge-rebuild/.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean:121,185-186`):
     ```lean
     def riemannZeta := hurwitzZetaEven 0
     def RiemannHypothesis : Prop :=
       ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
     ```
   - `TestTypes.lean:83` (`example : RiemannHypothesis = RiemannZetaZerosOnLine := rfl`) elaborated with exit code `0`, confirming definitional equality between Mathlib's `RiemannHypothesis` and `Statements.lean:3-4`.
   - Version/commit alignment:
     - `~/rh-audit/src/omega/lake-manifest.json:10`: `"rev": "0df444a360eaa60ab8c11dca51a86af692955474"`.
     - Command: `cd ~/rh-audit/challenge-rebuild/.lake/packages/mathlib && git rev-parse HEAD && git describe --tags --always` -> `0df444a360eaa60ab8c11dca51a86af692955474` and `v4.33.1`.
     - Command: `~/rh-audit/agents3/leanc.sh --version` -> `Lean (version 4.33.1, arm64-apple-darwin24.6.0, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)`, matching `challenge.ndjson:1`.

### 3(ii). Checker Log (`con-leche_compare.stdout.log`) on Hypotheses and Axioms of the Five Theorems

Exact contents of `~/rh-audit/agents3/input/con-leche_compare.stdout.log:1-6`:
```text
1: con-leche: accepted 51692 declarations, 5 axioms justified by the solution solution.ndjson (1468418 declarations accepted) (--verified)
2: con-leche: theorem riemannHypothesis justified by the solution
3: con-leche: theorem riemannZeta_eq_zero_re justified by the solution
4: con-leche: theorem LFunction_ne_zero_of_half_lt_re justified by the solution
5: con-leche: theorem LFunction_eq_zero_re justified by the solution
6: con-leche: theorem LFunction_eq_zero_re_of_isPrimitive justified by the solution
```

What this says (and does not say):
- **Declaration count match:** Streaming `challenge.ndjson` (6,495,712 lines) yields exactly `969 inductive + 4 quot + 10238 def + 40431 thm + 4 axiom + 46 opaque = 51692` declarations, matching `accepted 51692 declarations` on line 1.
- **Hypotheses:** Lines 2–6 report that `solution.ndjson` (1,468,418 declarations accepted) justifies all five named theorems of `challenge.ndjson`. Because none of the five theorem types in `challenge.ndjson` carries an extra hypothesis (verified in 3(iii) below), the log asserts that `solution.ndjson` justifies those exact hypothesis-free statements.
- **Axioms:** `challenge.ndjson` contains exactly 4 `axiom` records:
  - `challenge.ndjson:16847`: `propext` (`{"isUnsafe": false, "levelParams": [], "name": 2661, "type": 13681}`)
  - `challenge.ndjson:19518`: `Quot.sound` (`{"isUnsafe": false, "levelParams": [11], "name": 3046, "type": 15910}`)
  - `challenge.ndjson:45191`: `Classical.choice` (`{"isUnsafe": false, "levelParams": [11], "name": 4988, "type": 39114}`)
  - `challenge.ndjson:6426466`: `sorryAx` (`{"axiom":{"isUnsafe":false,"levelParams":[11],"name":326834,"type":6045959}}`)
  The five theorem declarations in `challenge.ndjson` all apply `sorryAx` (`ie=6045961`, `challenge.ndjson:6426469`) in their `value` expressions (reflecting `Challenge.lean:19,21,23,25,27` `:= by sorry`), which accounts for line 1's wording `5 axioms justified by the solution`. **Limitation (NOT VERIFIED):** The 6-line log does **not** print the list of axioms used by `solution.ndjson` by name; inferring that `solution.ndjson` uses only `{propext, Quot.sound, Classical.choice}` and zero `sorryAx`/custom axioms relies on trusting `con-leche --verified --compare`'s uninspected implementation.

### 3(iii). Streaming Inspection of `challenge.ndjson`: `riemannHypothesis` Record and `type` Expression

Streaming `~/rh-audit/export/challenge.ndjson` line by line in Python yielded:

- **Header (`challenge.ndjson:1`):**
  `{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"819816b2e0a3bf405af45ae5c7af2491d8f5bee6","version":"4.33.1"}}}`
- **Name and declaration records for `riemannHypothesis`:**
  - `challenge.ndjson:6426467`: `{"in":326835,"str":{"pre":0,"str":"riemannHypothesis"}}`
  - `challenge.ndjson:6426468`: `{"const":{"name":326825,"us":[]},"ie":6045960}`
  - `challenge.ndjson:6426520`: `{"thm":{"all":[326835],"levelParams":[],"name":326835,"type":6045960,"value":6046011}}`
- **Bare constant vs `forallE`:** The `type` expression of `riemannHypothesis` (`ie=6045960`, `challenge.ndjson:6426468`) is a **bare constant (`const`)**, **NOT** a `forallE`. Its constant name ID is `326825`, with empty universe list `us: []`.
- **Resolution of constant `326825` (`RiemannHypothesis`):**
  - `challenge.ndjson:6426430`: `{"in":326825,"str":{"pre":0,"str":"RiemannHypothesis"}}`
  - `challenge.ndjson:6426463`: `{"def":{"all":[326825],"hints":{"regular":52},"levelParams":[],"name":326825,"safety":"safe","type":3,"value":6045958}}` (where `ie=3` at `challenge.ndjson:14` is `{"ie":3,"sort":0}`, i.e. `Prop`).
  - Its unfolded `value` (`ie=6045958`) is the four-binder `forallE` chain at `challenge.ndjson:6426459-6426462`:
    - `challenge.ndjson:6426462`: `{"forallE":{"binderInfo":"default","body":6045957,"name":3214,"type":238344},"ie":6045958}` (binder `s` of type `ie=238344`, `challenge.ndjson:264972`: `const Complex`).
    - `challenge.ndjson:6426461`: `{"forallE":{"binderInfo":"default","body":6045956,"name":326831,"type":6045939},"ie":6045957}` (binder from `Mathlib.NumberTheory.LSeries.RiemannZeta` [`L6426433`], type `ie=6045939` applying `Eq` [`L3138`] to `riemannZeta` [`L6426438`] applied to `bvar 0` [`L12`] and `0`).
    - `challenge.ndjson:6426460`: `{"forallE":{"binderInfo":"default","body":6045955,"name":326832,"type":6045949},"ie":6045956}` (type `ie=6045949` applying `Not` [`L2676`] to `Exists` [`L16008`] over `Nat` [`L407`]).
    - `challenge.ndjson:6426459`: `{"forallE":{"binderInfo":"default","body":6045954,"name":326833,"type":6045950},"ie":6045955}` (type `s ≠ 1`, body `ie=6045954`).
  - `riemannZeta` itself is defined at `challenge.ndjson:6426425-6426429` as `HurwitzZeta.hurwitzZetaEven` (`L6426427`) applied to `ie=6027418` (`L6426428`), matching `RiemannZeta.lean:121`.
- **The other four theorems in `challenge.ndjson` also have bare `const` types (none is a `forallE`):**
  - `riemannZeta_eq_zero_re` (`L6426590`, `type: 6046030`) -> `L6426544`: `{"const":{"name":326836,"us":[]},"ie":6046030}` (`RiemannZetaZerosOnLine`, `L6426542`).
  - `LFunction_ne_zero_of_half_lt_re` (`L6485575`, `type: 6102821`) -> `L6485533`: `{"const":{"name":328666,"us":[]},"ie":6102821}` (`DirichletLNonvanishingRightOfHalf`, `L6485531`).
  - `LFunction_eq_zero_re` (`L6485634`, `type: 6102873`) -> `L6485593`: `{"const":{"name":328673,"us":[]},"ie":6102873}` (`DirichletLZerosOnLine`, `L6485591`).
  - `LFunction_eq_zero_re_of_isPrimitive` (`L6495696`, `type: 6112187`) -> `L6495650`: `{"const":{"name":329312,"us":[]},"ie":6112187}` (`PrimitiveDirichletLZerosOnLine`, `L6495648`).

### 3(iv). Static Scans of `~/rh-audit/src/omega` (Conditions 1, 2, 3, 5, 6)

1. **Axioms, `sorry`, bypasses, and statement redefinitions across all 175,188 `.lean` files (`git -C ~/rh-audit/src/omega ls-files 'src/*.lean' | wc -l` -> `175188`):**
   - `git grep -n -w -F 'axiom' src/`: **0 matches**.
   - `git grep -n -w -F 'admit' src/`: **0 matches**.
   - `git grep -n -w -F 'sorryAx' src/`: **0 matches**.
   - `git grep -n -w -F 'unsafe' src/`: **0 matches**.
   - `git grep -n -F 'implemented_by' src/`: **0 matches**.
   - `git grep -n -F -e 'native_decide' -e 'ofReduceBool' -e 'trustCompiler' -e '@[extern' src/`: **0 matches**.
   - `git grep -n -F 'import Challenge' src/`: **0 matches**.
   - `grep -E ':(private |protected )?opaque ' ~/rh-audit/index/decls.txt`: **0 matches**.
   - `git grep -n -w -F 'sorry' src/`: **5 matches, all in `src/Challenge.lean:19,21,23,25,27`** (never imported by `Main.lean`).
   - `git grep -n -F 'addDecl' src/`: **2 matches**, both in `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:78,82`, calling `addDecl (.defnDecl ...)` and `addDecl (.thmDecl ...)` (kernel-checked definitions/theorems, not `.axiomDecl`).
   - `git grep -n -E '(def|abbrev|structure|inductive|opaque|notation|macro)[[:space:]]+.*(RiemannHypothesis|riemannZeta)' src/`: **0 redefinitions** of `RiemannHypothesis` or `riemannZeta` (only helper defs mentioning them, such as `RHofHalfPlane` or `zetaR`).
2. **Vacuous `True` predicates and `rfl` declarations DO exist in `omega/src` (neutral check of Conditions 1 & 2):**
   - `grep -c -F ': Prop := True' ~/rh-audit/index/decls.txt` -> `9`. Examples confirmed directly in source:
     - `src/Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/SwOn.lean:5`: `def UpperTheory.One.M.TrivialCondition : Prop := True`
     - `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/TrivialLocalCondition.lean:89-90`: `def UnusedSlot55 ... : Prop := True` and `def NoCondition (_ : D7) : Prop := True`
     - `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:7`: `abbrev GlobalTheory.Published.UnusedSlot72 : Prop := True`
     - `src/Formalism/LocalToGlobal/ProjectiveLattices/RegPFree.lean:16`: `def trivialClassCondition (T : CDVR) (io : c.F →+* T.Fr) (_y : IntFr Xo c T io) : Prop := True`
   - `grep -c -E ':= fun .*=> True$' ~/rh-audit/index/decls.txt` -> `9`.
   - `grep -c -F ':= rfl' ~/rh-audit/index/decls.txt` -> `8084` (many are routine projection lemmas such as `src/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean:64`: `theorem adele_fst_mul (a b : 𝔸[E]) : (a * b).1 = a.1 * b.1 := rfl`).
   - **Important polarity distinction observed in `Main.lean`'s call chain:** Two `trivial` calls near the top of the proof chain (`Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:11` passing `trivial trivial` to `shape_of`, and `Imprimitive.lean:10` passing `trivial` to `h : ZeroFreeAll`) instantiate `True` in **negative (premise/domain) positions**:
     - `Development/AutomorphicArithmetic/CharacterBoxes/ShapeWin.lean:27`: `theorem UpperTheory.Top.shapeWin : GlobalTheory.GLq.Green → GlobalTheory.Fc.TopShape True True ... UpperTheory.Top.TopG` (where `TopShape V NR ... G` at `TopShape.lean:17,43,77` takes `(hVC : V)` and `(nR : NR)` as hypotheses—setting `V = True, NR = True` makes `shapeWin` **stronger**, proving `TopG` without those two hypotheses).
     - `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:14,18`: `def ZeroFreeOn (Q : PChar → Prop) : Prop := ∀ ψ : PChar, Q ψ → ψ.ZeroFreeAbove (1 / 2)` and `def ZeroFreeAll : Prop := ZeroFreeOn fun _ => True` (setting the quantifier filter `Q` to `fun _ => True` asserts zero-freeness for **all** `ψ`, making the statement **stronger**, not vacuous).

---

## 4. Is "Contains Vacuous Definitions and Equations Proved by `rfl`" Sufficient for "Proves Nothing"?

**Answer: NO.**

### Formal Argument

Let $\mathcal{L}$ be Lean's base dependent type theory (Calculus of Inductive Constructions with universe hierarchy plus `{propext, Quot.sound, Classical.choice}`), and let $T : \mathsf{Prop}$ be a closed proposition expressed strictly in the vocabulary of $\mathcal{L}$ (and a trusted library such as Mathlib; e.g., $T = \mathsf{RiemannHypothesis}$ or Euclid's theorem). Suppose a Lean development adds a finite set $\Delta$ of non-recursive definitions (including predicates equal to `True` or `fun _ => True`) and strictly positive inductive structures (including degenerate models with fields equated by `rfl`), and produces a closed kernel-checked derivation $\mathcal{L} + \Delta \vdash t : T$.

1. **Conservativity of definitional and standard-inductive extensions:** Every non-recursive `def c : A := e` is eliminable by $\delta$-expansion, and every strictly positive inductive structure type (such as `DegenerateModel` and `Bundle`) is conservatively interpretable in any standard set-theoretic model $\mathcal{M}$ of $\mathcal{L}$ (in ZFC + universes). Hence, for any closed formula $T$ not mentioning symbols in $\Delta$:
   $$\mathcal{L} + \Delta \vdash t : T \implies \mathcal{M} \models T \quad \text{for every standard model } \mathcal{M} \models \mathcal{L}.$$
   In particular, adding `anyGeometry := fun _ => True`, `DegenerateModel`, `Bundle`, `buildBundle`, and `rfl`-proved equalities **cannot** make a false or unprovable closed proposition $T$ provable (assuming $\mathcal{L}$ is consistent).
2. **Logical irrelevance of `True` and `rfl` inputs inside a proof term:** If an internal helper inside $t$ has type $P \to Q \to T$ where $P \equiv \mathsf{True}$ and $Q \equiv (42 = 42)$, then $(P \to Q \to T) \iff T$. Discharging $P$ with `trivial` and $Q$ with `rfl` supplies zero logical leverage toward $T$; the helper itself must still construct a valid derivation of $T$. Vacuous definitions can only make a result vacuous if they appear **positively inside the final statement $T$ itself** (weakening $T$), or if an empty/unproved hypothesis appears **negatively in $T$** (as in `claimed_rh`, where `hRH : RiemannHypothesis` is assumed).

### Compiled Minimal Lean Illustration

File created and compiled in scratch directory: `~/rh-audit/agents3/work/L/VacuousScaffoldingTest.lean` (`lines 1–129`).

- Lines `10–32` copy Nielsen's exact vacuous definitions (`anyGeometry := fun _ => True`, `targetFormula := 42`, `DegenerateModel`, `Bundle`, `buildBundle` with `geoOk := trivial` and `h_eq := rfl`, and `valid_bundle_of_manufactured`).
- Lines `35–36` define `def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p`.
- Lines `101–124` prove `theorem euclid_with_vacuous_scaffolding (n : Nat) : ∃ p : Nat, n < p ∧ IsPrime p` (Euclid's theorem: infinitely many primes), explicitly binding `let b : Bundle := buildBundle`, `have hvac := valid_bundle_of_manufactured b`, and passing `hvac.1 hvac.2` into a `helper : anyGeometry 0 → b.model.height = targetFormula → ∃ p : Nat, n < p ∧ IsPrime p`.
- Command: `~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/L/VacuousScaffoldingTest.lean`
- Output (exit code `0`):
  ```text
  VacuousScaffolding.euclid_with_vacuous_scaffolding : ∀ (n : Nat), ∃ p, n < p ∧ VacuousScaffolding.IsPrime p
  'VacuousScaffolding.euclid_with_vacuous_scaffolding' depends on axioms: [propext, Quot.sound]
  ```
Thus a file containing Nielsen's exact vacuous definitions and `rfl` equations—even woven directly into the proof term—still constitutes a completely sound, unconditional proof of a non-trivial mathematical theorem (using not even `Classical.choice`).

---

## 5. Exhaustive Ways a Kernel-Accepted Closed Term of Type `T` (Using Only `propext`, `Quot.sound`, `Classical.choice`) Can Still Fail to Prove the Intended Mathematical Statement

Assume a kernel accepts a closed term $\vdash t : T$ whose axiom footprint is $\subseteq \{\text{propext}, \text{Quot.sound}, \text{Classical.choice}\}$. Exhaustively, this can still fail to be a valid proof of the intended mathematical statement $S_{\text{math}}$ in the following ways:

1. **Statement-level mismatch (formalization gap between $T$ and $S_{\text{math}}$):**
   - **1a. Extra, hidden, or contradictory hypotheses in $T$:** $T$ has implication/`forallE` shape $H \to C$ where $H$ assumes the conclusion itself, an unproved conjecture, or a contradiction/empty domain (including implicit `variable`/section assumptions).
     - *Addressed by posted example?* **YES.** This is the sole mechanism by which `claimed_rh` (`NielsenMinimal.lean:35-38`) avoids proving RH: it assumes `(hRH : RiemannHypothesis)`.
   - **1b. Weakened conclusion or semantic error in $T$'s definitions:** $T$ is unconditional, but $T$ or a definition referenced by $T$ (`RiemannHypothesis`, `riemannZeta`, `Complex`, `Real`, `LFunction`, or edge-case/junk-value conventions) is shadowed, redefined (e.g., to `True`), or misformalized relative to $S_{\text{math}}$.
     - *Addressed by posted example?* **NO.** `NielsenMinimal.lean` imports Mathlib's `RiemannHypothesis` unmodified and only places vacuous definitions in a separate first conjunct.
   - **1c. Degenerate universe, implicit-argument, or typeclass instantiation in $T$:** $T$ quantifies over a degenerate structure/instance (e.g., a trivial ring `0 = 1` or broken instance) rather than the intended mathematical object.
     - *Addressed by posted example?* **NO.**
2. **Foundational / metamathematical failure of the base logic:**
   - **2a. Inconsistency of Lean's type theory + `{propext, Quot.sound, Classical.choice}`:** If CIC with universes + these three axioms were inconsistent, `False`—and hence every `T`—would admit a genuine closed proof term.
     - *Addressed by posted example?* **NO.**
   - **2b. Foundational rejection of classical axioms:** Under constructive, predicative, or finitary standards, reliance on `Classical.choice` or impredicative `Prop` disqualifies the derivation as a proof (though accepted in mainstream classical mathematics).
     - *Addressed by posted example?* **NO.** `NielsenMinimal.lean` treats `[propext, Classical.choice, Quot.sound]` as standard.
3. **Kernel, checker, and Trusted Computing Base (TCB) failure:**
   - **3a. Soundness bug in the kernel or independent checker:** A bug in Lean's kernel or in an external checker (`con-leche`, etc.)—such as faulty reduction/defeq, positivity/termination/universe checking, expression hash collision, or a faulty `--compare` routine (e.g., not enforcing matching types or failing to reject extra axioms/`sorryAx` in `solution.ndjson`)—could accept an invalid term.
     - *Addressed by posted example?* **NO.** `NielsenMinimal.lean` is a standard valid proof of an implication and triggers no kernel bug.
   - **3b. Unchecked kernel bypasses:** Mechanisms like `unsafe`, `@[implemented_by]`, `@[extern]`, `Lean.ofReduceBool`/`Lean.trustCompiler`, or unchecked environment insertion (`addDeclWithoutChecking`), if not caught by the kernel/axiom check (hence strictly a subcase of 3a or incomplete axiom auditing).
     - *Addressed by posted example?* **NO.**
   - **3c. Compiler, runtime, OS, or hardware fault/compromise:** Miscompilation of the kernel binary, supply-chain compromise ("trusting trust"), or hardware bit-flip producing a spurious acceptance.
     - *Addressed by posted example?* **NO.**
4. **Provenance and reporting mismatch:**
   - **4a. Disconnect between checked export and published source (or forged log):** `solution.ndjson` or `con-leche_compare.stdout.log` might not genuinely originate from compiling the published git revision of `~/rh-audit/src/omega` with an authentic checker. (Note: if a sound kernel truly accepted `solution.ndjson` against `challenge.ndjson` with only the 3 axioms, *some* formal proof of $T$ would still exist in `solution.ndjson`, even if `omega/src` were not its source.)
     - *Addressed by posted example?* **NO.**
   - **4b. Misreading/cherry-picking the audited declaration:** Checking `#print axioms` on a declaration while failing to inspect its full elaborated type (e.g., mistaking `claimed_rh : RiemannHypothesis → ...` for an unconditional proof of `RiemannHypothesis`).
     - *Addressed by posted example?* **YES (indirectly, via 1a):** `NielsenMinimal.lean:40` runs `#print axioms claimed_rh`, illustrating that a clean axiom list proves nothing unless one also inspects the theorem's type.

---

## 6. Verdict on (C)

**Verdict:** **INVALID**

**Reason (6 lines):**
1. Claim (C) asserts that the release compiles in the same way as `NielsenMinimal.lean` and therefore does not prove the Riemann Hypothesis.
2. In `NielsenMinimal.lean:35-38`, `claimed_rh` compiles without `sorry` or custom axioms **only** because its type is a `forallE` implication taking `(hRH : RiemannHypothesis)` as a premise and returning `hRH` unchanged (`TestTypes.lean`).
3. By contrast, `Main.lean:4` declares `theorem riemannHypothesis : RiemannHypothesis := rhOfAll` with no hypotheses, and `challenge.ndjson:6426468,6426520` confirms its kernel `type` is the bare constant `const RiemannHypothesis` (official Mathlib `v4.33.1`), not a `forallE`.
4. Although `omega/src` does contain some `:= True` definitions and `:= rfl` proofs, those ingredients are logically insufficient to forge or invalidate an unconditional closed proof of a non-vacuous type in a sound kernel (Section 4; `VacuousScaffoldingTest.lean`).
5. Thus both the factual premise ("compiles in the same way") and the inferential step ("vacuous ingredients imply proves nothing") of (C) fail.
6. *Scope caveat:* Ruling (C) **INVALID** refutes Nielsen's specific inference from the posted example; it does **not** independently verify that the unbuilt release source compiles into a sound proof of the Riemann Hypothesis (see "What I could not verify").

**Single strongest point in favour of Nielsen (the author of the example):**
The release source genuinely contains literal `:= True` / `UnusedSlot` definitions (`SwOn.lean:5`, `TrivialLocalCondition.lean:89-90`, `DiscreteSpectrumResidualClassification.lean:7`, `RegPFree.lean:16`), `trivial` arguments, and 8,084 `:= rfl` lines in `decls.txt`; and Nielsen's example rightly highlights that "zero `sorry`" plus a clean `#print axioms` output are insufficient by themselves without checking exact kernel types and build/checker provenance.

**Single strongest point against Nielsen (the author of the example):**
The sole mechanism allowing `claimed_rh` to compile without proving RH—taking `(hRH : RiemannHypothesis)` as an explicit `forallE` hypothesis (`NielsenMinimal.lean:35-38`)—is absent from `Main.lean:4` and refuted at the kernel-export level by `challenge.ndjson:6426468,6426520` (`const RiemannHypothesis`, not `forallE`), while vacuous `True`/`rfl` ingredients alone cannot produce a closed term of type `RiemannHypothesis` in a sound kernel (`VacuousScaffoldingTest.lean`).

---

## Summary Table

| Item / Condition | Tested via | Outcome | Key citation / output |
|---|---|---|---|
| Cond. 1 (`True` defs) | `decls.txt` grep + source read | Present (mixed polarity) | 9 `: Prop := True` (`SwOn.lean:5`, `UnusedSlot55/72`); negative polarity in `ShapeWin.lean:27`, `ZeroFreeAll` (`ExplicitFormulaErrorOfHostConditions.lean:18`) |
| Cond. 2 (`rfl` eqs) | `decls.txt` grep | Present (routine + general) | 8,084 `:= rfl` lines in `decls.txt` (e.g., `HeckeIdem.lean:64`) |
| Cond. 3 (No `sorry`/axioms in src) | `git grep` on `omega/src` (175,188 files) | Holds in `src/` (excl. `Challenge.lean`) | 0 `axiom`/`admit`/`sorryAx`/`unsafe`/`implemented_by`/`native_decide`; `sorry` only in `Challenge.lean:19-27` (unimported) |
| Cond. 4 (`forallE` `hRH` premise) | `TestTypes.lean`, `Main.lean`, `challenge.ndjson` | **REFUTED** | `claimed_rh : RiemannHypothesis → ...` vs `challenge.ndjson:6426468,6426520` `type: 6045960` = bare `const RiemannHypothesis` |
| Cond. 5 (RH redefined/weakened) | `diff`, Mathlib check, `git grep`, `challenge.ndjson` | **REFUTED** (for `Main`/`Challenge`) | `Statements.lean` = `Challenge.lean:1-16`; Mathlib `v4.33.1` (`0df444a3`); 0 redefs of `RiemannHypothesis`/`riemannZeta` |
| Cond. 6 (Checker/export bypass) | `challenge.ndjson`, `con-leche` log | **NOT VERIFIED** | Log reports 51,692 / 1,468,418 decls & 5 theorems justified; `solution.ndjson` and `con-leche` binary unaudited |
| Sec. 4 (Vacuous $\Rightarrow$ nothing?) | Formal proof + `VacuousScaffoldingTest.lean` | **NO** | Compiled Euclid's theorem with Nielsen's exact `Bundle`/`True`/`rfl` scaffolding; axioms `[propext, Quot.sound]` |
| Sec. 5 (Failure modes) | Exhaustive TCB/logic taxonomy | 4 categories (10 subcases) | Example addresses only 1a (and indirectly 4b); does not address 1b–c, 2a–b, 3a–c, 4a |
| Sec. 6 (Verdict on C) | Combined logic & mechanical tests | **INVALID** | Example's `hRH` hypothesis mechanism is absent; vacuous scaffolding cannot forge a closed RH proof |

---

## What I Could Not Verify

1. **Compilation of `~/rh-audit/src/omega` itself (`NOT VERIFIED`):** The release is not built locally and the review is strictly read-only, so `Main.lean` and its 175,188-file dependency graph were not elaborated or type-checked with Lean `4.33.1` or `leanchecker` here.
2. **Direct contents and axiom footprint of `solution.ndjson` (`NOT VERIFIED`):** The 61.57 GB `solution.ndjson` export was not part of the inspected artefacts. In particular, `con-leche_compare.stdout.log` does not print the list of `axiom` declarations present in `solution.ndjson` by name, so the absence of custom axioms, `sorryAx`, `Lean.ofReduceBool`, or `Lean.trustCompiler` inside `solution.ndjson` could not be directly verified from `solution.ndjson` itself.
3. **Provenance linking `solution.ndjson` to `~/rh-audit/src/omega` commit `c7d25b3bf` (`NOT VERIFIED`):** Nothing in the local artefacts cryptographically or mechanically proves that `solution.ndjson` was exported from this exact git checkout of `omega/src`, or that `con-leche_compare.stdout.log` was produced by an unmodified `con-leche` binary run on `challenge.ndjson` and `solution.ndjson`.
4. **Soundness and exact comparison semantics of `con-leche --verified --compare` (`NOT VERIFIED`):** Neither the source code nor the executable behavior of `con-leche` was audited; hence whether `--verified --compare` enforces that `solution.ndjson` introduces no axioms beyond `challenge.ndjson`'s `{propext, Quot.sound, Classical.choice}`, handles universe polymorphism/definitional equality soundly, and is free of checker bugs is not verified here.
5. **Exhaustive audit of multi-line vacuous definitions or mathematical content across all 175,188 files (`NOT VERIFIED`):** Single-line greps of `decls.txt` do not capture multi-line `:= True` or `:= rfl` declarations, and only the top-level files of `Main.lean`'s import chain and sampled `:= True` files were read in full. (Per Section 4, however, internal vacuous definitions cannot compromise a sound kernel check of an unconditional Mathlib statement.)
6. **Deep mathematical audit of Mathlib `v4.33.1`'s foundational definitions (`NOT VERIFIED`):** While `RiemannHypothesis`, `riemannZeta`, and `DirichletCharacter.LFunction` were confirmed to match official Mathlib `v4.33.1` (`0df444a360eaa60ab8c11dca51a86af692955474`), the full transitive chain of Mathlib's underlying definitions (`HurwitzZeta`, `Complex`, `Real`, etc.) was not audited line by line.
