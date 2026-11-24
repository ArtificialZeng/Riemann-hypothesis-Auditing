# Task M: Kernel-Export Statement Check (`solution.ndjson`, `challenge.ndjson`, and Nielsen's Posted Example)

**Inputs inspected (read-only):**
- `~/rh-audit/export/solution.ndjson` (`61,570,595,788` bytes; `1,080,769,508` lines; header line 1: `{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"819816b2e0a3bf405af45ae5c7af2491d8f5bee6","version":"4.33.1"}}}`)
- `~/rh-audit/export/challenge.ndjson` (`350,862,311` bytes; `6,495,712` lines; identical line 1 header)
- `~/rh-audit/agents3/input/posted_verbatim.txt` and `~/rh-audit/agents3/input/NielsenMinimal.lean`
- `~/rh-audit/agents3/input/con-leche_compare.stdout.log`

---

## 1. `riemannHypothesis` in `solution.ndjson`

Searching the tail of `~/rh-audit/export/solution.ndjson` (and confirming exact 1-based line numbers via the full-file streaming script `~/rh-audit/agents3/work/M/scan_sol_axioms.py` and `tail -n 2405 ~/rh-audit/export/solution.ndjson | head -n 12`) yields the following verbatim records:

- **Name record of `riemannHypothesis`** (`~/rh-audit/export/solution.ndjson:1080767110`):
  ```json
  {"in":14065054,"str":{"pre":0,"str":"riemannHypothesis"}}
  ```
  Name ID: `14065054` (top-level name, `pre: 0`).

- **`thm` record of `riemannHypothesis`** (`~/rh-audit/export/solution.ndjson:1080767112`):
  ```json
  {"thm":{"all":[14065054],"levelParams":[],"name":14065054,"type":6490658,"value":1065212062}}
  ```
  Type expression ID: `6490658`; proof-term (`value`) expression ID: `1065212062`; `levelParams`: `[]`.

- **Resolved `type` expression record `ie = 6490658`** (`~/rh-audit/export/solution.ndjson:6887633`, verified via `sed -n '6887630,6887638p;6894370,6894428p;6894429q'` and `~/rh-audit/agents3/work/M/find_early_sol.py`):
  ```json
  {"const":{"name":326825,"us":[]},"ie":6490658}
  ```

- **Resolved constant name `in = 326825`** (`~/rh-audit/export/solution.ndjson:6426430`):
  ```json
  {"in":326825,"str":{"pre":0,"str":"RiemannHypothesis"}}
  ```

- **Definition record of `RiemannHypothesis`** (`~/rh-audit/export/solution.ndjson:6426463`, with `ie = 3` at line `14` `{"ie":3,"sort":0}` and `ie = 6045958` at line `6426462`):
  ```json
  {"forallE":{"binderInfo":"default","body":6045957,"name":3214,"type":238344},"ie":6045958}
  {"def":{"all":[326825],"hints":{"regular":52},"levelParams":[],"name":326825,"safety":"safe","type":3,"value":6045958}}
  ```

**Shape of the type:** The `type` of `riemannHypothesis` in `solution.ndjson` (`ie = 6490658`) is a **bare `const`** referring to the top-level constant `RiemannHypothesis` (`name: 326825`, `us: []`). It does **not** start with `forallE` (there is no outer hypothesis or quantifier on the theorem's type expression; the `forallE` quantifiers over `s : Complex` etc. occur inside the definition body `value = 6045958` of `def RiemannHypothesis`).

---

## 2. `riemannHypothesis` in `challenge.ndjson` and Comparison

Scanning `~/rh-audit/export/challenge.ndjson` (via `~/rh-audit/agents3/work/M/analyze_challenge_fast.py` and `sed -n '6426460,6426522p' ~/rh-audit/export/challenge.ndjson`) yields the following verbatim records:

- **Name record of `riemannHypothesis`** (`~/rh-audit/export/challenge.ndjson:6426467`):
  ```json
  {"in":326835,"str":{"pre":0,"str":"riemannHypothesis"}}
  ```

- **`thm` record of `riemannHypothesis`** (`~/rh-audit/export/challenge.ndjson:6426520`):
  ```json
  {"thm":{"all":[326835],"levelParams":[],"name":326835,"type":6045960,"value":6046011}}
  ```
  (Here `value = 6046011` is built using `ie = 6045961` at line `6426469`: `{"const":{"name":326834,"us":[0]},"ie":6045961}`, i.e. `sorryAx`.)

- **Resolved `type` expression record `ie = 6045960`** (`~/rh-audit/export/challenge.ndjson:6426468`):
  ```json
  {"const":{"name":326825,"us":[]},"ie":6045960}
  ```

- **Resolved constant name `in = 326825`** (`~/rh-audit/export/challenge.ndjson:6426430`):
  ```json
  {"in":326825,"str":{"pre":0,"str":"RiemannHypothesis"}}
  ```

- **Definition record of `RiemannHypothesis`** (`~/rh-audit/export/challenge.ndjson:6426463`):
  ```json
  {"def":{"all":[326825],"hints":{"regular":52},"levelParams":[],"name":326825,"safety":"safe","type":3,"value":6045958}}
  ```

**Are the two statements the same constant by name?**
**Yes.** In both `solution.ndjson` and `challenge.ndjson`, the `type` of `riemannHypothesis` is a bare `const` (`us: []`) pointing to the top-level constant `RiemannHypothesis` (`pre: 0`), with the exact same name ID `326825`.

Furthermore, hashing the first `6,426,463` lines (up to and including `def RiemannHypothesis` at line `6426463`) of both files gives identical SHA-256 digests and byte lengths:
```text
challenge first 6426463 lines: 76cdfa12c3dc6bbfa22730e6d52c6e42e5057594a3fe1cb29068ee930f7011a1 347181802
solution  first 6426463 lines: 76cdfa12c3dc6bbfa22730e6d52c6e42e5057594a3fe1cb29068ee930f7011a1 347181802
IDENTICAL: True
```
Thus `RiemannHypothesis` (lines `6426430`–`6426463`, where `3214` is `s`, `238344` is `const 22503` = `Complex`, and `326824` is `riemannZeta`) and every transitive dependency preceding it are byte-for-byte identical in both exports.

---

## 3. Kernel Shape of Nielsen's Posted Example (`claimed_rh`)

Comparing `~/rh-audit/agents3/input/posted_verbatim.txt` (40 lines) and `~/rh-audit/agents3/input/NielsenMinimal.lean` (40 lines) confirmed they differ only in leading spaces (`non-leading-space diffs: []`). Elaborating `~/rh-audit/agents3/input/NielsenMinimal.lean` unmodified via:
```sh
~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/input/NielsenMinimal.lean
```
exited with code `0` and printed:
```text
'claimed_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
```

In `~/rh-audit/agents3/input/NielsenMinimal.lean:35-38`, the theorem is:
```lean
theorem claimed_rh (hRH : RiemannHypothesis) :
    (∃ b : Bundle, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis := by
  let b := buildBundle
  exact ⟨⟨b, valid_bundle_of_manufactured b⟩, hRH⟩
```

To inspect its elaborated kernel type and proof term without `open Lean in #eval`, I copied `NielsenMinimal.lean` verbatim to `~/rh-audit/agents3/work/M/CheckNielsen.lean` and appended lines 41–48:
```lean
#check @claimed_rh
set_option pp.explicit true in
#check @claimed_rh
set_option pp.explicit true in
#print claimed_rh
set_option pp.all true in
#check @claimed_rh
#print RiemannHypothesis
```

Running `~/rh-audit/agents3/leanc.sh ~/rh-audit/agents3/work/M/CheckNielsen.lean` exited with code `0` and produced the following verbatim output:
```text
'claimed_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
claimed_rh : RiemannHypothesis → (∃ b, anyGeometry 0 ∧ b.model.height = targetFormula) ∧ RiemannHypothesis
claimed_rh : RiemannHypothesis →
  And
    (∃ b,
      And (anyGeometry (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Eq Nat b.model.height targetFormula))
    RiemannHypothesis
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
claimed_rh : ∀ (hRH : RiemannHypothesis),
  And
    (@Exists.{1} Bundle fun (b : Bundle) =>
      And (anyGeometry (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Eq.{1} Nat (DegenerateModel.height (Bundle.model b)) targetFormula))
    RiemannHypothesis
def RiemannHypothesis : Prop :=
∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n, s = -2 * (↑n + 1)) → s ≠ 1 → s.re = 1 / 2
```

As `set_option pp.all true in #check @claimed_rh` and `set_option pp.explicit true in #print claimed_rh` show, the type of `claimed_rh` is a `forallE` (function/implication type) `∀ (hRH : RiemannHypothesis), And (...) RiemannHypothesis` whose domain is `RiemannHypothesis`, and its proof term is a `lam` (`fun hRH => ... hRH`) that receives a proof `hRH : RiemannHypothesis` as input and returns it in the second conjunct.

---

## 4. Resolving `value` of `riemannHypothesis` One Level in `solution.ndjson`

In `~/rh-audit/export/solution.ndjson:1080767112`, the `thm` record of `riemannHypothesis` has `"value":1065212062`. Resolving `ie = 1065212062` and the referenced constant in the tail (`tail -n 2405 ~/rh-audit/export/solution.ndjson | head -n 12`):

- **Expression record `ie = 1065212062`** (`~/rh-audit/export/solution.ndjson:1080767111`):
  ```json
  {"const":{"name":14065053,"us":[]},"ie":1065212062}
  ```
  It refers to a single constant: name ID `14065053` (`us: []`).

- **Name record of `14065053`** (`~/rh-audit/export/solution.ndjson:1080767105`):
  ```json
  {"in":14065053,"str":{"pre":0,"str":"rhOfAll"}}
  ```
  Constant name: top-level `rhOfAll` (`pre: 0`).

- **`thm` record of `rhOfAll`** (`~/rh-audit/export/solution.ndjson:1080767109`):
  ```json
  {"thm":{"all":[14065053],"levelParams":[],"name":14065053,"type":6490658,"value":1065212061}}
  ```

- **Resolved `type` of `rhOfAll`**: its `type` expression ID is `6490658` — the exact same expression record already found at `~/rh-audit/export/solution.ndjson:6887633`:
  ```json
  {"const":{"name":326825,"us":[]},"ie":6490658}
  ```
  Thus `rhOfAll` also has type equal to the bare `const` `RiemannHypothesis` (`name: 326825`, `us: []`), not a `forallE`.

*(Additional context one step further, directly adjacent at lines `1080767104`–`1080767108` and `6894372`–`6894424`: `rhOfAll`'s `value` `1065212061` is `{"app":{"arg":1065212060,"fn":1065212059},"ie":1065212061}`, applying `const 341189` (`Formalism.VW.rh_of_every`, L6894372/L6894424, whose `type = 6497237` at L6894374 is `{"forallE":{"binderInfo":"default","body":6490658,"name":269,"type":6497236},"ie":6497237}`, i.e. `UpperTheory.EveryCharacter → RiemannHypothesis`) to `const 14065052` (`allChi`, L1080767104, whose `type = 6497236` at L6894373 is `{"const":{"name":326947,"us":[]},"ie":6497236}`, i.e. `UpperTheory.EveryCharacter`).)*

---

## 5. Axioms in `challenge.ndjson` and `solution.ndjson`

### A. All `axiom` records in `challenge.ndjson` (full pass verified)

Running `~/rh-audit/agents3/work/M/analyze_challenge_fast.py` over all `6,495,712` lines (`51,692` declarations) of `~/rh-audit/export/challenge.ndjson` found **exactly 4 `axiom` records**:

1. **`propext`** (`name: 2661`):
   - `~/rh-audit/export/challenge.ndjson:16840`: `{"in":2661,"str":{"pre":0,"str":"propext"}}`
   - `~/rh-audit/export/challenge.ndjson:16847`: `{"axiom":{"isUnsafe":false,"levelParams":[],"name":2661,"type":13681}}`
2. **`Quot.sound`** (`name: 3046`):
   - `~/rh-audit/export/challenge.ndjson:61`: `{"in":15,"str":{"pre":0,"str":"Quot"}}`
   - `~/rh-audit/export/challenge.ndjson:19505`: `{"in":3046,"str":{"pre":15,"str":"sound"}}`
   - `~/rh-audit/export/challenge.ndjson:19518`: `{"axiom":{"isUnsafe":false,"levelParams":[11],"name":3046,"type":15910}}`
3. **`Classical.choice`** (`name: 4988`):
   - `~/rh-audit/export/challenge.ndjson:45187`: `{"in":4987,"str":{"pre":0,"str":"Classical"}}`
   - `~/rh-audit/export/challenge.ndjson:45188`: `{"in":4988,"str":{"pre":4987,"str":"choice"}}`
   - `~/rh-audit/export/challenge.ndjson:45191`: `{"axiom":{"isUnsafe":false,"levelParams":[11],"name":4988,"type":39114}}`
4. **`sorryAx`** (`name: 326834`):
   - `~/rh-audit/export/challenge.ndjson:6426464`: `{"in":326834,"str":{"pre":0,"str":"sorryAx"}}`
   - `~/rh-audit/export/challenge.ndjson:6426466`: `{"axiom":{"isUnsafe":false,"levelParams":[11],"name":326834,"type":6045959}}`

### B. `solution.ndjson` in `con-leche_compare.stdout.log` and Independent Verification

`~/rh-audit/agents3/input/con-leche_compare.stdout.log:1-6` reads verbatim:
```text
con-leche: accepted 51692 declarations, 5 axioms justified by the solution solution.ndjson (1468418 declarations accepted) (--verified)
con-leche: theorem riemannHypothesis justified by the solution
con-leche: theorem riemannZeta_eq_zero_re justified by the solution
con-leche: theorem LFunction_ne_zero_of_half_lt_re justified by the solution
con-leche: theorem LFunction_eq_zero_re justified by the solution
con-leche: theorem LFunction_eq_zero_re_of_isPrimitive justified by the solution
```

The log refers to the 5 target theorems (whose `thm` records in `challenge.ndjson` I verified exist at lines `6426520`, `6426590`, `6485575`, `6485634`, and `6495696`, out of `51,692` total declarations) as "5 axioms justified by the solution", and does not explicitly enumerate `propext`/`Quot.sound`/`Classical.choice` by name.

**What I verified myself on `solution.ndjson`:** I ran a single full streaming scan (`~/rh-audit/agents3/work/M/scan_sol_axioms.py`) over all `61,570,595,788` bytes (`1,080,769,508` lines) of `~/rh-audit/export/solution.ndjson` (completed in `428.1s`). Results:
- **Exactly 3 `axiom` records** appear in the entire 61.57 GB file, at the exact same lines and IDs (within the SHA-256-identical prefix) as the 3 standard Lean axioms in `challenge.ndjson`:
  - `~/rh-audit/export/solution.ndjson:16847`: `{"axiom":{"isUnsafe":false,"levelParams":[],"name":2661,"type":13681}}` (`propext`)
  - `~/rh-audit/export/solution.ndjson:19518`: `{"axiom":{"isUnsafe":false,"levelParams":[11],"name":3046,"type":15910}}` (`Quot.sound`)
  - `~/rh-audit/export/solution.ndjson:45191`: `{"axiom":{"isUnsafe":false,"levelParams":[11],"name":4988,"type":39114}}` (`Classical.choice`)
- **`0` occurrences** of `"sorryAx"` anywhere in `~/rh-audit/export/solution.ndjson`.
- **NOT VERIFIED by myself:** I did **not** re-run `con-leche` or any kernel type-checker over `solution.ndjson`'s `1,468,418` declarations, nor verify the declaration count `1468418` or the proof terms of `solution.ndjson` beyond checking `axiom`/`sorryAx` presence and the records cited in Sections 1–4.

---

## 6. Conclusion

No. At the kernel-export level, `riemannHypothesis` in `solution.ndjson` does **not** have the shape of Nielsen's posted example `claimed_rh`.
In Nielsen's example, `claimed_rh` has a `forallE` function type `∀ (hRH : RiemannHypothesis), (∃ b : Bundle, …) ∧ RiemannHypothesis` taking `RiemannHypothesis` as a hypothesis and returning it in its proof.
In both `solution.ndjson` and `challenge.ndjson`, `riemannHypothesis` has type `{"const":{"name":326825,"us":[]}}` — the bare constant `RiemannHypothesis` (defined identically in the byte-for-byte identical 6,426,463-line Mathlib prefix of both exports), with no outer `forallE`.
Resolving `riemannHypothesis`'s proof term one level in `solution.ndjson` gives `rhOfAll`, whose type is the same bare constant `RiemannHypothesis` (`ie: 6490658`).
A full pass over `solution.ndjson` finds only the three standard Lean axioms (`propext`, `Quot.sound`, `Classical.choice`) and zero `sorryAx` records, showing that the exported theorem does not assume `RiemannHypothesis` either as a parameter or as an axiom.
This check does not independently re-type-check `solution.ndjson`'s 1,468,418 declarations (relying on `con-leche_compare.stdout.log` for checker acceptance) nor audit intermediate proofs below `rhOfAll`.

---

## Summary Table

| Field | `solution.ndjson` | `challenge.ndjson` | Nielsen's `claimed_rh` |
|---|---|---|---|
| Target theorem | `riemannHypothesis` (`in:14065054`, L1080767110) | `riemannHypothesis` (`in:326835`, L6426467) | `claimed_rh` (`NielsenMinimal.lean:35`) |
| Type record / shape | Bare `const` (`ie:6490658`, L6887633) | Bare `const` (`ie:6045960`, L6426468) | `forallE` (`∀ (hRH : RiemannHypothesis), …`) |
| Constant referenced | `RiemannHypothesis` (`in:326825`, `us:[]`) | `RiemannHypothesis` (`in:326825`, `us:[]`) | Domain `RiemannHypothesis`; codomain `And … RH` |
| `RiemannHypothesis` def | L6426463; 6,426,463-line prefix SHA-256 identical | L6426463; 6,426,463-line prefix SHA-256 identical | Mathlib v4.33.1 `RiemannHypothesis` |
| 1-level `value` | `const` `rhOfAll` (`in:14065053`, `type:6490658`) | `app` using `sorryAx` (`in:326834`, L6426469) | `fun hRH => … hRH` |
| `axiom` records | 3: `propext`, `Quot.sound`, `Classical.choice` | 4: `propext`, `Quot.sound`, `Classical.choice`, `sorryAx` | `[propext, Classical.choice, Quot.sound]` |
| `sorryAx` in file | 0 hits across all 61.57 GB (verified) | Present (L6426466, L6426469) | Absent (`#print axioms`) |
| Full type-checking | Reported accepted in `con-leche` log (NOT re-run) | 51,692 decls counted; `con-leche` NOT re-run | Verified via `leanc.sh` (Lean 4.33.1) |

---

## What I could not verify

1. **Full kernel type-checking of `solution.ndjson` (NOT VERIFIED):** I did not run `con-leche` or any Lean 4 kernel checker on `solution.ndjson` or `challenge.ndjson`. The acceptance of `1,468,418` declarations in `solution.ndjson` and justification of the 5 challenge theorems come solely from `~/rh-audit/agents3/input/con-leche_compare.stdout.log`; I did not inspect the `con-leche` binary, source code, or invocation.
2. **Total declaration count and non-`axiom` declaration kinds in `solution.ndjson` (NOT VERIFIED):** My full streaming scan of `solution.ndjson` checked only `"axiom":`, `"sorryAx"`, and the `riemannHypothesis`/`rhOfAll` records. I did not independently verify the total declaration count (`1,468,418`) of `solution.ndjson`, nor scan all `1,080,769,508` lines for `opaque` declarations or `unsafe`/`partial` definitions.
3. **Complete recursive unfolding of `def RiemannHypothesis` (`ie: 6045958`) inside the export (NOT FULLY VERIFIED):** I verified that `def RiemannHypothesis` at line `6426463` has `type: 3` (`Prop`), `value: 6045958` (four nested `forallE` binders beginning with `s : Complex` and referencing `riemannZeta`), and sits inside a 6,426,463-line prefix that is SHA-256 identical between `challenge.ndjson` and `solution.ndjson`, and confirmed Mathlib v4.33.1's `RiemannHypothesis` via `#print RiemannHypothesis`. I did not recursively decode every leaf expression of `ie: 6045958` in the NDJSON to prove term-by-term equivalence with Mathlib v4.33.1's source.
4. **Other four theorems, deeper proof structure, and source-to-export correspondence (NOT VERIFIED):** I did not inspect the types or proof terms of the other four theorems (`riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`) in `solution.ndjson`, did not inspect proofs inside `allChi` or `Formalism.VW.rh_of_every`, and could not verify that `solution.ndjson` was exported from the unbuilt checkout at `~/rh-audit/src/omega`.
5. **Direct `lean4export` serialization of `NielsenMinimal.lean` (NOT VERIFIED):** As specified in the task, Nielsen's example was not exported to `lean4export` NDJSON; its kernel shape was verified via Lean 4.33.1 elaboration output (`#check @claimed_rh`, `pp.explicit`, `pp.all`, `#print claimed_rh`).
