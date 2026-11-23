# Independent Logic Review of J. L. Nielsen's Argument ([quotation from the paper omitted])

**Path conventions.** Citations of the form `paper.txt:L` refer to `~/rh-audit/nielsen/paper.txt`. Citations of the form `src/...:L` (or repo-root files such as `lake-manifest.json:L`, `comparator.json:L`) refer to `~/rh-audit/src/omega/`. Citations of `decls.txt:L` refer to `~/rh-audit/index/decls.txt`. Known facts F1–F4 are taken as given by the review mandate; all code claims cited below were checked directly against the source tree unless explicitly marked **NOT VERIFIED**.

---

## 1. Reconstruction of the Paper's Inference

Below is the paper's argument from its premises to its conclusion *[quotation from the paper omitted]* (`paper.txt:32`, `paper.txt:837-838`), reconstructed step by step and tagged as `(code fact)`, `(claim about what a proof requires)`, or `(logical inference)`:

1. **(code fact)** The headline theorem inhabits Mathlib's `RiemannHypothesis`, is closed with no hypotheses, and uses no `axiom`, `sorry`, `native_decide`, `unsafe`, or `opaque` declarations.
   - `paper.txt:14-16`: `[quotation from the paper omitted]`
   - `paper.txt:814-815`: `[quotation from the paper omitted]`
   - Code verification: `src/Main.lean:4`: `theorem riemannHypothesis : RiemannHypothesis := rhOfAll`; `src/Supplements/Kernels/MainTheorems.lean:9`: `theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi` (consistent with F1–F2).

2. **(code fact)** The actual proof term of `riemannHypothesis` routes through `rhOfAll` → `allChi` → `everyCharacter` → `everyCharacter_of_row` → `every_character_of_literature_of_vWin` → `every_character_of_theta_integrals_local_matching` → `every_character_of_green_v_win` → `zero_free_all_of_green_v_win` → `zeroFreeAll_of_topG`.
   - `paper.txt:71-75`, `paper.txt:321-324`: `[quotation from the paper omitted]`
   - Code verification: `src/Main.lean:4`; `src/Supplements/Kernels/MainTheorems.lean:7-9`; `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7-11` (`everyCharacter` → `everyCharacter_of_row` → `every_character_of_literature_of_vWin`); `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810-811` (`...every_character_of_literature_of_vWin ... := _root_.UpperTheory.Lit.every_character_of_theta_integrals_local_matching ...`); `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69-73` (`every_character_of_theta_integrals_local_matching ... := _root_.UpperTheory.Top.every_character_of_green_v_win ...`); `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12-18` (`every_character_of_green_v_win` → `zero_free_all_of_green_v_win` → `zeroFreeAll_of_topG`).

3. **(code fact)** On this live route, `zero_free_all_of_green_v_win` builds `TopG` via `forall_goal_of_shape_of_hyps ... (shape_closed_link_n_of_green hG) trivial trivial h`, where `h : Nonempty (HypsAlt ...)` comes from `nonempty_hyps_definite_side_of_closed_bound`, which passes `geoCl anyGeometry`, with `anyGeometry := fun _ _ _ => True`.
   - `paper.txt:17-19`: `[quotation from the paper omitted]`
   - `paper.txt:328-337`, `paper.txt:483-485`, `paper.txt:731-735`.
   - Code verification: `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:14-15`: `h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG ... (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (_root_.UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h) ...`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:59-67` (passes `(geoCl anyGeometry)` at lines 60, 63, 67); `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean:19`: `def anyGeometry : GeoP := fun _ _ _ => True`; `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotGeoClFalse.lean:21-26`: `inductive GeoCl (Γ : GeoP) ... | base ... : Γ D J X → GeoCl Γ D J X ... def geoCl (Γ : GeoP) : GeoP := GeoCl Γ` (consistent with F4).

4. **(code fact)** The geometric witness constructed in `exists_divT` / `geoOver_stages` uses a degenerate model (`geoDegenerate`, `divXFl` with `iMj := 0`, `degHH := 0`, `pn := 0`, `vol := 0`, and seed `x0` with `Lev := Empty`, `Surf := Empty`, `Comp := Empty`), copies row-side lattice fields (`MjH := mjH Z`, `logLam := logLamOf Z hH`, `kapR := fun _ => kapSharp D`) so that `MjAre`, `kapR`, and `LamAre` hold by `rfl` / `HEq.rfl`, and leaves geometric predicates trivially satisfied (`GeoCl.base trivial` / `trivial`).
   - `paper.txt:19-21`: `[quotation from the paper omitted]`
   - `paper.txt:128-135`, `paper.txt:145-220`, `paper.txt:485-488`.
   - Code verification: `src/Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean:241-296` (`geoDegenerate`: `Var := ℕ`, `Fn := fun _ => F`, `H0 := fun _ _ => ⊤`, `Eff/nef/big/bpf/nefA := True`, `vol/arVol/arTop/pn := 0`, `Cl/pts/Met := PUnit`), `Inhabited.lean:829-861` (`divXFl`: `degHH := fun _ _ _ => 0`, `iMj := fun j _ => (0 : ...)`); `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:57-121` (`x0`: `Lev := Empty`, `MjH := mjH Z`, `Comp := fun _ => Empty`, `logLam := logLamOf Z hH`, `kapR := fun _ => kapSharp D`, `Surf := Empty`), `TupPinsOfMuIsW.lean:178-192` (`exists_divT`: `exists_mjHTie ... rfl HEq.rfl, fun _ => rfl, lamAre_of_eq ... rfl`), `TupPinsOfMuIsW.lean:204-209` (`divEx_prov`: `exact ⟨⟨trivial, lamAre_heq hp ht (hX ▸ h4)⟩⟩`). (Note: global zero-call counts for `geoOf_surf`, `GeoTiedP.geoTied`, `GeoTiedP.formsTieX`, etc. across 175,187 files in `paper.txt:276-288` are **NOT VERIFIED** across the whole repository in this logic review; their declarations are verified at `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotLamAreShift.lean:30` and `src/Formalism/LocalToGlobal/LatticeGeometry/GeoTiedP.lean:136,140`.)

5. **(code fact)** In the divisor-family construction (`SetUnipotentTranslate.lean`), `setDiv` overwrites `D.div.h` with the explicit formula `DV.hExpl6 D p.L Y.X C.Csz`, so the height equation `h_eq` holds by `fun _ => rfl`.
   - `paper.txt:21-22`: `[quotation from the paper omitted]`
   - `paper.txt:378-396`, `paper.txt:489-496`.
   - Code verification: `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/SetUnipotentTranslate.lean:25-31` (`def setDiv ... div := { D.div with ... h := h ... }`), `SetUnipotentTranslate.lean:379-400` (`def ht : D.what₂.Word → ℝ := DV.hExpl6 D p.L Y.X C.Csz`, `D := setDiv D (nPrime p.L) p.ht`, `h_eq := fun _ => rfl`) (consistent with F4).

6. **(code fact)** Downstream, `zeroFreeAll_of_topG` consumes the `TopG` object assembled inside `zero_free_all_of_green_v_win` from `h : Nonempty (HypsAlt ...)`; in the released proof term there is no separate, parallel route to `everyCharacter` that bypasses `nonempty_hyps_definite_side_of_closed_bound` and `zero_free_all_of_green_v_win`.
   - `paper.txt:729-743`: `[quotation from the paper omitted]`
   - Code verification: `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12-18`; `src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:26-34` (`zeroFreeAll_of_topG` consumes `h : TopG`).

7. **(logical inference — invalid; see Section 3)** From steps 3–5, the paper infers that the divisor/geometric side and the row/analytic side are forced to be *[quotation from the paper omitted]*, so *[quotation from the paper omitted]*
   - `paper.txt:23-26`: `[quotation from the paper omitted]`
   - `paper.txt:497-500`, `paper.txt:748-750`.

8. **(logical inference — invalid; see Section 2)** From steps 1, 3–5, and 7, the paper infers that the Lean kernel certifies only *[quotation from the paper omitted]*, because *[quotation from the paper omitted]*
   - `paper.txt:29-30`: `[quotation from the paper omitted]`
   - `paper.txt:509-512`: `[quotation from the paper omitted]`

9. **(claim about what a proof requires)** The proof named by the source's identifiers and layout requires an *independent* geometric object (with non-trivial positivity, degree, and height properties) and a substantive identification of its sections with the row-side lattice; proving the two squeeze inequalities for an explicitly chosen formula `hExpl6` (which cancels as a transit variable) is *[quotation from the paper omitted]* and therefore does not supply what the argument requires.
   - `paper.txt:526-534`: `[quotation from the paper omitted]`
   - `paper.txt:573-580`, `paper.txt:584-586`, `paper.txt:744-750`.

10. **(claim about what a proof requires)** *[quotation from the paper omitted]* (`paper.txt:608`), paired with the premise that the geometric input *is* essential to the proof (`paper.txt:748`: `[quotation from the paper omitted]`; `paper.txt:755-757`: `[quotation from the paper omitted]`).

11. **(claim about what a proof requires)** Because the algebraic zero-free step is syntactically downstream of the `TopG` / `HypsAlt` package—so removing that package leaves no remaining route in the released proof term—the vacuity of the geometric component in the package defeats the algebraic step as well.
    - `paper.txt:740-743`, `paper.txt:757-758`: `[quotation from the paper omitted]`
    - `paper.txt:848-852`: `[quotation from the paper omitted]`

12. **(claim about what a proof requires)** Kernel type-checking only checks *[quotation from the paper omitted]* relative to the supplied definitions; *[quotation from the paper omitted]*
    - `paper.txt:845-847`, `paper.txt:853-856`.

13. **(logical inference — main conclusion; fails for formal validity)** From steps 3–12, the paper concludes that the proof is invalid and *[quotation from the paper omitted]*
    - `paper.txt:32`: `[quotation from the paper omitted]`
    - `paper.txt:609`: `[quotation from the paper omitted]`
    - `paper.txt:837-838`: `[quotation from the paper omitted]`

**Summary of where the inference fails.** Steps 1–6 are largely accurate `(code fact)`s (up to unverified global occurrence counts). The conclusion in step 13 fails as a claim of formal invalidity because steps 7 and 8 are factually and type-theoretically false, step 10 begs the question by assuming essentiality instead of applying modus tollens, step 11 mistakes syntactic dependency on a composite record for logical dependence on its vacuous field, and steps 9 and 12 conflate *"executes the named geometric narrative / is human-checkable"* with *"is a valid formal proof of `RiemannHypothesis`."*

---

## 2. What the Kernel Certified vs. [quotation from the paper omitted]

The paper asserts:
- `paper.txt:29-30`: `[quotation from the paper omitted]`
- `paper.txt:509-512`: `[quotation from the paper omitted]`

**Is this an accurate description of what the kernel certified?**
No. Under F1–F3, this description is **false** as a statement about Lean's type theory and kernel certification.

1. **Exact type of the certified term.**
   - In `src/Main.lean:4`: `theorem riemannHypothesis : RiemannHypothesis := rhOfAll`.
   - In `src/Challenge.lean:19`: `theorem riemannHypothesis : RiemannHypothesis := by sorry`, compared against `Main` via `comparator.json:2-10` (`"challenge_module": "Challenge", "solution_module": "Main", "theorem_names": ["riemannHypothesis", ...]`).
   - By F1, the type of `riemannHypothesis` is Mathlib's constant `RiemannHypothesis : Prop` (Mathlib pinned at `v4.33.1`, commit `0df444a360eaa60ab8c11dca51a86af692955474`, `lake-manifest.json:6-15`), with no hypotheses. Its unfolding in `src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:5-7,61-62` (`unfold RiemannHypothesis; intro s hs htriv hs1 ...`) confirms it is the universally quantified proposition about non-trivial zeros of `riemannZeta` having `s.re = 1 / 2` (matching `RiemannZetaZerosOnLine` in `src/Statements.lean:3-4`; the verbatim Mathlib file `Mathlib/NumberTheory/LSeries/RiemannZeta.lean` is not inside `src/` and is therefore **NOT VERIFIED** directly here, though F1 fixes it).
   - A search of `decls.txt` finds zero `def`, `abbrev`, or `theorem` declarations named `RiemannHypothesis` in `src/` (only compound names like `RiemannHypothesisOfHalfLinks` at `src/Formalism/HalfLinks/Statement.lean:144`, and the two `theorem riemannHypothesis : RiemannHypothesis` declarations in `src/Challenge.lean:19` and `src/Main.lean:4`).
   - Crucially, the certified type is `RiemannHypothesis`, **not** the equality proposition `RiemannHypothesis = RiemannHypothesis` (whose trivial proof is `rfl : RiemannHypothesis = RiemannHypothesis`). In Lean's dependent type theory, a term `t` of type `T` is *[quotation from the paper omitted]* (i.e., checkable by `rfl`) only when `T` reduces to `a = b` with `a` and `b` definitionally equal. `RiemannHypothesis` is not an equality type at all, nor is it definitionally equal to `True`; no `rfl` term can inhabit `RiemannHypothesis`.

2. **Can definitions made inside the development change the meaning of Mathlib's `RiemannHypothesis`?**
   - **No.** In Lean's kernel (Calculus of Inductive Constructions), user definitions (`anyGeometry`, `geoDegenerate`, `hExpl6`, `setDiv`, `HypsAlt`, `TopG`, etc.) are **conservative definitional extensions**. They add new constants and reduction rules for those new constants; they cannot modify any previously declared constant in Mathlib (`RiemannHypothesis`, `riemannZeta`, `Complex`, `ℝ`) or alter its definitional unfolding.
   - A closed proof term `t : RiemannHypothesis` using only the three standard axioms `propext`, `Quot.sound`, `Classical.choice` (F2) and accepted by Lean's kernel and independent kernels (F3) certifies that `RiemannHypothesis` is provable in Lean's base logic plus Mathlib's definitions. Because every auxiliary definition introduced inside `src/` can in principle be unfolded (delta-reduced) out of the proof term without touching the target type `RiemannHypothesis`, no combination of `fun _ _ _ => True` predicates or `rfl` record equalities in intermediate definitions can ever forge a closed proof of a false Mathlib proposition.
   - The phrase `[quotation from the paper omitted]` (`paper.txt:30,511`) therefore conflates two entirely different situations: (i) proving a theorem whose *statement* uses custom/degenerate definitions (which could indeed be tautological), and (ii) proving a theorem whose *statement* uses only Mathlib's fixed definitions via *auxiliary internal definitions* (which cannot weaken or tautologize the conclusion).

---

## 3. Consistency of the Paper's Two Descriptions of the Squeeze Inequality vs. the Code

The paper gives two incompatible accounts of the inequalities in `WordFacts`:

- **Account A (Abstract, Section 8 opening, Section 10):**
  - `paper.txt:24-26`: `[quotation from the paper omitted]`
  - `paper.txt:498-500`: `[quotation from the paper omitted]`
  - `paper.txt:749-750`: `[quotation from the paper omitted]`

- **Account B (Section 7 and Section 8 [quotation from the paper omitted]):**
  - `paper.txt:427-432`: `[quotation from the paper omitted]`
  - `paper.txt:515-524`: `[quotation from the paper omitted]`
  - `paper.txt:566-571` (table): marks `"height = formula"` as `"yes, by rfl"`, but marks `"the two inequalities for the formula"` as `"yes"` (not `"by rfl"`).

**Are these two descriptions consistent?**
**No.** They contradict each other. An inequality that *[quotation from the paper omitted]* has the form $X \le X$ (discharged by `le_rfl` or `rfl`) and yields no constraint. By contrast, Account B describes two non-reflexive inequalities $A \le h$ and $\mu + h - F_o \le \mathrm{MAIN} + \mathrm{error}$ linking distinct analytic quantities (`htMap` of the pairing, `muDual`, `Fo`, `MAIN`), proved by `divClausesR_of` from ~40 matrix/covolume/valuation estimates.

**Which description matches the code?**
**Account B matches the code; Account A is contradicted by the code.**

1. **`RecBridge.lean:128-155`:**
   - `src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:128-133` defines `WordFacts`:
     ```lean
     def WordFacts {D : D7} (L : SizeData₂ D) (C Cabs : ℝ) (u : D.what₂.Word) : Prop :=
       (D.div.Nu u).L.map ((D.div.Bk u).restrictScalars (𝓞 D.what₂.LL)) ≤ D.div.cc ∧
       (D.div.Bk u ≠ 0 → Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X D.div.RR.dualB D.div.RR.dualX (D.div.Bk u) ≤
         D.div.h u) ∧
       D.div.RR.muDual + D.div.h u - L.Fo ≤ L.MAIN u +
         C * (D.host.TT.card : ℝ) * L.sc.a * L.La + C * (D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)
     ```
     Neither inequality compares a quantity with itself: the first compares the map height `Formalism.HN.htMap ... (D.div.Bk u)` against `D.div.h u`, and the second compares `D.div.RR.muDual + D.div.h u - L.Fo` against `L.MAIN u + ...`.
   - `src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:135-154` proves `wordFacts_of` from three explicit clause hypotheses (`c1`, `c2 : B ≠ 0 → ht ≤ hu - kap`, `c3 : muC - kap + hu - Fo2 ≤ rhs`) plus five ties (`tHt`, `tMu`, `tH : hu - kap = D.div.h u`, `tFo`, `tR`):
     ```lean
     refine ⟨oneMap_of_coord ... c1, fun hne => ?_, ?_⟩
     · rw [tHt, ← tH]
       exact c2 (ne_zero_of_coord eN eR (D.div.Bk u) B hB hne)
     · rw [← tMu, ← tH, ← tFo]
       linarith
     ```
     Neither inequality holds by `rfl` or `le_rfl`.

2. **`ConstantGeTwentyEight.lean:105-250` (and `26-104`):**
   - `DivInputsR` (`src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean:105-109`) extends `DivInputs0R` (`ConstantGeTwentyEight.lean:26-103`, 37 fields) with `val2` (`line 108-109`), totaling 38 fields: lattice/frame conditions (`Nu_lat`, `sg_fin`, `Xc_unit`, `X0`, `base_matrix_det_unit`), matrix chain and operator-norm bounds (`ch`, `hn`, `nP`, `cb`, `nKcb`, `eig6`), local basis / valuation / covolume bounds (`eb`, `heb`, `bi`, `bLG`, `biv`, `borderedMinorImage`, `twisted_third_sum_le`, `L3main`, `errB`), passage parameters (`de0`, `deQ`, `Q1`, `Qb`, `la_le`, `constant_ge_twenty_eight`), and `val2`.
   - `DivClausesR` (`ConstantGeTwentyEight.lean:111-121`) states four clauses, including the operator-norm bound `(∃ cu : InfinitePlace K → ℝ, ... (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (cu v) = R.hu - meanLog P.cols.κ)` (`lines 114-117`, which feeds `htMap_le_of_bound` in `RecBridge.lean:161-171,202`) and the upper bound `P.cols.muCC - meanLog P.cols.κ + R.hu - 2 * FoOfR P ≤ R.rhs` (`line 118`).
   - `divClausesR_of` (`ConstantGeTwentyEight.lean:184-248`) proves these clauses substantively:
     - Clause 2 (`lines 194-209`): for `P.cols.col.B u ≠ 0`, calls `height_chain_atR` (`lines 123-182`, which calls `complex_height_cast_at` on `I.ch`, `I.nP`, `nK`, and `S.log_eigenvalue_sum_le_min`) together with `I.hn.le_hu (∑ j, N.l6 j) I.eig6` (`src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:113-123`, calling `Formalism.DivisorInequality.height_bound_at_set`), finishing via `linarith [Hm, h1]`. (When `B u = 0`, `opNormAt` is 0; in `WordFacts` this case is already excluded by `D.div.Bk u ≠ 0 → ...`.)
     - Clause 3 (`lines 211-245`): invokes `P.base.boundsMu` (`line 211`), `P.extra.passage` (`line 216`), `I.Qb` (`line 227`), `I.L3main` (`line 242`), `I.errB` (`line 245`), and `R.divIneq` (`DivisionHeightBoundStatement.lean:131-180`, invoking `Formalism.DivisionValues.divIneqRecord`).
   - What actually holds by `rfl` is *only* the assignment `h_eq := fun _ => rfl` (`SetUnipotentTranslate.lean:400`) equating the field `D.div.h u` to `hExpl6 ...`, which is distinct from both inequalities in `WordFacts`. Account A conflates that definitional equality with the two inequalities proved by `divClausesR_of`.

---

## 4. Section 8 ([quotation from the paper omitted])

In Section 8 (`paper.txt:514-580`), the paper acknowledges that adding the two inequalities cancels `h` and produces a comparison between the pairing and the main term established by `divClausesR_of` (`paper.txt:515-524`), and then objects:
- `paper.txt:526-527`: `[quotation from the paper omitted]`
- `paper.txt:536-539`: `[quotation from the paper omitted]`
- `paper.txt:547-552`: `[quotation from the paper omitted]`

Downstream in the code, `D.div.h` indeed functions algebraically as an intermediate real-valued shift: `sFrame D.div.Nu D.div.h` is a rank-weighted average of `(D.div.Nu u).mu - D.div.h u` (`src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean:568-569`: `sFrame D.div.Nu D.div.h * (∑ u, ((D.div.Nu u).rank : ℝ)) = ∑ u, ((D.div.Nu u).rank : ℝ) * ((D.div.Nu u).mu - D.div.h u)`), `Frame_at` bounds `sFrame D.div.Nu D.div.h - error ≤ D.div.RR.muDual` (`src/Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean:188-193`, using `htMap ... (D.div.Bk u) ≤ D.div.h u` via `frameReal_at_of` at `TopDensityNGeSixteen.lean:679-683`), and `data_DIV` uses `D.div.RR.muDual + D.div.h u - Fo ≤ L.MAIN u + ...` (`QuadraticLogDerivCongr.lean:580-585`).

1. **Is "a valid derivation that is not the one suggested by the identifier names" a ground for calling a formal proof invalid?**
   - **No.** Logical validity of a formal proof depends solely on whether the proof term obeys the inference rules of the logic from permitted axioms to the stated target type. Identifier names (`h`, `div`, `DivX`, `geo`) are completely semantically inert in Lean's kernel; systematically alpha-renaming them changes nothing about validity. A proof whose identifiers suggest a geometric narrative while its actual Lean terms execute an analytic/matrix-theoretic derivation is **misleadingly named** (a flaw in exposition, documentation, or mathematical transparency), not **logically invalid**.

2. **Does proving $A \le B$ and $B \le C$ for an explicitly defined $B$ require $B$ to be "independent" or "geometric" for $A \le C$ to follow?**
   - **No.** By transitivity (and additive cancellation) of $\le$ on $\mathbb{R}$, for *any* $A, B, C \in \mathbb{R}$, once both $A \le B$ and $B \le C$ are proved, $A \le C$ follows unconditionally—whether $B$ is derived from geometry, defined by an explicit formula in the same variables as $A$ and $C$, or *"chosen to fit"* (`paper.txt:544-548`).
   - Choosing an explicit interpolant $B$ specifically so that both $A \le B$ and $B \le C$ can be proved is a standard, completely valid proof technique across analysis and number theory. Calling this circular (`paper.txt:530,756`) is a fallacy: defining $B$ does **not** make $A \le B$ or $B \le C$ true. If $A \le C$ were false (i.e., $C < A$), no real number $B$—however defined—could satisfy both $A \le B$ and $B \le C$. Hence proving both inequalities for an explicitly chosen `hExpl6` genuinely proves the resulting bound between the pairing/slope data and `MAIN + error`, even though it proves nothing about any geometric height of a Shimura variety.

---

## 5. Appendix A, the "Remove the Package" Test, and Universal Quantification

Appendix A states the kernel objection (`paper.txt:842-844`: `[quotation from the paper omitted]`) and replies:
- `paper.txt:848-852`: `[quotation from the paper omitted]`
- Similarly, Section 10 (`paper.txt:742-743`): `[quotation from the paper omitted]`

1. **Does the kernel objection assume that removing the vacuous inputs leaves a separate independent derivation already written in the codebase?**
   - **No.** The kernel objection makes a proof-theoretic claim about the *existing* proof term: because the existing closed term already typechecks at type `RiemannHypothesis`, any `True` / `trivial` / degenerate field inside it carries zero deductive weight in establishing `RiemannHypothesis`. It does **not** assume that a second, parallel declaration avoiding `nonempty_hyps_definite_side_of_closed_bound` or `zero_free_all_of_green_v_win` already sits in the repository. It claims that the single existing derivation is already valid and that its geometric slots are logically eliminable (non-essential).

2. **Is [quotation from the paper omitted] a valid test of soundness?**
   - **No.** That test conflates *syntactic dependency on a composite wrapper/bundle* with *logical dependency on a vacuous field inside it*. Consider a trivial sound derivation:
     `structure Wrap (P : Prop) where dummy : P; real : 2 + 2 = 4`
     `theorem t : 2 + 2 = 4 := (Wrap.mk (P := True) trivial rfl).real`
     Deleting `Wrap.mk` (the package) leaves `t` with no remaining route and breaks compilation—not because `t` is unsound or depends logically on `dummy : True`, but because `Wrap` bundles `dummy` alongside the substantive field `real`. Likewise, `HypsAlt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean:22-90`) bundles ~45 substantive analytic/automorphic/lattice fields (`𝒜`, `σ`, `hEx`, `hRB`, `hDivG`, `rRows`, `aPt0`, ..., `nRest`) alongside the route that instantiated `Γ := geoCl anyGeometry`. Deleting the `HypsAlt` / `TopG` constructor breaks `zeroFreeAll_of_topG` because `zeroFreeAll_of_topG` needs the *substantive* fields in `TopG`, not because it uses `anyGeometry`.

3. **Comparison with the "replace by an arbitrary input" test (universal quantification / parametricity).**
   - The sound logical test for whether downstream consumers actually use a geometric assumption is whether those consumers are **universally quantified** over the input (so replacing the vacuous input by an arbitrary parameter of the same type leaves every consumer's proof intact). Checking the actual statements on the live route shows that **every consumer on the route IS universally quantified** over the inputs the paper calls vacuous:

   - **Shape consumer (`forall_goal_of_shape_of_hyps`)** — `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ShapeOf.lean:31-32`:
     ```lean
     theorem GlobalTheory.Fc.forall_goal_of_shape_of_hyps : ∀ (V NR : Prop) (N : FamClass → Prop) (G : Prop),
       _root_.GlobalTheory.Fc.TopShapeAlt V NR N G → V → NR →
       _root_.GlobalTheory.Fc.HypsAlt N _root_.GlobalTheory.Fc.DefiniteSideCondition → G := ...
     ```
     It is universally quantified over arbitrary propositions `(V NR : Prop)`. Moreover, the shape supplied at `TopPlug.lean:15` is `shape_closed_link_n_of_green` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:33-34`):
     ```lean
     theorem UpperTheory.Top.shape_closed_link_n_of_green : GlobalTheory.GLq.Green →
       _root_.GlobalTheory.Fc.TopShapeAlt True True (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) UpperTheory.Top.TopG := by
       intro hGreen 𝒜 cT hEx sel hduty ... hLit hVC hWu ... hServ nR nRest ...
     ```
     In `TopShape.lean:35-55`, neither `hVC : True` nor `nR : True` (corresponding to `hVC : V` at `TopShapeAlt.lean:50` and `nR : NR` at `TopShapeAlt.lean:84`) is referenced anywhere in the proof body. The two `trivial` arguments in `TopPlug.lean:15` simply discharge two unused generic slots of `TopShapeAlt`.

   - **Consumers taking `(Γ : GeoP)` called inside `nonempty_hyps_definite_side_of_closed_bound` (`SiegelEisensteinSecondTermHypotheses.lean:59-68`) and `hypotheses_nonempty_of_unramified_exponents_alt` (`HypothesesNonemptyOfUnramifiedExponents.lean:49-61`):**
     - `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/OpenAndLinkedOfStrongerExtension.lean:28`:
       `theorem open_and_linked_of_stronger_extension_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), ...`
     - `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/RowFunAtGridA.lean:32`:
       `theorem rowFun_at_gridA_alt : ... → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), ...`
     - `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkedBundlesL3OfOpen.lean:31`:
       `theorem linked_bundles_l3_of_open_alt : ... → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), ...`
     - `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkROfIsLinked.lean:50`:
       `theorem allRows_of_open0_alt : ... → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (NN : FamClass → Prop), ...`
     - `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/NonemptyHypsOfAllRows.lean:19`:
       `theorem nonempty_hyps_of_allRows_alt : ... → ∀ (KP : ...) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) (N : FamClass → Prop) (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType), ... → Nonempty (_root_.GlobalTheory.Fc.HypsAlt N DR)` (universally quantified over arbitrary slot predicates `Q Q'`, and `HypsAlt` in `ThirdPlaceSeries/Hyps.lean:22-90` does not even mention `Γ : GeoP`).
     - Similarly upstream, `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ThirdLevelOfGoodTwists.lean:24,28`:
       `def levelThreeIndependentOfChoices {N : NExt hL} {S S' : SExt} {Γ Γ' : GeoP} {Z : w.Lt} (v : Lv3 (prmR N S Γ).s K w Z) : Lv3 (prmR N S' Γ').s K w Z`
       `theorem third_level_of_good_twists {S : SExt} {Γ : GeoP} (h : Has3 (prmR (NEg hL) S Γ).s K B f T w) : Has3 (prmR (NEb hL) S Γ).s K B f T w`

   - **Polarity contrast with producers:** Where `anyGeometry` is *fixed* rather than universally quantified is strictly on the **producer** (existential-witness) side—`divEx_prov (𝒮 : Slots) (hOx : 𝒮.Ox = OX anyGeometry) : DivEx 𝒮` (`TupPinsOfMuIsW.lean:204`), `parametersOfDependence` (`Prm1.lean:20-21`), `large_unramified_exponent_bundles_exist_alt` (`MemberBundlesLargeUnramifiedExponents.lean:69`), and `hypotheses_nonempty_of_unramified_exponents_alt` (`HypothesesNonemptyOfUnramifiedExponents.lean:41`). Logically, when every consumer proves `∀ Γ : GeoP, Witness Γ → Goal`, instantiating `Γ := geoCl anyGeometry` on the producer side to construct `Witness (geoCl anyGeometry)` is completely sound and directly demonstrates that `Goal` (`Nonempty (HypsAlt ...)`, hence `TopG`, hence `RiemannHypothesis`) requires **no** geometric property from `Γ`.

---

## 6. Logical Consequence of [quotation from the paper omitted]

In Section 9, the paper writes:
- `paper.txt:608`: `[quotation from the paper omitted]`

Formalize the three relevant propositions:
- $V$: the released closed Lean proof term is a valid proof of `RiemannHypothesis`.
- $T$: the geometric slot in that proof term is trivially discharged (`anyGeometry := fun _ _ _ => True`, `GeoCl.base trivial`, `geoDegenerate`, `h_eq := fun _ => rfl`).
- $E$: a substantive geometric argument is essential to the validity of the proof.

The paper's premise states the incompatibility $\neg(V \land E \land T)$—equivalently, conditional on $V$, $\neg(E \land T)$, i.e., $T \to \neg E$ and $E \to \neg T$.

Now combine this premise with the established facts:
1. By F4 (and verified in `OverIx.lean:19`, `TupPinsOfMuIsW.lean:204-209`, `SetUnipotentTranslate.lean:400`), **$T$ is an undisputed code fact**.
2. Therefore, from $\neg(V \land E \land T)$ and $T$ alone, logic yields the disjunction:
   $$\neg V \;\lor\; \neg E$$
   (either the proof is invalid, **or** the geometric argument is not essential).
3. Now bring in F1–F3: the closed term has type Mathlib's `RiemannHypothesis`, uses only `{propext, Quot.sound, Classical.choice}`, and was checked by Lean's kernel and several independent kernels. Modulo the soundness of those kernels, those standard axioms, and Mathlib's definition of `RiemannHypothesis`, F1–F3 establish **$V$**.
4. From $V$, $T$, and $\neg(V \land E \land T)$, **modus tollens strictly forces $\neg E$: the geometric argument is NOT essential to the proof of `RiemannHypothesis`.**

The paper reaches the opposite conclusion ($\neg V$: `"the proof is invalid"`, `paper.txt:609`) only by **assuming $E$ without proof**—asserting from the identifiers and intended mathematical story that the proof *must* use an independent geometric height (`paper.txt:584-585`, `paper.txt:748`: `"The independence of the geometric side is essential"`, `paper.txt:755-757`: `"The geometry is therefore not unused scaffolding"`). That is circular (begging the question): in a kernel-checked closed proof, the fact that a slot can be trivially discharged *refutes* the claim that the slot was essential; it does not refute the proof.

---

## 7. Steelman: How the Paper's Observations Could Indicate a Genuine Defect, and What Evidence Exists

Even for a kernel-checked closed theorem `theorem riemannHypothesis : RiemannHypothesis`, formal verification rests on a trusted computing base (TCB) and on statement adequacy. Extensive vacuous or degenerate scaffolding (`anyGeometry`, `geoDegenerate`, `h_eq := rfl`) is legitimately a **heuristic warning sign** prompting scrutiny of every link in that TCB. Below is every mechanism by which a genuine defect could still exist, what evidence would settle it, and whether the paper supplies such evidence:

| Potential genuine defect | How it could invalidate the claim despite a kernel check | Evidence that would settle it | Does the paper offer such evidence? |
|---|---|---|---|
| **1. Wrong target statement (local shadowing / hidden hypotheses)** | `Main.lean` defines or imports a shadowed/weakened `RiemannHypothesis` or adds contradictory implicit parameters. | Export-level type comparison against `Challenge.lean` (`comparator.json:2-10`); inspecting all local declarations of `RiemannHypothesis`. | **No.** The paper agrees the theorem inhabits Mathlib's `RiemannHypothesis` with no hypotheses (`paper.txt:14-15,50,842`). Ruled out by F1 (and 0 local definitions of `RiemannHypothesis` in `decls.txt`). |
| **2. Bug in Mathlib's definition of `RiemannHypothesis` (or `riemannZeta`, `ℂ`, `ℝ`)** | Mathlib `v4.33.1`'s `RiemannHypothesis` is accidentally vacuously true or inequivalent to classical RH (e.g., wrong trivial-zero exclusion, integer `1/2 = 0`, faulty `riemannZeta` analytic continuation). | Line-by-line audit of Mathlib `v4.33.1` (`0df444a3...`, `lake-manifest.json:10`) for `RiemannHypothesis`, `riemannZeta`, `completedRiemannZeta`, and verifying `1/2 : ℝ` and classical equivalence. (Mathlib source itself is **NOT VERIFIED** locally here; `RhOfRight.lean:6-62` corroborates `1/2 : ℝ` and the functional equation.) | **No.** The paper cites Mathlib `v4.33.1` (`paper.txt:865-866`) and alleges no defect in Mathlib's definitions. |
| **3. Soundness bug in Lean's kernel (or a shared bug across kernels)** | Degenerate structures, `HEq`, `set_option genInjectivity false` (`Hyps.lean:20`), `set_option genSizeOfSpec false` (`Hyps.lean:21`), or 17.4M lines of code trigger an unknown kernel bug deriving `False`, with the vacuous geometry acting as a symptom or smokescreen. | Replaying the full exported proof term in multiple independent kernels (`leanchecker-paranoid`, `nanoda`, `con-leche`, `con-ron` in `comparator.json:12-17`); or isolating a standalone reproducer of `False` or a specific declaration rejected by a sound kernel. | **No.** `paper.txt:765-768` explicitly notes that a Comparator mismatch under Lean 4.36.0 / `nanoda` *[quotation from the paper omitted]* and exhibits no kernel bug or proof of `False`. F3 states independent kernels re-checked the export. |
| **4. Unauthorized axiom / `sorry` / `native_decide` / `unsafe` / `opaque` / metaprogramming bypass** | An unsound axiom or kernel bypass (`skipKernelTC`, `implemented_by`, `extern`, tampered environment) enters the transitive dependency cone. | Kernel-level `#print axioms` / Comparator axiom check against `{propext, Quot.sound, Classical.choice}` (`comparator.json:11`), plus auditing metaprogramming (`verification/NOTES.md:47-49` notes `addDecl` in `CutCptCopy.lean`, which still invokes kernel checking). | **No.** The paper explicitly rules this out (`paper.txt:15-16`, `814-815`: `[quotation from the paper omitted]`). Ruled out by F2. |
| **5. Foundational inconsistency of CIC + standard axioms** | Lean's type theory plus `propext`, `Quot.sound`, `Classical.choice` is inconsistent, making every proposition provable. | Exhibiting a closed proof of `False` from those axioms alone. | **No.** The paper makes no such claim. |
| **6. Source / checked-artifact mismatch** | The `.olean` or export checked by independent kernels differs from the published source archive (or pins a tampered Mathlib fork). | Reproducible clean build from the SHA-256-verified source archive (`paper.txt:805-806`, `verification/NOTES.md:12-18`) against upstream Mathlib `v4.33.1` (`lake-manifest.json:6-15`), followed by independent kernel replay of the freshly built export. | **No.** The paper audits the same mirror (`paper.txt:805-806,862-863`) and alleges no build/artifact discrepancy. |

**Steelman verdict:** While the paper's code findings are a strong heuristic trigger to audit mechanisms 1–6 rigorously, **none** of the paper's findings actually establishes any of mechanisms 1–6. Given F1–F3, the steelman fails to bridge the gap from *"vacuous geometric layer"* to *"invalid closed proof of `RiemannHypothesis`."*

---

## 8. Legitimate, Weaker Conclusions That Do Follow

Setting formal validity aside, the paper's source audit establishes several genuine, mathematically and methodologically important conclusions:

1. **The formalization does not execute the geometric / Arakelov-height proof suggested by its names and architecture.**
   - On the live `everyCharacter` route, the geometry predicate is `anyGeometry : GeoP := fun _ _ _ => True` (`OverIx.lean:19`), wrapped in `geoCl anyGeometry` (`SiegelEisensteinSecondTermHypotheses.lean:60,63,67`; `Prm1.lean:21`), and discharged by `trivial` in `divEx_prov` (`TupPinsOfMuIsW.lean:204-209`). Furthermore, `divEx_of_ox` (`TupPinsOfMuIsW.lean:211-213`) accepts three named literature hypotheses (`RayField`, `PrincipalIdealSt`, `CMCurveGoodOutsidePrimeSt`) and discards all three (`fun _ _ _ 𝒮 hOx => divEx_prov 𝒮 hOx`).
   - The geometric witness `divXFl` (`Inhabited.lean:829-861`) uses `geoDegenerate` (`Inhabited.lean:241-300`: `Var := ℕ`, `Fn := fun _ => F`, `H0 := fun _ _ => ⊤`, `Eff/nef/big/bpf/nefA := True`, `vol/arVol/arTop/pn := 0`), `degHH := 0` (`line 856`), and the zero map `iMj := 0` (`line 860`), grafted onto seed `x0` with `Lev/Comp/Surf/SurfFp/QPl := Empty` (`TupPinsOfMuIsW.lean:59,95,105,117,120`). For this model, `degHH_def` (`src/Formalism/SharpRestriction/Divisibility/PlaceRankTwoOne.lean:142-146`) has an unsatisfiable norm premise (`0 = r σ ^ 2` with `0 < r σ`), and `D.div.h` is assigned directly to `DV.hExpl6` via `setDiv` with `h_eq := fun _ => rfl` (`SetUnipotentTranslate.lean:25-31,379-400`).

2. **What is—and is not—actually formalized on the live route.**
   - *Not used on the live route:* No non-trivial Shimura-variety geometry, no second-Chern-number or Arakelov height derivation, and no substantive embedding of Hermitian lattices into geometric sections (`iMj := 0`) contribute to `riemannHypothesis`. (Likewise, `shape_closed_link_n_of_green` at `TopShape.lean:33-55` instantiates `V := True, NR := True` and ignores both `hVC` and `nR`.)
   - *Actually active on the divisor-link segment:* As verified in `RecBridge.lean:128-243` and `ConstantGeTwentyEight.lean:184-248`, `WordFacts` / `DivClausesR` are established purely from row-side matrix/operator-norm/covolume/valuation bounds (`DivInputsR`) via the explicit real formula `hExpl6` (`KernelPlaceMeanBound.lean:25-27`). Consequently, any informal narrative claiming that this formalization proves RH by constructing an independent geometric height on a Shimura variety misstates what the Lean proof actually does.

3. **Severe deficit in explanatory value, maintainability, and human auditability—and a roadmap for extraction.**
   - In a 17.4M-line, 175,187-file release (`verification/NOTES.md:25`), carrying an extensive degenerate geometric layer (`geoDegenerate`, `mdlJunk`, `anyGeometry`, `GeoTiedP`, unused `geoOf`) alongside the active analytic/automorphic core obscures the true mathematical argument.
   - Appendix A's final normative point (`paper.txt:855-856`: *[quotation from the paper omitted]*) has legitimate epistemological force when separated from the invalid claim of formal unsoundness: kernel acceptance establishes formal provability (modulo TCB), not human mathematical understanding. Ironically, by identifying which geometric structures are degenerate and universally quantified over, the paper's code observations provide a valuable blueprint for **pruning** the vestigial geometric scaffolding to isolate and understand the genuinely active non-geometric proof inside the release.

---

## Overall Assessment

Nielsen's paper documents real, verifiable code facts: `anyGeometry := fun _ _ _ => True`, `geoDegenerate`, `iMj := 0`, `divEx_of_ox` discarding three named hypotheses, and `h_eq := fun _ => rfl` via `setDiv` all lie in the live dependency cone of `riemannHypothesis` (`OverIx.lean:19`, `Inhabited.lean:241-300,860`, `TupPinsOfMuIsW.lean:204-213`, `SetUnipotentTranslate.lean:379-400`).
However, the paper's central inference—that the release therefore *[quotation from the paper omitted]* (`paper.txt:32,838`)—is **logically invalid** given F1–F3.
First, the claim that the kernel certifies only *[quotation from the paper omitted]* (`paper.txt:29-30,510-512`) is type-theoretically false: local definitions are conservative and cannot alter Mathlib's `RiemannHypothesis`, nor can `rfl` inhabit it (`src/Main.lean:4`, `RhOfRight.lean:5-62`).
Second, the paper contradicts itself on the squeeze inequality: its Abstract/Section 8 claim that the inequality *[quotation from the paper omitted]* (`paper.txt:24-26,498-500`) is refuted by its own Section 7 (`paper.txt:427-432`) and by `RecBridge.lean:128-155` and `ConstantGeTwentyEight.lean:105-248`, where `divClausesR_of` proves two non-reflexive inequalities from 38 matrix, covolume, and valuation inputs.
Third, Section 8's objection that an explicitly defined transit variable `hExpl6` is *[quotation from the paper omitted]* (`paper.txt:526-527`) confuses misleading identifier names with logical invalidity; proving $A \le B$ and $B \le C$ validly implies $A \le C$ for any real $B$.
Fourth, Appendix A's *"remove that package"* test (`paper.txt:742-743,848-852`) mistakes syntactic dependency on a composite record for logical dependence on its vacuous field; in fact, the live consumers (`forall_goal_of_shape_of_hyps` at `ShapeOf.lean:31-32`, `open_and_linked_of_stronger_extension_alt`, `rowFun_at_gridA_alt`, `linked_bundles_l3_of_open_alt`, `allRows_of_open0_alt`, and `nonempty_hyps_of_allRows_alt`) are universally quantified over `(V NR : Prop)` and `(Γ : GeoP)` / `(Q Q' : V4.Slot)`.
Fifth, combining *[quotation from the paper omitted]* (`paper.txt:608`) with F1–F4 yields by modus tollens that **the geometric argument is not essential**, not that the proof is invalid; the paper begs the question by assuming essentiality.
Sixth, while vacuous scaffolding is a legitimate red flag to audit the TCB (Mathlib's statement, kernel soundness, axioms, build/export match), the paper offers no evidence for any TCB failure and concedes F1–F2 (`paper.txt:14-16,765-768,814-815`).
What *does* legitimately follow from the paper's audit is substantial but weaker: the formalization does **not** carry out an Arakelov/Shimura-variety geometric height proof, its geometric naming severely misrepresents its active argument, and the geometric layer is vestigial scaffolding.
As an attack on formal validity, the paper's argument fails at Steps 7, 8, 10, and 11 (Section 1).
As a diagnostic of what is and is not formalized, it succeeds in showing that any real mathematical proof certified by the release resides entirely in the non-geometric analytic, automorphic, and matrix-theoretic core rather than in the degenerate geometric layer.
Consequently, the proper response to Nielsen's findings (assuming F1–F3 hold) is not to declare `riemannHypothesis` invalid, but to strip the unused geometric scaffolding and extract the actual non-geometric proof for human mathematical verification.
