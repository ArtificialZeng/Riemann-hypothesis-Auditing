# Audit Report G: The Height and the Two Inequalities (Nielsen Sections 7 & 8)

**Repository audited:** `~/rh-audit/src/omega` (Lean 4 source under `src/`, read-only inspection without Lean execution).  
**Paper reviewed:** J. L. Nielsen, *[quotation from the paper omitted]* (`~/rh-audit/nielsen/paper.txt`, Sections 7–8, lines 318–581).

---

## Item 1: Sites Constructing the Height Equation `h_eq`

**Verdict: PARTLY TRUE**

The claim correctly identifies the **sole origin** of the height equation `div.h u = hExpl6 ...`—it is installed by `fun _ => rfl` in `SetUnipotentTranslate.lean:400` after overwriting `div.h` via `setDiv`—and correctly identifies one copying site (`FamRaise.lean:36`). However, the claim's list of four sites is **factually wrong**: the two sites cited in `DisjointSplitLevelPlaces.lean` (`:331` and `:501`) are **not** the height equation at all (they construct an unrelated adelic group factorization `RawDat.h_eq : h = hP * k`), while **two genuine propagation sites** (`ExistsFamPOfKits.lean:139` and the record update in `LinkNOfGd.lean:17-30`) are missed.

### Where the height equation field `h_eq` is declared

1. `ExtraAt.h_eq` in `src/Formalism/SharpRestriction/InertJacobiLevels/AsmIface.lean:157-164`:
```lean
structure ExtraAt (C : FC) {D : D7} (L : SizeData₂ D) (gatT : GatTies D) (Gx : G.Inst D L) (Gy : G.LatInst D) where
  ...
  h_eq : ∀ u, D.div.h u = DV.hExpl6 D L X C.Csz u
```
2. `FamP.h_eq` in `src/Formalism/SharpRestriction/ParConsts.lean:73`:
```lean
  h_eq : ∀ x, x1 < x → ∀ (i : Ix x) u, (D x i).div.h u = DV.hExpl6 (D x i) (L x i) (X x i) Csz u
```

### The sole origin site (by `fun _ => rfl`)

In `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/SetUnipotentTranslate.lean:25-31`, `setDiv` overwrites `D.div.h` with an arbitrary function `h`:
```lean
@[reducible] def setDiv (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : D7 :=
  { D with
    div := { D.div with
      Nu := fun u => { D.div.Nu u with L := N u }
      h := h
      HH := max 1 (sFrame (fun u => { D.div.Nu u with L := N u }) h + D.div.RR.muMax)
      HH_ge := le_max_right _ _ } }
```
Then `LedPart.pt` (`SetUnipotentTranslate.lean:379-401`) sets `ht` to `DV.hExpl6`, installs it with `setDiv`, and discharges `ExtraAt.h_eq` by `fun _ => rfl`:
```lean
def ht : D.what₂.Word → ℝ := DV.hExpl6 D p.L Y.X C.Csz

def pt : Pt C where
  D := setDiv D (nPrime p.L) p.ht
  ...
  xa :=
    { ...
      h_eq := fun _ => rfl
      ... }
```
An exhaustive `git grep -n -w -F 'h_eq' src/` (98 occurrences across `src/`) confirms that `SetUnipotentTranslate.lean:400` is the **only** site in the codebase where `ExtraAt.h_eq` or `FamP.h_eq` is proved from scratch.

### False citations in `DisjointSplitLevelPlaces.lean`

In `src/Formalism/LocalToGlobal/IndefiniteReal/DoubleCosetOperators/DisjointSplitLevelPlaces.lean:264`, `RawDat.h_eq` is a completely unrelated adelic group factorization:
```lean
  k_mem : k ∈ S.KV
  h_eq : h = hP * k
```
Both `DisjointSplitLevelPlaces.lean:331` (`h_eq := d.h_eq`) and `DisjointSplitLevelPlaces.lean:501` (`h_eq := rfl`) populate `RawDat.h_eq`, **not** `ExtraAt.h_eq` or `FamP.h_eq`.

### All actual sites propagating `h_eq` (3 sites, 2 missed by the paper)

1. **`famOfKits`** in `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsFamPOfKits.lean:139` *(missed by paper)* — copies `Pt.xa.h_eq` from each kit point into `FamP.h_eq`:
```lean
  h_eq x _ i := ((k x).pt i.1).xa.h_eq
```
2. **`FamP.raise`** in `src/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/FamRaise.lean:12-36` *(cited by paper)* — copies `Fm.h_eq` when raising `x1`:
```lean
def FamP.raise {eps : ℝ} (Fm : FamP eps) (y : ℝ) : FamP eps :=
  { Fm with
    ...
    h_eq := fun x h => Fm.h_eq x (raise_lt h)
```
3. **`UpperTheory.GalC.gd`** in `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/HeckeGaloisCriteria/LinkNOfGd.lean:17-30` *(missed by paper)* — constructs a new `FamP eps` via record update `{ Fm with ... }`:
```lean
def gd (Fm : FamP eps) (c : ∀ x (i : Fm.Ix x), CutD (Fm.D x i)) : FamP eps :=
  { Fm with
    D := fun x i => (raw (c x i)).rec'
    L := fun x i => Gen.ledTr (raw (c x i)) (Fm.L x i)
    ...
    X := fun x i => Gen.divTr (raw (c x i)) (Fm.X x i)
    ... }
```
Because `setRaw` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NStageTrivialCharacterCoeffEqAlt.lean:112-123`) leaves `D.div` unchanged and `Gen.ledTr`/`Gen.divTr` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/HeckeGaloisCriteria/BuDefQEta.lean:25,42`) are transparent record copies, Lean implicitly reuses `Fm.h_eq` at the updated type.

*(Note: `GlobalTheory.LayerMove.Mv.D` in `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/WithLocPre.lean:39-49` also calls `setDiv D m.N m.h`, but only to transport a stage `D7`; it does not construct `ExtraAt`, `FamP`, or `h_eq`.)*

---

## Item 2: `exists_divStage_of_pk` and `exists_divStage`

**Verdict: PARTLY TRUE**

The core factual point—that `exists_divStage_of_pk` accepts `h` as a free parameter and every caller passes `fun _ => 0`, and that the zero-initializing `exists_divStage` lemmas set `Bk := fun _ => 0` and `h := fun _ => 0` across eight call sites—is **true**. However, the paper **misses 3 of the 5 callers** of `exists_divStage_of_pk` and **conflates two distinct `exists_divStage` theorems** in two different files, misattributing `DivInhab.exists_divStage` to `ExistsDivStage.lean:334`.

### `exists_divStage_of_pk`

In `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsDivStageOfPk.lean:76-124`, `exists_divStage_of_pk` takes `(h : B.Word → ℝ)` as a parameter, sets `Bk := bkOf ...` (not zero) and `h := h`, and proves `V.div.h = h` by `rfl`:
```lean
theorem exists_divStage_of_pk : ∀ (B : Base) (C : Cols B) ... (h : B.Word → ℝ) (etaF : ℝ),
    ∃ V : DivStage B C (p.what₂ e W₀ n η hη), ... ∧ V.div.h = h ∧ ...
  ...
  let Dd : DivData B.LL B.Word :=
    { RR := RR, Nu := Nu, Bk := bkOf (p.what₂ e W₀ n η hη) p.cR, h := h,
      HH := sFrame Nu h + RR.muMax, HH_ge := le_rfl, ... }
  ...
  refine ⟨V, ..., fun u x => Iff.rfl, rfl, rfl, rfl, fun H u φ x => bkOf_spec ...⟩
```

An exhaustive grep for `exists_divStage_of_pk` finds **5 call sites**, and **all 5 pass `(fun _ => 0)`** for `h`:
1. `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/StartStateUntwistedEmptyLocal.lean:54-55` *(cited)*:
```lean
  obtain ⟨V, hV, -, -, hη, -, hB⟩ := exists_divStage_of_pk B w.C (Gc B w.px) P.q.p P.q.e P.q.W₀ P.q.n (fun _ _ => 0)
    (fun _ _ => le_rfl) (frames_unit P.q.t) (fun u => ((w.C.fm u).lat 0).L) (fun _ => 0) (6 * K.s.x ^ (-K.C.P.CF))
```
2. `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/BareStatementOfDiscreteSeries.lean:252-254` *(cited)*:
```lean
  obtain ⟨V, hV, -, -, hη, -, hB⟩ := exists_divStage_of_pk _ w'.C (Gc _ w'.px) P'.q.p P'.q.e P'.q.W₀ P'.q.n
    (fun _ _ => 0) (fun _ _ => le_rfl) (frames_unit P'.q.t) (fun u => ((w'.C.fm u).lat 0).L) (fun _ => 0)
    (6 * K.s.x ^ (-K.C.P.CF))
```
3. `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ExistsBareFormOfSaturation.lean:50-51` *(missed by paper)* — passes `(fun _ => 0)`.
4. `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/MinimalKtypeOfLocalComponents.lean:31-33` *(missed by paper)* — passes `(fun _ => 0)`.
5. `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MinimalKtypeOfLocalComponents.lean:33-35` *(missed by paper)* — passes `(fun _ => 0)`.

### Three distinct `exists_divStage` declarations

1. **`GlobalTheory.Mem.DivModel.exists_divStage`** (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExistsDivStage.lean:334-381`) — *this*, not `DivInhab.exists_divStage`, is at `ExistsDivStage.lean:334`:
```lean
theorem exists_divStage (B : Base) (C : Cols B) (W : RowsRest B C) :
    ∃ V : DivStage B C W, V.div.AllGood ∧ ... := by
  ...
  refine ⟨{ div := { RR := stdLat B.LL W.Drows
                     Nu := Nu
                     Bk := fun _ => 0
                     h := fun _ => 0
```
Called at **2** sites (`ExistsExtTwistedPlaces.lean:46`, `ExistsLtGrpTrue.lean:44`).

2. **`GlobalTheory.Mem.DivInhab.exists_divStage`** (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeEmbeddingMemUnitGroup.lean:282-326`):
```lean
theorem exists_divStage : ∀ (B : GlobalTheory.Mem.Base) (C : GlobalTheory.Mem.Cols B) (W : GlobalTheory.Mem.RowsRest B C),
    ∃ X : GlobalTheory.Mem.DivStage B C W, ...
  ...
  let D : DivData B.LL B.Word :=
    { RR := RR, Nu := Nu, Bk := fun _ => 0, h := fun _ => 0, HH := sFrame Nu (fun _ => 0) + RR.muMax ... }
```
Called at **6** sites (`ExistsBaseJointFld.lean:125`, `ExistsOkPins.lean:199`, `NontrivialReferenceForms.lean:408`, `ExistsTrueColsRowInt.lean:103`, `ExistsStagesWithDelta.lean:38`, `ExistsPreHasLetters.lean:73`). Together, the two zero-setting `exists_divStage` lemmas account for `2 + 6 = 8` call sites.

3. **`GlobalTheory.Mem.exists_divStage`** (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LinearIndependentSemilinearOfBasis.lean:117-174`) — parameterized by `Bk` and `h`; called at **1** site (`ExistsDivStageStandIn.lean:14-15`), which passes `(fun _ => 0)` for both.

---

## Item 3: Full Definition of `WordFacts`

**Verdict: TRUE** *(with the omission noted: `WordFacts` has **three** conjuncts, whereas Nielsen's §8 quotation omits the first conjunct)*

The full verbatim definition in `src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:128-133` is:
```lean
def WordFacts {D : D7} (L : SizeData₂ D) (C Cabs : ℝ) (u : D.what₂.Word) : Prop :=
  (D.div.Nu u).L.map ((D.div.Bk u).restrictScalars (𝓞 D.what₂.LL)) ≤ D.div.cc ∧
  (D.div.Bk u ≠ 0 → Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X D.div.RR.dualB D.div.RR.dualX (D.div.Bk u) ≤
    D.div.h u) ∧
  D.div.RR.muDual + D.div.h u - L.Fo ≤ L.MAIN u +
    C * (D.host.TT.card : ℝ) * L.sc.a * L.La + C * (D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)
```

Its three conjuncts are:
1. **Integrality / dual-lattice inclusion (omitted in Nielsen's display):** `(D.div.Nu u).L.map ((D.div.Bk u).restrictScalars (𝓞 D.what₂.LL)) ≤ D.div.cc`, where `D.div.cc := D.div.RR.dualL` (`src/Formalism/LocalRingCardinality/DataArith.lean:168`). Quantified over all `u`, this is `D.div.OneMapIntoCC`.
2. **Slope / map-height inequality (a):** `D.div.Bk u ≠ 0 → Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X D.div.RR.dualB D.div.RR.dualX (D.div.Bk u) ≤ D.div.h u`.
3. **Upper bound (b):** `D.div.RR.muDual + D.div.h u - L.Fo ≤ L.MAIN u + C * (D.host.TT.card : ℝ) * L.sc.a * L.La + C * (D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)`.

---

## Item 4 (KEY QUESTION): How Inequalities (a) and (b) Are Established on the Live Route

**Verdict: (ii) — FALSE as to the claim that inequalities (a) and (b) hold by reflexivity / `rfl` / `le_refl` comparing a quantity with itself.**

On the live route to the final theorem, **neither inequality (a) nor inequality (b) is proved by reflexivity (`rfl`/`le_refl`) or by comparing a quantity with itself**. Both are proved from substantive operator-norm, spectral, valuation, covolume, and analytic inequalities packaged into `DivInputsR` and processed by `divClausesR_of`. What *is* discharged by `fun _ => rfl` (via `setDiv`) is the **equality** `D.div.h u = DV.hExpl6 D L Z Csz u` (`Fm.h_eq`), which enters only as the rewriting identity `tH : R.hu - meanLog P.cols.κ = D.div.h u` connecting `D.div.h u` to the explicit formula `R.hu - meanLog κ` that inequalities (a) and (b) actually bound from below and above. (Separately, two auxiliary fields of `DivInputs0R`—`constant_ge_twenty_eight` and the scale-matching field `eig6`—are trivial/bookkeeping, while the genuine spectral/operator-norm/valuation/divisor bounds live in `nP`, `nKcb`, `S.log_eigenvalue_sum_le_min`, `bi`, `bLG`, `biv`, `borderedMinorImage`, `twisted_third_sum_le`, `errB`, `deQ`/`Qb`, `val2`, `P.base.boundsMu`, `P.extra.passage`, and `R.divIneq`.)

### 4.1 Complete Trace from `wordFacts_of` to `divClausesR_of` and `closed_linkDIVt_of_closed_bridge_kernel`

1. **`wordFacts_of`** (`src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean:135-153`):
```lean
theorem wordFacts_of ... (ht muC kap hu Fo2 rhs : ℝ)
    (c1 : ∀ φ ∈ Nc, B φ ∈ Formalism.HN.dualLat Rc) (c2 : B ≠ 0 → ht ≤ hu - kap) (c3 : muC - kap + hu - Fo2 ≤ rhs)
    (tHt : Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X D.div.RR.dualB D.div.RR.dualX (D.div.Bk u) = ht)
    (tMu : muC = D.div.RR.muDual) (tH : hu - kap = D.div.h u) (tFo : Fo2 = L.Fo)
    (tR : rhs ≤ L.MAIN u + C * (D.host.TT.card : ℝ) * L.sc.a * L.La +
      C * (D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)) :
    WordFacts L C Cabs u := by
  refine ⟨oneMap_of_coord ... c1, fun hne => ?_, ?_⟩
  · rw [tHt, ← tH]; exact c2 (ne_zero_of_coord ... hne)
  · rw [← tMu, ← tH, ← tFo]; linarith
```
2. **`wordFacts_of_clauses`** (`RecBridge.lean:179-202`) and **`wordFacts_of_face`** (`RecBridge.lean:204-225`) supply:
   - `c1` from `hcl.1` (after `rw [hNs]`),
   - `c2` from `hcl.2.1` via `htMap_le_of_bound` (`RecBridge.lean:161-171`) and `opNormAt_pos_of` (`RecBridge.lean:222`),
   - `c3` directly from `hcl.2.2.1` (`DivClausesR`'s 3rd conjunct: `P.cols.muCC - meanLog P.cols.κ + R.hu - 2 * FoOfR P ≤ R.rhs`),
   - `tHt` from `RBTie.htMap_tie` (`RecBridge.lean:223-224`),
   - `tMu` from `RBTie.muDual_tie` (`RecBridge.lean:225`),
   - `tH`, `tFo`, `tR` passed through from `DivisionPackageFace`.
3. **`DivisionPackageFace.ofOpen`** (`src/Formalism/LocalToGlobal/Divisibility/RecBridgeMkF.lean:38-66`) supplies:
   - `tH` (`hTie`) via `hTie_of` (`RecBridge.lean:341-345`), which uses `hh : D.div.h u = hExpl6 D L Z Ch u` (from `Fm.h_eq`), `hnum_of_numRecTieH` (`RecBridgeNum.lean:220-240`), and `hk : Z.kapR σ = κ (mk σ)`,
   - `tFo` (`foTie`) via `two_FoOfR_eq_Fo` (`RecBridgeMkF.lean:63`),
   - `tR` (`rhs`) via `rhs_le_record` (`RecBridgeMkF.lean:64-65`).
4. **`DivisionPackageFace.wordFacts`** (`RecBridge.lean:633-641`) supplies `hcl : DivClausesR ...` by calling `linkDIV_L2R_face` (`src/Formalism/LocalToGlobal/Divisibility/LinkDIVL2R3Col.lean:19-24`), which directly calls `divClausesR_of` (`src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean:184-247`):
```lean
theorem DivisionPackageFace.wordFacts ... : WordFacts L C Cabs u :=
  wordFacts_of_face ... (linkDIV_L2R_face P.Pk ... { toDivInputs0R := P.inp u,
    val2 := Formalism.L2.G.ServJointF.val2AllAtRF ... }) ...
```
5. Inside **`divClausesR_of`** (`ConstantGeTwentyEight.lean:184-247`):
   - **Clause 1 (integrality / `c1`)** (`:191-192`): invokes `P.cols.intoDual divIntoDualShift latticeGlue wf1 ... I.val2`.
   - **Clause 2 (inequality (a) / `c2`)** (`:194-209`): for `P.cols.col.B u ≠ 0`, invokes `nK_of_cb I.cb ... I.nKcb`, `height_chain_atR wf1 P.cols u hne I.X0 I.base_matrix_det_unit I.ch I.hn.hPn I.hn.sz I.nP nK` (`:123-182`, which calls `complex_height_cast_at height_constant_bound` and `S.log_eigenvalue_sum_le_min`), and `I.hn.le_hu (∑ j, N.l6 j) I.eig6` (`DivisionHeightBoundStatement.lean:113-123`, calling `Formalism.DivisorInequality.height_bound_at_set`).
   - **Clause 3 (inequality (b) / `c3`)** (`:211-245`): invokes `P.base.boundsMu Formalism.DivisorInequality.boundsMu specDet reduction_lemma_zero latticeGlue ramBasic wf0 ... I.bi I.bLG I.biv I.borderedMinorImage I.twisted_third_sum_le`, `P.extra.passage` (with `I.de0`, `I.deQ`, `I.Q1`, `I.Qb`, `I.la_le`, `I.constant_ge_twenty_eight`), `I.L3main`, and `R.divIneq ... I.errB` (`DivisionHeightBoundStatement.lean:131-180`, invoking `Formalism.DivisionValues.divIneqRecord` → `divisor_inequality_explicit`, `GlobalBoundRefinements.lean:63-91`).
6. **`linkDIVt_of_rowsF`** (`RecBridge.lean:656-695`) calls `DivisionPackageFace.wordFacts` and `linkDIV_at_words` (`RecBridge.lean:327-339`); **`linkDIVt_of_rowsT`** (`RecBridgeTied.lean:200-203`) feeds into both **`linkDIVt_closedK`** (`RecBridgeSel.lean:369-377`) and the live-route wrapper **`closed_linkDIVt_of_closed_bridge_kernel`** (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DIVRecBridgeSel.lean:197-205`).

### 4.2 Every Field of `DivInputs0R` and `DivInputsR`

`DivInputs0R` (`src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean:26-104`) has **37 fields**, and `DivInputsR` (`:105-109`) extends it with **1 additional field** (`val2`), for **38 fields total**:

| # | Field | Type (`ConstantGeTwentyEight.lean:26-109`) | Substantive inequality/bound? |
|---|-------|-------------------------------------------|-------------------------------|
| 1 | `Nu_lat` | `Submodule.IsLattice K Nu` | Structural (lattice property) |
| 2 | `sg_fin` | `(Function.support (shiftZ sg)).Finite` | Structural (finite support) |
| 3 | `Xc_unit` | `∀ v, IsUnit (Dc.Xc u v).det` | Structural (invertible frames) |
| 4 | `a_pos` | `0 < Dc.a u` | Structural (positive dimension) |
| 5 | `X0` | `InfinitePlace K → Matrix (Fin (Df1.nV Bs.μ0)) (Fin (Df1.nV Bs.μ0)) ℂ` | Data (archimedean frames) |
| 6 | `base_matrix_det_unit` | `∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹)ᴴ * (X0 v)⁻¹ = (Df1.HV Bs.μ0).map v.embedding` | Structural (Hermitian frame identity) |
| 7 | `ch` | `ColChain Dc u` | Data (chain of column maps/matrices) |
| 8 | `hn` | `HtNums R (InfinitePlace K)` | Data + numerical bounds for height chain |
| 9 | `nP` | `∀ v, opNormAt ... (ch.X (Fin.last ch.mm)) ... (dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn` | **Yes — substantive operator-norm bound** |
| 10 | `cb` | `CBData ch.X ch.Kj` | Data (Cauchy-Binet / norm-square certificates) |
| 11 | `nKcb` | `∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ univ.filter (fun l => ch.lf l = j), hn.sz l v` | **Yes — substantive step-norm bound** |
| 12 | `eig6` | `∑ j, R.hX j ≤ ∑ j, N.l6 j` | Inequality in interface; on live route holds as equality via `ZscFix3` (`l6u := 0`); actual spectral lower bound is `S.log_eigenvalue_sum_le_min` in `IndefColsR` |
| 13 | `eb` | `∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df0.dQ t) → Fin (Df0.dQ t) → K` | Data (local bases) |
| 14 | `heb` | `∀ t w, IsLocBasis (Df0.abelian₂ t) w (eb t w)` | Structural (local basis spec) |
| 15 | `Sy` | `Finset (HeightOneSpectrum (𝓞 K))` | Data (finite set of places) |
| 16 | `Sy_tw` | `P.base.Tw ⊆ Sy` | Structural (set inclusion) |
| 17 | `G0` | `∀ y, y ∉ Sy → vw y (Df0.Gm eb (P.base.μ y) y) = 0` | Structural (unramified Gram valuation = 0) |
| 18 | `LG` | `ℝ` | Data (Gram valuation bound parameter) |
| 19 | `E3` | `ℝ` | Data (ramified-place sum bound; set to `1`) |
| 20 | `E2` | `Bs.J → ℝ` | Data (twisted-place η-sum bound) |
| 21 | `gy` | `HeightOneSpectrum (𝓞 K) → ℝ` | Data (per-place Gram valuation bound) |
| 22 | `ηy` | `HeightOneSpectrum (𝓞 K) → Bs.J → ℝ` | Data (per-place lift-index excess) |
| 23 | `bi` | `∀ y ∈ Sy, (vw y (Df0.Gm eb (P.base.μ y) y) : ℝ) ≤ (P.base.D : ℝ) * gy y` | **Yes — substantive Gram determinant valuation bound** |
| 24 | `bLG` | `∑ y ∈ Sy, lw y * gy y ≤ LG` | **Yes — substantive weighted place-sum bound** |
| 25 | `biv` | `∀ y ∈ P.base.Tw, ∀ j, (jw (Df0.HT j (P.base.μ y)) y (Df0.Tl j (P.base.μ y)) : ℝ) ≤ ((ramw y : ℝ) * N.J0 (P.base.μ y) y j) * (P.base.D : ℝ) + ηy y j` | **Yes — substantive lift-index / local valuation bound** |
| 26 | `borderedMinorImage` | `∀ j, ∑ y ∈ P.base.Tw, lw y * ηy y j / (P.base.D : ℝ) ≤ E2 j` | **Yes — substantive weighted twisted-place η-sum bound** |
| 27 | `twisted_third_sum_le` | `∑ y ∈ Sy, lw y * (2 / ellw y ^ 2) ≤ E3` | **Yes — substantive prime-sum bound (`≤ 1`)** |
| 28 | `El3` | `ℝ` | Data (level-3 error parameter) |
| 29 | `L3main` | `∑ j, N.l3 j ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + El3` | Matching bound (exact sum match + `El3 := m * (C * l3u)`) |
| 30 | `errB` | `El3 + LG + (∑ j, (N.E1 j + E2 j)) + E3 ≤ R.errB` | **Yes — substantive total error-budget inequality** |
| 31 | `Q` | `ℝ` | Data (passage amplification bound) |
| 32 | `de0` | `0 ≤ N.de` | Sign condition |
| 33 | `deQ` | `3 * N.de * Q ≤ 1` | **Yes — substantive passage smallness bound** |
| 34 | `Q1` | `1 ≤ Q` | Lower bound (by `max 1 ...` in `QOfR`) |
| 35 | `Qb` | `boundBR P LG E3 E2 + N.hh + 28 * N.la ≤ Q` | **Yes — substantive upper bound on `boundBR + hh + 28 la`** |
| 36 | `la_le` | `N.la ≤ R.lam0` | Matching bound (`log |G| ≤ log |G|`) |
| 37 | `constant_ge_twenty_eight` | `28 ≤ R.C0` | Numerical threshold (trivial via `c0F := max 28 ...`) |
| 38 | **`val2`** (`DivInputsR:108-109`) | `∀ w, ∀ φ ∈ Nu, ∀ F ∈ Df1.Mt (P.cols.μ w), Dc.Pt u (P.cols.μ w) φ F = 0 ∨ sg w ≤ (vw w (Dc.Pt u (P.cols.μ w) φ F) : ℝ)` | **Yes — substantive non-archimedean valuation bound** |

### 4.3 Where `DivInputs0R` / `DivInputsR` Is Constructed on the Live Route

Tracing from `shape_closed_link_n_of_green` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:46-47`):
- `TopShape.lean:46` calls `wire_sel_alt` (`ThirdPlaceSeries/WireSel.lean:50`) → `inpAt_of_alt` (`ThirdPlaceSeries/Wire4F.lean:87`) → **`ThirdPlaceSeries/InpAtOf.lean:54-55`**, which constructs the term of type `DivInputs0R`:
```lean
  refine ⟨fun u => ((DivisionInputsWithoutNorm.ofRows (hrest2 u).2.2.2 (Formalism.L2.DIV.Cons.sgRec_fin L u) (hrest2 u).2.1 (hrest2 u).2.2.1
      (X0 u) (hX0 u) (ch u) (hn u) (hnP u) (cb u) (hrest2 u).1 h11 dg hdg hdvd (hA u)).toDef hN).toDivInputs0R hOk hsep,
    fun u => T u, fun u => hF u⟩
```
Here `DivInputsDef3.toDivInputs0R` (`src/Formalism/LocalToGlobal/Divisibility/TwistedPlaceEtaSumLeExtended.lean:247-286`) fills `DivInputs0R`, and **`DivisionPackageFace.wordFacts`** (`RecBridge.lean:638-640`) upgrades `DivInputs0R` to `DivInputsR` by adding `val2 := Formalism.L2.G.ServJointF.val2AllAtRF ...`.

### 4.4 Audit of 13 Specific Fields on the Live Route

1. **`nP`** (`∀ v, opNormAt ... ch.PtL ^ 2 ≤ exp hn.hPn`):
   - **Provided by:** `GlobalTheory.DefRowsChain.rowsBody_of_framed` (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerChainMatricesWithNormBounds.lean:227-270`, specifically `:261-269`), invoked via `rowsU_of_colPins_alt` (`ThirdPlaceSeries/RowsUOfColPins.lean:17-84`) → `memberRows_of_kernelDatum_sizes` → `rowsBody_of_kerTies` → `rowsBody_colFace` (`ColumnsMemberRowsOfLogLevelLe.lean:25-58`).
   - **Substantive or trivial:** **Real argument.** `rowsBody_of_framed` is 44 lines (in a 271-line file), `rowsBody_colFace` is 34 lines, `PeriodBoundLastLog.lean` is 95 lines, `LastMapNorm.lean` is 397 lines, and `LastMapHalfRecNumsOfLogLevelPrimeLe.lean` is 194 lines.
   - **Main lemmas invoked:** `opNormAt_pairing_sq_le_of_value_bound`, `GlobalTheory.ColRowsTop.period_le`, `GlobalTheory.BranchNorm.lastMapNorm`, `lastMapHalf_recNums_of_log_levelPrime_le`, `exists_htNums_of_kerSide_lastSide`, `GlobalTheory.BranchMembers.interlace`, `members_sameShift`, `frames_tilde_gamma_values_alt`.

2. **`nKcb`** (`∀ j v, log (cb.sq j v) ≤ ∑ l, hn.sz l v`):
   - **Provided by:** Same chain (`KerChainMatricesWithNormBounds.lean:233-260`), invoking `GlobalTheory.DefRowsCB.exists_cbData` (`:258-259`) from `FactorBounds` produced by `GlobalTheory.T.kernelHalf_chainNumbers_any_levelPrime` (`ColumnsMemberRowsOfLogLevelLe.lean:27,33-38`).
   - **Substantive or trivial:** **Real argument.** `KerChainMatricesWithNormBounds.lean` is 271 lines; `KernelHalfChainNumbersAnyLevelPrime.lean` is 332 lines.
   - **Main lemmas invoked:** `exists_cbData`, `sq_le_of`, `kernelHalf_chainNumbers_any_levelPrime`, `exists_htNums_of_kerSide_lastSide`, `colsIn_isometry`, `famFramed_chF`, `evGSD_datFramed`.

3. **`bi`** (`vw y (Df0.Gm ...) ≤ P.base.D * gy y`):
   - **Provided by:** `gram_valuation_le_extended` (`TwistedPlaceEtaSumLeExtended.lean:20-28`), plugged in at `:271`.
   - **Substantive or trivial:** **Real argument.** The wrapper is 9 lines; it invokes `DefFam.GmOf_le` (`src/Formalism/LocalToGlobal/Divisibility/RowLatLemmas.lean:806-823`, 18 lines in a 1030-line file).
   - **Main lemmas invoked:** `DefFam.GmOf_le`, `S.dQ_eq`, `reduction_lemma_first` (inside `RowLatLemmas.lean`).

4. **`bLG`** (`∑ y ∈ Sy, lw y * gy y ≤ LG`):
   - **Provided by:** `bLG_def` (`src/Formalism/LocalToGlobal/Divisibility/LinkDef.lean:119-127`), plugged in at `TwistedPlaceEtaSumLeExtended.lean:272`.
   - **Substantive or trivial:** **Real argument** (elementary algebraic number theory). 9 lines in a 365-line file.
   - **Main lemmas invoked:** `place_sum_natural` (product formula / sum of local valuations weighted by `lw y` equals `log n`), `Real.log_mul`.

5. **`biv`** (`jw ... ≤ (ramw y * J0) * D + ηy`):
   - **Provided by:** `lift_index_bound_extended` (`TwistedPlaceEtaSumLeExtended.lean:30-61`), plugged in at `:273`.
   - **Substantive or trivial:** **Real argument.** 32 lines directly, calling `DefFam.jw_le` (`src/Formalism/LocalToGlobal/Divisibility/LiftLatLemmas.lean:663-668`, in a 1245-line file).
   - **Main lemmas invoked:** `lift_lattices`, `exponent_weight_spectral`, `DefFam.jw_le` (→ `local_bounds_from_exponent`), `S.rankZ`, `A3.side_well_formed`.

6. **`borderedMinorImage`** (`∑ y ∈ Tw, lw y * ηy y j / D ≤ E2 j`):
   - **Provided by:** `twisted_place_eta_sum_le_extended` (`TwistedPlaceEtaSumLeExtended.lean:63-96`), plugged in at `:274-275`, with `hN` supplied by `inEta3_num` (`src/Formalism/LocalToGlobal/Divisibility/SumLeEtaSumNum.lean:78-84`, called at `ThirdPlaceSeries/InpAtOf.lean:49-50`).
   - **Substantive or trivial:** **Real argument.** 34 lines (+ 90-line `SumLeEtaSumNum.lean`).
   - **Main lemmas invoked:** `place_sum_natural`, `vw_nat_le_of_dvd`, `W5.lw_nonneg`, `inEta3_num`.

7. **`twisted_third_sum_le`** (`∑ y ∈ Sy, lw y * (2 / ellw y ^ 2) ≤ E3`):
   - **Provided by:** `Formalism.DivisorInequality.places_ell_weighted_sum_le_one` (`src/Formalism/DivisorInequality/DivisorInequalityProofs/BaseLevelBoundsWithCovolumeHolds.lean:35-45`), plugged in at `TwistedPlaceEtaSumLeExtended.lean:276`.
   - **Substantive or trivial:** **Real argument.** 11 lines calling `ramified_places_weighted_sum_le_one` (`:22-33`, 12 lines in a 71-line file).
   - **Main lemmas invoked:** `ramified_places_weighted_sum_le_one`, `place_sum`, `prime_mod_six_of_large.1`.

8. **`eig6`** (`∑ j, R.hX j ≤ ∑ j, N.l6 j`):
   - **Provided by:** `eigenvalue_sum_le_closed_of` (`src/Formalism/LocalToGlobal/Divisibility/EigenvalueSumLeClosedOf.lean:80-90`, 11 lines) applied to `levelSix_fixed_eq` (`:50-55`, 6 lines) inside `arithmetic_fixed_scale` (`:251-269`).
   - **Substantive or trivial:** **Bookkeeping/definitional matching** (NOT where the spectral bound lives): `ZscFix3` (`:41-44`) defines `l6m j := z.l6m j - Cf * z.l6u` and `l6u := 0`, so `eig6` reduces to an equality by `Nd.sum_lifts` and `ring`. The **substantive** spectral lower bound using `N.l6` is `S.log_eigenvalue_sum_le_min` (`ConstantGeTwentyEight.lean:163`), carried by `IndefColsR` inside `Pk.core.cols`!

9. **`L3main`** (`∑ j, N.l3 j ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + El3`):
   - **Provided by:** `levelThree_bound_closed` (`EigenvalueSumLeClosedOf.lean:94-115`, 22 lines).
   - **Substantive or trivial:** **Algebraic matching** (reindexing `ZscOfNum3`'s `l3m` via `Nd.sum_lifts` and setting `El3 := m * (C * l3u)`, where the genuine bound on `l3u` is then proved in `errB`).
   - **Main lemmas invoked:** `Nd.sum_lifts`, `Fintype.card_congr`, `hZ.l3m`.

10. **`errB`** (`El3 + LG + ∑ j, (E1 j + E2 j) + E3 ≤ R.errB`):
    - **Provided by:** `error_bound_closed_numbers` (`EigenvalueSumLeClosedOf.lean:170-200`, 31 lines), called from `arithAt_rec` (`:1994-2033`, 40 lines) and `arithClause_rec` (`src/Formalism/LocalToGlobal/Divisibility/ArithClauseRec.lean:22-62`, 41 lines).
    - **Substantive or trivial:** **Real argument.**
    - **Main lemmas invoked:** `errB_of_units`, `Nd.logLog_le`, `Nd.loss_bound_nonneg`, `Nd.one_le_m_unitE`, `lamSizeAt_record_one`, `divSize_eq_unitE`.

11. **`deQ` and `Qb`** (`3 * N.de * Q ≤ 1` and `boundBR P LG E3 E2 + N.hh + 28 * N.la ≤ Q`):
    - **Provided by:** `Q_ge_bound_add` (`EigenvalueSumLeClosedOf.lean:151-154`, 4 lines) and `de_mul_Q_le_one` supplied by `q_rec` (`EigenvalueSumLeClosedOf.lean:1885-1953`, 69 lines in a 2037-line file).
    - **Substantive or trivial:** **Real argument** (asymptotic parameter dominance).
    - **Main lemmas invoked:** `boundBR_le_closed`, `polyBound_mul_b_le_sq`, `main_rec`, `HookProductWeightBounds.fo_le_pol`, `Lit.mertens_bound`, `errB_rec`, `hg_of_sizeG`, `mul_rpow_le_b`, `logG_rec`.

12. **`constant_ge_twenty_eight`** (`28 ≤ R.C0`):
    - **Provided by:** `twentyEight_le_constant` (`EigenvalueSumLeClosedOf.lean:67`, 1 line: `:= h`) from `h28 : 28 ≤ C0 := le_max_left _ _` (`ArithClauseRec.lean:43`), where `c0F := max 28 ...` (`ArithClauseRec.lean:11`).
    - **Substantive or trivial:** **Trivial by construction** (`le_max_left`, 1 line).

13. **`val2`** (`Dc.Pt u (P.cols.μ w) φ F = 0 ∨ sg w ≤ vw w (Dc.Pt u (P.cols.μ w) φ F)`):
    - **Provided by:** `Formalism.L2.G.ServJointF.val2AllAtRF` (`src/Formalism/LocalToGlobal/GroupLattices/ServJointF.lean:84-102`, 19 lines), calling `perToVal2F` (`:42-82`, 41 lines), plugged in at `RecBridge.lean:639-640`.
    - **Substantive or trivial:** **Real argument** (ultrametric triangle inequality / `Submodule.span_induction` transporting `adm2` valuation bounds through `CutUp` linear combinations).
    - **Main lemmas invoked:** `perToVal2F`, `Submodule.span_induction`, `perCol_lin`, `VGeq.sum`, `VGeq.int_mul`, `VGeq.zero`, `VGeq.add`, `adm2`.

---

## Item 5: Unfolding `D.div.h u = hExpl6 ...` in Inequalities (a) and (b)

**Verdict: FALSE (as to either inequality being syntactically or definitionally `X ≤ X`)**

### Definition of `hExpl6` and its components

From `src/Formalism/LocalRingCardinality/KernelPlaceMeanBound.lean:16-27`:
```lean
def L6lo (D : D7) (L : SizeData₂ D) (C : ℝ) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, logHook (D.R.sigW j).1 (aPlus D j ρ)) -
    C * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lprime D L

def kernelPlaceMeanBound (D : D7) (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, kerPlace D L u j ρ) +
    C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La +
    C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L

def hExpl6 (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ) (u : D.what₂.Word) : ℝ :=
  SZbP D L C u + (∑ j ∈ SizeData₂.lifts D, kernelPlaceMeanBound D L C u j) - (∑ j ∈ SizeData₂.lifts D, L6lo D L C j) -
    meanE D (fun e => Real.log (X.kapR e))
```
where (`src/Formalism/LocalRingCardinality/DataDIVDefs.lean:75-87` and `src/Formalism/LocalRingCardinality/DataParams₂.lean:218,232-234`):
- `SZbP D L C u = -(∑ t : D.host.TT, (L.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ)) + C * ((D.host.TT.card : ℝ) * L.sc.b' * (D.R.N D.R.m : ℝ) + ...) * L.La`,
- `kerPlace D L u j τ = (∑ i ∈ Finset.range (D.R.N (j - 1)), phF (nuRow D u j τ i)) - (∑ i ∈ Finset.range (D.R.N (j - 1)), nuRow D u j τ i) * L.logOm`,
- `L.Fo = ∑ j ∈ lifts D, ∑ w ∈ L.supp, sz w (L.F j w)`,
- `L.MAIN u = ∑ t : D.host.TT, ((D.R.m : ℝ) * (phF (L.aT t) - (L.aT t : ℝ) * L.logOm) - (L.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ))`.

### Unfolded Inequality (a)

Substituting `D.div.h u = hExpl6 D L X Csz u` into `WordFacts`'s 2nd conjunct (`RecBridge.lean:130-131`) gives:
```text
D.div.Bk u ≠ 0  →
  (1 / nPl LL) * ∑ v, log (opNormAt (D.div.Nu u).b (D.div.Nu u).X D.div.RR.dualB D.div.RR.dualX v (D.div.Bk u) ^ 2)
  ≤  SZbP D L Csz u
     + ∑_{j=1}^m kernelPlaceMeanBound D L Csz u j
     - ∑_{j=1}^m L6lo D L Csz j
     - meanE D (fun e => log (X.kapR e))
```
- **LHS:** Archimedean map-height `htMap` of the linear map `D.div.Bk u` (average over infinite places of `log (‖D.div.Bk u‖_v^2)`).
- **RHS:** Explicit real formula built from `-∑ aT(t) log T_u`, `phF(nuRow) - nuRow * logOm`, `-logHook(aPlus)`, `-meanE (log ∘ X.kapR)`, and error terms.
- **Is it `X ≤ X`?** **No** — neither syntactically nor definitionally. Proving it requires factoring `Bk u` through the column chain (`height_chain_atR`), bounding `ch.PtL` (`nP`), bounding intermediate step matrices (`nKcb`), and lower-bounding archimedean eigenvalues (`S.log_eigenvalue_sum_le_min`).

### Unfolded Inequality (b)

Substituting `D.div.h u = hExpl6 D L X Csz u` into `WordFacts`'s 3rd conjunct (`RecBridge.lean:132-133`) gives:
```text
D.div.RR.muDual
  + ( SZbP D L Csz u
      + ∑_{j=1}^m kernelPlaceMeanBound D L Csz u j
      - ∑_{j=1}^m L6lo D L Csz j
      - meanE D (fun e => log (X.kapR e)) )
  - L.Fo
≤  L.MAIN u
   + C * TT.card * L.sc.a * L.La
   + C * m * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)
```
- **LHS:** Slope `D.div.RR.muDual` of the dual Hermitian lattice `RR.dualL` plus `hExpl6` minus `L.Fo`.
- **RHS:** `L.MAIN u` plus error terms. (Note: both `SZbP` on the LHS and `L.MAIN u` on the RHS share the leading term `-∑_{t ∈ TT} aT(t) log T_u`, while `muDual` is bounded via `P.base.boundsMu` + `P.extra.passage` in terms of `meanLog κ + ∑ l3 + L.Fo + ...`, so `meanLog κ` cancels `-meanE (log ∘ kapR)` and `L.Fo` cancels `-L.Fo`, after which `TheoremDivIneq` (`StatementK.lean:11-57`) combines `∑ l3`, `ph(nuRow) - nuRow * logOm`, and `-logHook` to reach `∑ m (ph(aT) - aT logOm)` + absorbed errors.)
- **Is it `X ≤ X`?** **No** — neither syntactically nor definitionally.

*(Role of `D.div.h` in the squeeze: `D.div.h` acts as an intermediate upper bound for `htMap (D.div.Bk u)`—entering with a **minus** sign in `sFrame D.div.Nu D.div.h` inside `TheoremF` to give a lower bound on `D.div.RR.muDual`, and with a **plus** sign in inequality (b) to give an upper bound on `D.div.RR.muDual + D.div.h u`. Adding the two eliminates `D.div.h u` completely. Notably, Nielsen's Section 8 acknowledges this cancellation at `paper.txt:514-525`, which directly contradicts the paper's own claim in the Abstract (`paper.txt:25-26`) and Section 8 (`paper.txt:498-500`) that the inequality [quotation from the paper omitted].)*

---

## Item 6: Is `Bk` Identically Zero on the Live Route?

**Verdict: FALSE — `Bk` is NOT identically zero on the live route, and the case `Bk u ≠ 0` is both non-vacuous and essential downstream.**

### How `Bk` is set and preserved along the live route

1. **Initial setting via `bkOf`:** Unlike `DivInhab.exists_divStage` / `DivModel.exists_divStage` (which set `Bk := fun _ => 0` for auxiliary inhabitation), `exists_divStage_of_pk` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsDivStageOfPk.lean:33-38, 92`) sets `Bk := bkOf (p.what₂ e W₀ n η hη) p.cR`:
```lean
def bkOf {B : Base} {C : Cols B} (W : RowsRest B C) {m : ℕ} (c : Fin m → W.EE) (u : B.Word) :
    (C.fm u).ramSub →ₗ[B.LL] Module.Dual B.LL (Fin m → B.LL) :=
  if H : ∀ u (φ : (C.fm u).ramSub) (x : Fin m → B.LL),
      W.Bu u (GlobalTheory.Mem.ramForm W u φ) (GlobalTheory.Mem.coordForm B.embLL c x) ∈ Set.range B.embLL then
    bkMk W c (fun u φ x => (H u φ x).choose) (fun u φ x => (H u φ x).choose_spec) u
  else 0
```
2. **Preserved by `setDiv`:** `setDiv` (`SetUnipotentTranslate.lean:25-31`, quoted in Item 1) updates only `Nu.L`, `h`, `HH`, `HH_ge` — it leaves `D.div.Bk` untouched.
3. **Rationality proved along the family (`BuRational`):** `D.BuRational` (`src/Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:364-365`) asserts that `D.div.Bk` realizes the complex Bessel pairing `D.what₂.Bu` under `D.what₂.embLL`:
```lean
def BuRational : Prop := ∀ u (φ : (D.div.Nu u).V) (x : D.div.RR.V),
  D.what₂.Bu u (D.jN u φ) (D.jEE x) = D.what₂.embLL (D.div.Bk u φ x)
```
On the live route, `buRat_rrFull_closed_alt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BurrbPlug.lean:23-56`) proves `(Fm.D x i).BuRational` along the family via `buRational_of` (`src/Formalism/LocalToGlobal/Divisibility/DivisibilityRemainder/RationalColumns/BuRationalOf.lean:26-54`), which uses `hR.colsBk` (`D.div.Bk` equals `P.C.B` in coordinates) and `PerDescent.per_sec`. `BuRational` is then packaged into `BesselId D` inside `LinkDIV_at` (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:79`).

### Where `Bk u ≠ 0` and the first conjunct of `WordFacts` matter downstream

1. **Matrix identification (`block_eq`, `MatReal_at`):** In `src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean:1245-1271`, `block_eq` uses `hRat : D.BuRational` to show that the upper block of the Bessel frame matrix `Ball u` is precisely `Y'⁻¹ * (toMatrix (D.div.Bk u)).map v * Y u`:
```lean
    (fun (k : D.div.RR.ι) (j : (D.div.Nu u).ι) => D.besS u (U u (oM D u j)) (V (oE D k))) =
      ((bE D).toMatrix (oE D))ᵀ *
        (LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u)).map D.what₂.embLL *
        ((a u)⁻¹ • (bN D u).toMatrix (oM D u))
```
In `MatReal_at` (`TopDensityNGeSixteen.lean:658-672`), `Ball u` satisfies `Ball u = Bf u * Vr u`, `(Vr u)ᴴ * Vr u = 1`, `InputSG Bf γ D.what₂.Dstar η0 η1 e0` (near-isometry from `LinkS`), and `(1 - D.what₂.delp) * card (RR.ι ⊕ κ₁) ≤ card RR.ι` with `delp < 1` (from `LinkIRR`). If `D.div.Bk u` were identically zero, the upper `(1 - delp)` fraction of rows of `Ball u` would vanish identically, making the near-isometry condition `InputSG` impossible for small `e0, delp`.

2. **Use of `WordFacts` conjuncts 1 and 2 in `TheoremF`:** `frameRealF_of` / `frameReal_at_of` (`TopDensityNGeSixteen.lean:679-723`) unpack `hOne : D.div.OneMapIntoCC` (conjunct 1 of `WordFacts`) and `hht : ∀ u, D.div.Bk u ≠ 0 → htMap ... (D.div.Bk u) ≤ D.div.h u` (conjunct 2) from `LinkDIV` and pass them into `TheoremF` / `theoremFSharp_of` (`src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean:279-300`):
```lean
  let M : ℝ → Submodule (𝓞 K) W := fun τ => ⨆ i, (Nt τ i).map ((B i).restrictScalars (𝓞 K))
  have hMle : ∀ τ, M τ ≤ St τ := by
    intro τ
    refine iSup_le fun i => ?_
    by_cases h0 : (Nt τ i).map ((B i).restrictScalars (𝓞 K)) = ⊥
    · rw [h0]; exact bot_le
    · have hBi : B i ≠ 0 := by ...
      have hsi := (slope_inequality_mean ... (B i) (Nt τ i) (hNtFG τ i) h0).1
      ...
      have hhi := hht i hBi
      refine (frameB_hnStep ... hLcc (θ' τ)).2.2.1 _ ?_ h0 ?_
      · exact le_trans (Submodule.map_mono (hNtle τ i)) (hBN i)
      · ...; linarith
```
Here `hBN i` (`OneMapIntoCC`) ensures `(Nt τ i).map (B i) ≤ cc`, and `hht i hBi` bounds the slope drop `htMap (B i) ≤ h i` whenever `(Nt τ i).map (B i) ≠ ⊥` (which forces `B i ≠ 0`). Then `hplace` (`:309-322`) uses `thmF_place` on `Ball` to show `rkK (M τ) ≥ (1 - w τ) * card κ`, which requires non-zero images `(Nt τ i).map (B i)` whenever `w τ < 1` and `card κ > 0`.

---

## Item 7: Consumer Chain from `WordFacts` to `zeroFreeOn_of_tiedWin_cyc`

**Verdict: TRUE**

### Statements along the chain

1. **`linkDIVt_closedK`** (`src/Formalism/LocalToGlobal/Divisibility/RecBridgeSel.lean:369-373`) and live-route counterpart **`closed_linkDIVt_of_closed_bridge_kernel`** (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DIVRecBridgeSel.lean:197-201`):
```lean
theorem linkDIVt_closedK (𝒟 : FamClass) (Cabs : ℝ)
    (Rk : ∀ {eps : ℝ} (Fm : FamP eps), 𝒟 Fm →
      Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsKernel (Fm.ex x hx i))
    (h : Closed 𝒟 (fun Fm CH => ∀ hc : 𝒟 Fm, TuSize Fm → DGamSize Fm → BridgeRowsK Fm (Rk Fm hc) Cabs CH)) :
    Closed 𝒟 (fun Fm CH => TuSize Fm → DGamSize Fm → LinkDIVt Fm Cabs CH)
```
```lean
theorem closed_linkDIVt_of_closed_bridge_kernel (𝒟 : FamClass) (Cabs : ℝ)
    (Rk : ...) (h : Closed 𝒟 (fun Fm CH => ∀ hc : 𝒟 Fm, TuSize Fm → DGamSize Fm →
      DivisionKernelConstantBounds Fm (Rk Fm hc) Cabs CH)) :
    Closed 𝒟 (fun Fm CH => TuSize Fm → DGamSize Fm → LinkDIVt Fm Cabs CH)
```
2. **`shape_closed_link_n_of_green`** (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:33-55`):
```lean
theorem UpperTheory.Top.shape_closed_link_n_of_green :
    GlobalTheory.GLq.Green → _root_.GlobalTheory.Fc.TopShapeAlt True True
      (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) UpperTheory.Top.TopG
```
(At `:47`, it builds `hDIV := closed_linkDIVt_of_closed_bridge_kernel (D3 3 𝒜) 2 ... hBR`, and passes `hDIV` into `topDesWin` at `:52-55`.)

3. **`topDesWin`** (`src/Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean:11-22`):
```lean
theorem topDesWin (𝒞 𝒞' ℰ : FamClass) (Cabs C0 eD eL : ℝ) (hEx : DesignExists (WithTw (WithSm 𝒞')) C0)
    (h1 : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → 𝒞 Fm) (h2 : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → ℰ Fm)
    (hV : ∀ {eps : ℝ} (Fm : FamP eps), ℰ Fm → HypV Fm.toFamCore)
    (hN : Closed (Des 𝒞 C0) fun Fm _ => LinkN Fm) ...
    (hDIV : Closed (Des 𝒞 C0) fun Fm CH => TuSize Fm → DGamSize Fm → LinkDIVt Fm Cabs CH)
    (hRk : Closed (Des 𝒞 C0) fun Fm CH => ChosenE Fm C0 CH → NuFullF Fm ∧ J.MuRank Fm)
    (hG : Closed (Des 𝒞 C0) fun Fm _ => LinkG Fm)
    (hS : Closed (Des 𝒞 C0) fun Fm _ => TuSize Fm → LinkS Fm C0)
    (hGL : Closed (Des 𝒞 C0) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 eD eL) :
    FamilyClassConnected ℰ
```
4. **`GlobalTheoremInputs` / `LinkGLOBAL`** (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:158-164`) and **`FamilyClassConnected`** (`src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:13-15`):
```lean
def GlobalTheoremInputs {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 : ℝ) : Prop :=
  LinkG Fm ∧ LinkS Fm C0 ∧ LinkIRR Fm ∧ LinkDIV Fm Cabs CH ∧ LinkMu Fm

def LinkGLOBAL {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 eD eL : ℝ) : Prop :=
  ChosenE Fm C0 CH → GlobalTheoremInputs Fm Cabs CH C0 →
    ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ChainTied Fm eD eL K cHH eK CL x
```
```lean
def FamilyClassConnected (ℰ : FamClass) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ →
    ∃ Fm : FamP eps, ℰ Fm ∧ ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ChainTied Fm eD eL K cHH eK CL x
```
5. **`zeroFreeAll_of_topG`** (`src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:26`) and **`zeroFreeOn_of_tiedWin_cyc`** (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean:90-93`):
```lean
theorem zeroFreeAll_of_topG {la : ℝ} (hla : 1 < la) (h : TopG) (hS : ∀ ψ : PChar, HostExW la (GChi ψ).req) : ZeroFreeAll
```
```lean
theorem zeroFreeOn_of_tiedWin_cyc {Q : PChar → Prop} {la : ℝ} (hla : 1 < la)
    (h112 : ∀ ψ, Q ψ → ChebyshevInequalityOnWindows @core @Tied (Level.cyc ψ)) (hB : ∀ ψ, Q ψ → (Level.cyc ψ).FormB)
    (h : ∀ ψ, Q ψ → ChebyshevInequalityAtWindowScale @core @Tied la (Level.cyc ψ)) : ZeroFreeOn Q
```

### Summary of the Consumer Chain (12 lines)

1. At each word `u`, `DivisionPackageFace.wordFacts` (`RecBridge.lean:633`) invokes `divClausesR_of` to produce `WordFacts` (conjuncts: `OneMapIntoCC`, `htMap ≤ D.div.h u`, and `muDual + D.div.h u - Fo ≤ MAIN u + err`).
2. `linkDIV_at_words` (`RecBridge.lean:327`) bundles `WordFacts` with `FrameNumberBound`, `BesselId D`, `D.RRFull`, `ZeroAbove`, and `Compl3` into `LinkDIV_at`, which `linkDIVt_of_rowsF` (`:656`) → `linkDIVt_of_rowsT` (`RecBridgeTied.lean:200`) → `closed_linkDIVt_of_closed_bridge_kernel` (`DIVRecBridgeSel.lean:197`, parallel to `linkDIVt_closedK`, `RecBridgeSel.lean:369`) lifts to a `Closed` family statement yielding `LinkDIVt Fm 2 CH`.
3. `shape_closed_link_n_of_green` (`TopShape.lean:33-55`) passes this `hDIV` together with `DesignExists`, `LinkN`, `LinkEta`, `LinkIRR`, `SmallLevelRankEq`, `NuFullF ∧ MuRank`, `LinkG`, `LinkS`, and `LinkGLOBAL` into `topDesWin` (`DesWin.lean:11`).
4. `topDesWin` intersects all 9 `Closed` conditions, obtains a family `Fm` for every small `ε > 0`, upgrades `LinkDIVt` + `LinkEta` + `DIVinN` to `LinkDIV`, derives `LinkMu` from `LinkDIV`, forms `GlobalTheoremInputs Fm`, and applies `LinkGLOBAL` (`LinkGl.lean`)—where `TheoremF` eliminates `D.div.h` between the lower bound on `muDual` and `WordFacts`'s upper bound—to produce `ChainTied` on `Fm.Win` (`FamilyClassConnected (G.cls la)`).
5. `zero_free_all_of_green_v_win` (`ThirdPlaceSeries/TopPlug.lean:12-15`) instantiates `shape_closed_link_n_of_green` to get `TopG` and passes it to `zeroFreeAll_of_topG` (`ZeroFreeAllOfTopG.lean:26-34`).
6. `zeroFreeAll_of_topG` invokes `zeroFreeOn_of_tiedWin_cyc` (`TopWin.lean:90-93`) with `level_gm_le_on_family_scales` (`LevelGmLeOnFamilyScales.lean:28`, converting `ChainTied` into Chebyshev bounds on `Fm.Win`) and `Comparison₂.formB` (converting windowed Chebyshev bounds into zero-free half-planes via `level_of_tiedWin`, `TopWin.lean:68-81`), concluding `ZeroFreeAll` (and `EveryCharacter` at `TopPlug.lean:16-18`).

---

## Overall Summary

| Item | Topic | Verdict | Key Finding |
|------|-------|---------|-------------|
| 1 | Sites constructing `h_eq` | **PARTLY TRUE** | Sole origin is indeed `fun _ => rfl` after `setDiv` (`SetUnipotentTranslate.lean:379-400`); `FamRaise.lean:36` copies it. However, `DisjointSplitLevelPlaces.lean:331,501` are **unrelated** (`RawDat.h_eq : h = hP * k`), and 2 real copying sites (`ExistsFamPOfKits.lean:139`, `LinkNOfGd.lean:17-30`) were missed. |
| 2 | `exists_divStage_of_pk` / `exists_divStage` | **PARTLY TRUE** | All 5 callers of `exists_divStage_of_pk` (3 missed by paper) pass `h := fun _ => 0`. Paper conflates `DivModel.exists_divStage` (`ExistsDivStage.lean:334`, 2 callers) and `DivInhab.exists_divStage` (`LatticeEmbeddingMemUnitGroup.lean:282`, 6 callers); total is `2 + 6 = 8`. |
| 3 | Definition of `WordFacts` | **TRUE** | Exact match at `RecBridge.lean:128-133`, except `WordFacts` has **3** conjuncts; Nielsen omits the 1st (`(D.div.Nu u).L.map (D.div.Bk u) ≤ D.div.cc`, i.e., `OneMapIntoCC`). |
| 4 | How (a) and (b) are proved (**KEY**) | **FALSE** *(for reflexivity claim; **(ii) substantive**)* | Neither (a) nor (b) is proved by `rfl`/`le_refl` comparing a quantity with itself. Only the *equality* `D.div.h u = hExpl6 ...` (entering `tH`) comes from `rfl`. Inequalities (a) and (b) are proved via `divClausesR_of` from substantive operator-norm, spectral, valuation, covolume, and analytic bounds (`nP`, `nKcb`, `S.log_eigenvalue_sum_le_min`, `bi`, `bLG`, `biv`, `borderedMinorImage`, `twisted_third_sum_le`, `errB`, `deQ`/`Qb`, `val2`, `boundsMu`, `passage`, `divIneqRecord`). |
| 5 | Unfolded (a) and (b) vs `X ≤ X` | **FALSE** | Unfolding `D.div.h u = hExpl6 ...` yields `htMap (Bk u) ≤ hExpl6` and `muDual + hExpl6 - Fo ≤ MAIN + err`. Neither is syntactically or definitionally `X ≤ X`; `D.div.h` is an intermediate transit quantity that cancels in the global squeeze. |
| 6 | Is `Bk` identically zero? | **FALSE** | On the live route `Bk` is set via `bkOf`, preserved by `setDiv`, tied to `D.what₂.Bu` by `BuRational` (`BurrbPlug.lean`), identified with the upper block of the near-isometric frame matrix `Ball` (`block_eq`), and used non-vacuously with `Bk u ≠ 0` inside `theoremFSharp_of`. |
| 7 | Consumer chain to `zeroFreeOn_of_tiedWin_cyc` | **TRUE** | Verified end-to-end: `WordFacts` → `LinkDIV_at` → `closed_linkDIVt_of_closed_bridge_kernel` → `shape_closed_link_n_of_green` → `topDesWin` → `LinkGLOBAL`/`ChainTied` → `zeroFreeAll_of_topG` → `zeroFreeOn_of_tiedWin_cyc` → `ZeroFreeAll`. |

**Bottom line on Sections 7–8 of Nielsen's paper:**
- **Confirmed by the code:** `D.div.h` is never derived as an intrinsic geometric invariant; it is initialized to `0` at early stages, overwritten via `setDiv` with the explicit target formula `DV.hExpl6` in `SetUnipotentTranslate.lean:379-400`, and `h_eq` is proved solely by `fun _ => rfl`.
- **Contradicted by the code:** Setting `D.div.h := hExpl6` by `rfl` does **not** make the two inequalities in `WordFacts` hold by reflexivity or compare a quantity with itself. Because `D.div.h` serves merely as a transit variable bounded below by `htMap (D.div.Bk u)` in (a) and bounded above alongside `D.div.RR.muDual` in (b) (and then eliminated in `LinkGLOBAL`), setting `D.div.h := hExpl6` simply instantiates the existential intermediate quantity `h`; both inequalities (a) and (b) remain genuine theorems about `htMap (D.div.Bk u)`, `D.div.RR.muDual`, `L.Fo`, and `L.MAIN u`, and are proved on the live route from substantive non-trivial arguments (with `Bk` non-zero and non-vacuously tied to the Bessel frame matrix). Nielsen's own §8 text (`paper.txt:514-525`) partially acknowledges this transit-variable cancellation, contradicting the stronger reflexivity claim in the Abstract (`paper.txt:25-26`) and §8 (`paper.txt:498-500`). Additionally, several specific site citations in §7 (`DisjointSplitLevelPlaces.lean:331,501`, `DivInhab.exists_divStage` at `ExistsDivStage.lean:334`) are inaccurate.
