# Audit Report B: Logical Role of the Geometry Parameter `Γ : GeoP`

**Scope & Ground Rules.** This report audits the logical role of the geometry predicate parameter `Γ : GeoP` and its instantiation at `geoCl anyGeometry` (`anyGeometry := fun _ _ _ => True`) in `~/rh-audit/src/omega` (read-only source audit; Lean 4 is not installed). Every factual claim cites exact file paths and line numbers relative to `~/rh-audit/src/omega/` and quotes actual Lean terms/types. Findings verified directly from source are explicitly separated from logical inferences, with confidence levels stated throughout.

---

## Executive Summary & Call Chain Overview

### Verified Entry-Point Topology (Two Parallel Tracks)

Inspection of the actual call chain from `src/Main.lean` reveals **two parallel, structurally isomorphic tracks** in the repository:

1. **Actual `Main.lean` track (`ThirdPlaceSeries` / `HypsAlt` / `Parameters`):**
   - `src/Main.lean:4`: `theorem riemannHypothesis : RiemannHypothesis := rhOfAll`
   - `src/Supplements/Kernels/MainTheorems.lean:7,9`: `rhOfAll := Formalism.VW.rh_of_every allChi`, `allChi := UpperTheory.FinalTheorems.everyCharacter`
   - `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7-11`: `everyCharacter` → `everyCharacter_of_row` → `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin`
   - `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810-813`: `every_character_of_literature_of_vWin` calls `_root_.UpperTheory.Lit.every_character_of_theta_integrals_local_matching`
   - `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:44-73`: `every_character_of_theta_integrals_local_matching` calls `UpperTheory.Top.every_character_of_green_v_win` with `nonempty_hyps_definite_side_of_closed_bound` (which produces `Nonempty (HypsAlt S0.NL DefiniteSideCondition)` using `geoCl anyGeometry`).
   - `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12-18`: `every_character_of_green_v_win` → `zero_free_all_of_green_v_win` → `GlobalTheory.Fc.forall_goal_of_shape_of_hyps ... (UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h`.

2. **Parallel `EveryCharacterE.lean` track (`Hyps` / `Prm` / `prmR`, referenced in the critic's background):**
   - `src/Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/EveryCharacterE.lean:41-71`: `everyE₂` calls `UpperTheory.Top.plugAll` with `hypsE₂` (which produces `Nonempty (Hyps S0.NL DRS)` using `geoCl anyGeometry`).
   - `src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:8-18`: `plugAll` → `plugWin` → `GlobalTheory.Fc.shape_of ... (UpperTheory.Top.shapeWin hG) trivial trivial h`.

**Verified:** Both tracks use the **exact same** definitions of `GeoP`, `anyGeometry`, `geoOf`, `GeoCl`, `geoCl`, `OAt`, `OX`, `Slots`, `Built`, `Wit`, `WPt`, `divEx_of_ox`, `divEx_geoCl`, and `oAt_setDiv`, and have identical quantification and polarity structure with respect to `Γ`. Both tracks are documented below.

---

## 1. Definitions of `GeoP`, `geoOf`, `anyGeometry`, `GeoCl`/`geoCl`, `OAt`, `OX`, `Prm`, `prmR`, and Parameter Flow

*(All items in Section 1 are **VERIFIED** directly from source; confidence: **100%**.)*

### 1.1 `GeoP`, `geoOf`, `anyGeometry`, `OAt`, and `OX`

In `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean:14-19,29-49`:

```lean
-- OverIx.lean:14-19
abbrev GeoP : Type 1 := ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop

def geoOf (Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D) : GeoP := fun D J X =>
  (∃ c : ℕ, 0 < c ∧ GlobalTheory.ShFam.IsGeoOf (Q D) J c X) ∧ GlobalTheory.ShFam.Pad.HasTrueSurf X

def anyGeometry : GeoP := fun _ _ _ => True
```

```lean
-- OverIx.lean:29-38
def OverIx (Z : R3.ReadL R F X0 Y) (σ : D.what₂.FT) (c : A3.fam3.base3.Ix) : Prop :=
  ∀ i : Fin D.R.m, D.what₂.isot ((i : ℕ) + 1) σ ≤
    Submodule.span ℂ ((Z.jW i) '' ((R3.s0Of R F).Wp i c : Set (Fin ((R3.s0Of R F).dW i) → D.what₂.LL)))

def LamAre (Z : R3.ReadL R F X0 Y) (Xd : DivX D) : Prop :=
  ∃ lab : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, (∃ c, OverIx Z σ c) → OverIx Z σ (lab σ)) ∧
    ∀ (i : Fin D.R.m) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ), e ≠ D.what₂.embLL →
      (D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ →
        Xd.logLam ((i : ℕ) + 1) σ e = Real.log ((R3.s0Of R F).lam i A3.A.μ0 (lab σ) (InfinitePlace.mk e))) ∧
      (D.what₂.isot ((i : ℕ) + 1) σ = ⊥ → Xd.logLam ((i : ℕ) + 1) σ e = 0)
```

```lean
-- OverIx.lean:44-49
structure OAt (Γ : GeoP) {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0)
    (X : DivX (w.D Z)) : Type 1 where
  geo : Γ (w.st Z).toD7 t.r.z.core.toCore X
  lam : LamAre t.r.Z X

def OX (Γ : GeoP) : OComponent₂ := fun _ _ _ _ _ _ _ O t => OAt Γ t O.X
```

Key observations:
- `OAt Γ t X` is a **two-field** structure:
  1. `geo : Γ (w.st Z).toD7 t.r.z.core.toCore X` (depends on `Γ`), and
  2. `lam : LamAre t.r.Z X` (completely **independent** of `Γ`; asserts a nontrivial logarithmic eigenvalue-matching identity for `X.logLam` at all non-base archimedean embeddings).
- `geoOf Q D J X` requires both `∃ c > 0, IsGeoOf (Q D) J c X` (`LargeFor.lean:78-80`) and `HasTrueSurf X` (`SecondChernDegreeVanishesTrueSurfaces.lean:346`, asserting `SurfSt.of X = surfSt`, where `surfSt.Surf` and `surfSt.SurfFp` are proved inhabited at lines 417 and 448).
- `anyGeometry` is literally the constant predicate `fun _ _ _ => True`.

### 1.2 `GeoCl` and `geoCl`

In `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotGeoClFalse.lean:11-28`:

```lean
-- NotGeoClFalse.lean:21-28
inductive GeoCl (Γ : GeoP) : ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop
  | base {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} : Γ D J X → GeoCl Γ D J X
  | step {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
      {J : Formalism.L2.Pj.Core D} {X : DivX D} : GeoCl Γ D J X → GeoCl Γ (setDiv D N h) (coreS N h J) (divTr N h X)

def geoCl (Γ : GeoP) : GeoP := GeoCl Γ

theorem geoCl_of {Γ : GeoP} {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} (h : Γ D J X) : geoCl Γ D J X := GeoCl.base h
```

`GeoCl Γ` is the closure of `Γ` under division-lattice/height shifts `(setDiv, coreS, divTr)`. When `Γ = anyGeometry`, `GeoCl.base trivial : geoCl anyGeometry D J X` holds unconditionally for every `(D, J, X)`, so `geoCl anyGeometry` is pointwise equivalent to `True`.

### 1.3 `Slots`, `Prm`, `prmR`, `Parameters`, `parametersOfExtension`, and Derived Parameter Records

How `Γ : GeoP` enters the parameter records and propagates into slots, built cores, witnesses, and linked bundles:

- `Slots` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonzeroPlacesOverPrimes.lean:112-122`):
  ```lean
  abbrev OComponent₂ : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (O : Obj2 (w.D Z)) (_ : RowsT K w Z Wt O.p0), Type 1

  structure Slots : Type 2 where
    Rx : RPosition
    Nx : NCondition
    Sx : SPosition
    Ox : OComponent₂
  ```
- `Prm` and `prmR` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ThetaChr.lean:26-34,117`):
  ```lean
  structure Prm (hL : GlobalTheory.Published.LocalLanglandsGL) : Type 2 where
    R : RPosition
    N : NExt hL
    S : SExt
    Γ : GeoP

  @[reducible] def Prm.s (p : Prm hL) : Slots := ⟨p.R, NX hL p.N, SXE p.S, OX p.Γ⟩
  ...
  @[reducible] def prmR (N : NExt hL) (S : SExt) (Γ : GeoP) : Prm hL := ⟨RX, N, S, Γ⟩
  ```
- `Parameters` and `parametersOfExtension` on the `Main.lean` (`ThirdPlaceSeries`) track (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/CoreAltAltBis.lean:19-25,61`):
  ```lean
  structure Parameters (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Type 2 where
    R : RPosition
    N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL
    S : SExt
    Γ : GeoP

  @[reducible] def Parameters.s (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : Slots := ⟨p.R, _root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL p.N, SXE p.S, OX p.Γ⟩
  ...
  @[reducible] def parametersOfExtension (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL := ⟨RX, N, S, Γ⟩
  ```
- Concrete `NExt` extensions and parameter instances:
  - `NEb` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/StrictHenselianAcyclic.lean:60`):
    ```lean
    def NEb : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NE hL K B f T w Z Wt p0 t nch n xd c × PLift (BkLaw (w.D Z))
    ```
  - `NEl` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/SettingsFormsExistList.lean:26-27`):
    ```lean
    def NEl : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEb hL K B f T w Z Wt p0 t nch n xd c ×
      PLift (ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh cDep K.s.b)
    ```
  - `NEo` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUnlocalizedSaturatedState.lean:32-33`):
    ```lean
    def NEo : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEl hL cDep K B f T w Z Wt p0 t nch n xd c ×
      PLift (Org hL cDep K w Wt nch)
    ```
    (With `ThirdPlaceSeries` twin `extensionWithOrigin` in `ThirdPlaceSeries/ExtensionWithOrigin.lean:26-27`.)
  - `NEa` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/GKeyFin.lean:18-19`):
    ```lean
    def NEa (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (A : AtP) : NExt hL := fun K B f T w Z Wt p0 t nch n xd c =>
      N K B f T w Z Wt p0 t nch n xd c × PLift (A K B f T)
    ```
  - `prm0` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ParMem.lean:137`):
    ```lean
    @[reducible] def prm0 (hL : GlobalTheory.Published.LocalLanglandsGL) : Prm hL := prmR (NEb hL) SExt.none (geoCl anyGeometry)
    ```
  - `prm1` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MultW.lean:44-45`):
    ```lean
    @[reducible] def prm1 (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) : Prm hL :=
      prmR (GlobalTheory.HeightCounting.Up.NEl hL cDep) SExt.none (geoCl anyGeometry)
    ```
    (With `ThirdPlaceSeries` twin `parametersOfDependence` in `ThirdPlaceSeries/Prm1.lean:20-21`: `parametersOfExtension (extensionWithList hL cDep) SExt.none (geoCl anyGeometry)`.)
  - `prmA` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/GKeyFin.lean:21-22`):
    ```lean
    @[reducible] def prmA (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (A : AtP) : Prm hL :=
      prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) A) SExt.none (geoCl anyGeometry)
    ```
- How `Slots.Ox = OX p.Γ` enters cores, witnesses, and linked bundles:
  - `Built` (`NonzeroPlacesOverPrimes.lean:147-168`): has 19 fields (`pin`, `coh`, `g`, `col`, `what₂`, `rx`, `xi`, `lev`, `errX`, `n`, `nx`, `sx`, `ker0`, `ker_eq`, `ker`, `div`, `th`, `obj`, and line 167: `ox : 𝒮.Ox K B f T w Z c.Wt c.O what₂`).
  - `BuiltE`, `GoodE`, `IsBuiltE`, `IsGoodE` (`ThetaChr.lean:85-91`):
    ```lean
    def BuiltE (𝒮 : Slots) : CP := fun K _ _ _ w Z c => ∃ b : Built 𝒮 K w Z c, EntC b.ker
    def GoodE (𝒮 : Slots) : CP := fun K B f T w Z c => BuiltE 𝒮 K B f T w Z c ∧ GoodO (w.D Z) c.O.nch c.O.xd
    def IsBuiltE (𝒮 : Slots) : V4.Slot := positionOf (BuiltE 𝒮)
    def IsGoodE (𝒮 : Slots) : V4.Slot := positionOf (GoodE 𝒮)
    ```
  - `Wit` and `WPt` (`DsigEq.lean:24-65`): `Wit` has 26 fields including line 46 `ox : 𝒮.Ox K B f T w Z Wt O what₂`; `WPt 𝒮 K` packages `(B, f, T, w, Z, O, x : Wit 𝒮 K w Z (ofObj O))`.
  - `IsLinked` (`IsLinked.lean:80-81`) and `linkOf` (`DsigEq.lean:70-72`):
    ```lean
    def linkOf {𝒮 : Slots} {Bd : GlobalTheory.Fc.BdT} (P : PinT 𝒮 Bd) : GlobalTheory.Fc.LkT Bd := fun K β c b =>
      ∃ (p : WPt 𝒮 K) (b' : Bd (p.w.D p.Z) p.O c), P K p c b' ∧
        (⟨β.D, β.O, b⟩ : Σ (D : D7) (O : Obj D), Bd D O c) = ⟨p.w.D p.Z, p.O, b'⟩

    def IsLinked (p : Prm hL) : GlobalTheory.Fc.LkT GlobalTheory.Fc.Bundle :=
      linkOf (𝒮 := p.s) (Bd := GlobalTheory.Fc.Bundle) fun _ q _ b => Nonempty (BWit (p := p) q b)
    ```
  - Note: `Lv2`, `Lv3`, and `Lv4` (`NonzeroPlacesOverPrimes.lean:124-146`) do **not** contain an `𝒮.Ox` field at all (`Lv2` has `rx`, `Lv3` adds `nx`, `Lv4` adds `sx`); `ox` enters **only** at `Built` / `Wit` (via `DivEx`, lines 183-185).

---

## 2. Signatures of Every Lemma on the Path Receiving `geoCl anyGeometry`

*(All signatures below are **VERIFIED** verbatim from source; confidence: **100%**.)*

The lemmas on the path divide cleanly into **three groups**:

### Group A: Lemmas Universally Quantified in `∀ Γ : GeoP` (Instantiated at `geoCl anyGeometry` at Call Sites)

Every single universal/consumption-side theorem — plus the set-division transport theorems and `ExBL` / `ExportF` / `MultQ` — is proved **uniformly for an arbitrary `Γ : GeoP`**:

| Lemma | File & Line | Quantification over `Γ` |
|---|---|---|
| `GlobalTheory.Glob.open_and_linked_of_stronger_extension` (`_alt`) | `Proofs/GlobalInterpolation/OpenAndLinkedMonoExtension.lean:12` (`ThirdPlaceSeries/OpenAndLinkedOfStrongerExtension.lean:28`) | **`∀ ... (Γ : GeoP)`** |
| `GlobalTheory.Fc.StageOne.rowFun_at_gridA` (`_alt`) | `Proofs/GlobalInterpolation/LargeFieldLinkedBundlesExist.lean:15` (`ThirdPlaceSeries/RowFunAtGridA.lean:32`) | **`∀ ... (Γ : GeoP)`** |
| `GlobalTheory.Glob.CovolRow.linked_bundles_l3_of_open` (`_alt`) | `Proofs/GlobalInterpolation/OpenImpliesL3AtLinkedBundles.lean:15` (`ThirdPlaceSeries/LinkedBundlesL3OfOpen.lean:31`) | **`∀ ... (Γ : GeoP)`** |
| `GlobalTheory.T.geometric_condition_large_grid` (`_alt`) | `Proofs/IwasawaDecomposition/GeometricConditionLargeGridStatement.lean:12` (`ThirdPlaceSeries/RowGeoAtGridAStatement.lean:19`) | **`∀ ... (Γ : GeoP)`** |
| `GlobalTheory.T.class_sum_divisor_all` (`_alt`) | `Proofs/IwasawaDecomposition/ClassSumDivisorAllStatement.lean:10` (`ThirdPlaceSeries/LinkedTiesStatement.lean:22`) | **`∀ ... (Γ : GeoP)`** |
| `GlobalTheory.Fc.AllAtMemberStage0.allRows_of_open0` (`_alt`) | `Proofs/GlobalInterpolation/LinkedBundlesOfCasselmanWallach.lean:52` (`ThirdPlaceSeries/LinkROfIsLinked.lean:50`) | **`∀ ... (Γ : GeoP)`** |
| **All 12 component theorems of `Open0` / `OpenParameterStatements`:** `entry_hPA_at_parameters`, `entry_point_g_at_parameters`, `nonempty_extension_entries`, `entries_combined_real`, `main_theorem_published_inputs_third`, `bk_law_entries`, `real_group_inputs_combined`, `harish_chandra_inputs_combined`, `linked_bundles_good_of_local_langlands`, `good_ft_entries`, `geometric_zero_condition_all`, `weil_unitary_entries` (and all 12 `ThirdPlaceSeries` twins) | `Proofs/GlobalInterpolation/*Statement.lean`, `Proofs/DecoratedLatticeProofs/MainTheoremPublishedInputsThirdStatement.lean:35`, `Proofs/IwasawaDecomposition/GeometricZeroConditionAllStatement.lean:10` (and `ThirdPlaceSeries/` twins) | **`∀ ... (Γ : GeoP)`** for **all 12/12** |
| `UpperTheory.N.boundAtTwoThree_at_prm_of_prints` (`boundAtTwoThree_linked_of_recT`) | `Development/AutomorphicArithmetic/ResidueCharacters/ClosedOfAll.lean:22` (`ThirdPlaceSeries/At23OfAll.lean:24`) | **`∀ (p : Prm hL)`** (arbitrary `p.Γ`) |
| `GlobalTheory.T.residual_at_of_nonempty_exceptional` | `Proofs/InertiaEigenvalues/ResidualAtOfNonemptyExceptionalStatement.lean:19` | **`∀ ... (Γ : GeoP)`** |
| `GlobalTheory.T.local_representation_inputs_imply` (`member_multiplicatively_closed_alt`) | `Proofs/IwasawaDecomposition/LocalRepresentationInputsImplyStatement.lean:28` (`ThirdPlaceSeries/MultiplicativeClosurePrimeMem.lean:47`) | **`∀ ... (Γ : GeoP)`** |
| `GlobalTheory.T.automorphy_of_hypotheses` (`ExportF`) | `Proofs/IwasawaDecomposition/AutomorphyOfPublishedInputsStatement.lean:27` | **`∀ ... (Γ : GeoP)`** |
| `GlobalTheory.T.geometric_parameter_uniform` (`ExBL`) | `Proofs/IwasawaDecomposition/GeometricParameterUniformStatement.lean:32` | **`∀ ... (Γ : GeoP)`** |
| `GlobalTheory.T.built_linked_large_grid` (`compatibleSystem_weilBlock_ne_alt`) | `Proofs/IwasawaDecomposition/BuiltLinkedLargeGridStatement.lean:12` (`ThirdPlaceSeries/ExistsWeilBlockNeAtMember.lean:41`) | **`∀ ... (Γ : GeoP)`** |
| `GlobalTheory.T.member_preserved_large_grid` (`memberE_extensionWithAtProperty_of_evLgG`) | `Proofs/IwasawaDecomposition/MemberPreservedLargeGridStatement.lean:12` (`ThirdPlaceSeries/IsBuiltEPrmAIffStatement.lean:15`) | **`∀ ... (Γ : GeoP)`** |
| `GlobalTheory.T.divisionGeometryScalars_transfer_setDivision` (`oAt_setDiv`) | `Proofs/IwasawaDecomposition/DivisionGeometryScalarsTransferSetDivisionStatement.lean:9` | **`∀ (Γ : GeoP) ...`** (for `geoCl Γ`) |
| `GlobalTheory.T.movable_geometric` (`slot_mv_extension_with_origin_geo_cl`) | `Proofs/IwasawaDecomposition/SlotStageMovesGeometricStatement.lean:18` (`ThirdPlaceSeries/SlotMvPrmRNelStatement.lean:15`) | **`∀ ... (Γ : GeoP)`** (for `geoCl Γ`) |
| `GlobalTheory.NLink.Final.movable_pin` (`slot_mv_extension_with_list_geo_cl`) | `Proofs/InertiaEigenvalues/LinkOfClosedAtFamily.lean:48` (`ThirdPlaceSeries/SlotMvPin.lean:20`) | **`∀ ... (Γ : GeoP)`** (for `geoCl Γ`) |
| `GlobalTheory.T.lv3Mv_prmR_NEo_and_NEog` & `has3_neo_of_localLanglands` | `Proofs/IwasawaDecomposition/Lv3StageMovesSpectralStatement.lean:18`, `MemberBuiltLinkedGeometric.lean:22-24` | **`∀ ... (Γ : GeoP)`** |
| `GlobalTheory.T.parameter_of_discrete_series_ray` (`_alt`) | `Proofs/IwasawaDecomposition/ParameterOfDiscreteSeriesRay.lean:104` (`ThirdPlaceSeries/ParameterOfDiscreteSeriesRay.lean:69`) | **`∀ ... (Γ : GeoP)`** |

Selected verbatim quotes of key Group A signatures:

```lean
-- OpenAndLinkedMonoExtension.lean:12
theorem open_and_linked_of_stronger_extension :
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N N' : NExt hL) (S : SExt) (Γ : GeoP),
      (∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c)) →
      (∀ H : ∀ 𝒜 : FamClass, RawSel Bundle 𝒜 → Prop,
        RL.At (prmR N S Γ) (fun Q L => Row Q L H) → RL.At (prmR N' S Γ) (fun Q L => Row Q L H)) ∧
      (S0.Open0 (prmR N S Γ) → S0.Open0 (prmR N' S Γ))
```

```lean
-- LargeFieldLinkedBundlesExist.lean:15
theorem rowFun_at_gridA : ... →
    ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP),
      (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
        Nonempty (GlobalTheory.HeightCounting.Up.NEl hL CF K B f T w Z Wt p0 t nch n xd c)) →
      S0.Open0 (prmR (NEa hL N (GridA CF)) S Γ) →
      RL.At (prmR (NEa hL N (GridA CF)) S Γ) S0.FunctorialityCondition
```

```lean
-- OpenImpliesL3AtLinkedBundles.lean:15
theorem linked_bundles_l3_of_open : ... →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP),
      (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
        Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) →
      S0.Open0 (prmR N S Γ) → RL.At (prmR N S Γ) S0.CovolumeBound'
```

```lean
-- LinkedBundlesOfCasselmanWallach.lean:52
theorem allRows_of_open0 : ... →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP) (NN : FamClass → Prop),
      S0.Open0 (prmR N S Γ) →
      RL.At (prmR N S Γ) S0.CovolumeBound' →
      RL.At (prmR N S Γ) S0.FunctorialityCondition →
      RL.At (prmR N S Γ) (fun Q L => R1.PredicateAtBundlePoints Q L NN) →
      AllRows KPx (IsBuiltE (prmR N S Γ).s) (IsGoodE (prmR N S Γ).s) (IsLinked (prmR N S Γ)) NN DRS
```

```lean
-- GeometricParameterUniformStatement.lean:32
theorem _root_.GlobalTheory.T.geometric_parameter_uniform : ... →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL),
      p = prmR N SExt.none Γ → ... → PositionMv p.s →
      (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat) →
      GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (IsLinked p)
```

```lean
-- SlotStageMovesGeometricStatement.lean:18
theorem _root_.GlobalTheory.T.movable_geometric :
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (Γ : GeoP),
      PositionMv (prmR (NEo hL cDep) SExt.none (geoCl Γ)).s
```

### Group B: Wrapper Theorems Whose Signatures Fix `prm1` / `geoCl anyGeometry` (Purely by Calling Group A)

These theorems are **not** quantified over `Γ` in their stated signatures, but their proofs simply instantiate Group A lemmas at `geoCl anyGeometry` without ever touching `anyGeometry` directly:

- `GlobalTheory.T.open_first_parameters_of_hypothesesUE` (`OpenFirstParametersOfPrintsUEStatement.lean:9`) → `open_of_hypothesesUE` (`OpenFirstParametersOfPublishedUE.lean:26-59`):
  ```lean
  theorem open_of_hypothesesUE : S0.HypothesesUE → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ), S0.Open0 (prm1 hL cDep)
  ```
  (And `ThirdPlaceSeries/OpenOrbitOfUnramifiedExponents.lean:39-75`: `open0_of_unitary_group_hypotheses`.)
  Both proofs consist solely of calling the 12 Group A theorems at `SExt.none (geoCl anyGeometry)` and packaging the tuple `⟨hPA, hLam, hDiv, hDc, hJ, hTie, hLab, hGood.2, hGeo, hMi.2, hKap, hDf⟩`.
- `GlobalTheory.NLink.Final.main` (`LinkOfClosedAtFamily.lean:68-74`) and `UpperTheory.GalC.final_of_alt` (`ThirdPlaceSeries/LinkNFam.lean:75-86`): instantiate `movable_pin` / `slot_mv_extension_with_list_geo_cl` and `residual_at_of_nonempty_exceptional` / `atMem_at_wit_alt` at `geoCl anyGeometry`.
- `GlobalTheory.Fc.S0.StageU.nonempty_hyps_of_classicalTheoremsUE` (`NonemptyHypsOfPublishedUE.lean:30-50`):
  ```lean
  theorem nonempty_hyps_of_classicalTheoremsUE : S0.HypothesesUE → S0.RowRat →
      ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (A : GroupRetwisting.AtP), EvLgG A →
        RL.At (prm1 hL cDep) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => GlobalTheory.NLink.BoundAtTwoAndThreeForFamily Fm) →
        RL.At (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)) S0.FunctorialityCondition →
        RL.At (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)) S0.CovolumeBound' →
        Nonempty (Hyps S0.NL DRS)
  ```
  (And `ThirdPlaceSeries/HypothesesNonemptyOfUnramifiedExponents.lean:41-61`: `hypotheses_nonempty_of_unramified_exponents_alt` producing `Nonempty (HypsAlt S0.NL DefiniteSideCondition)`.)
  It combines `linked_bundle_construction_exists` (Group C below, which fixes `geoCl anyGeometry`), `open_first_parameters_of_hypothesesUE`, `NLink.Final.main`, `open_and_linked_of_stronger_extension`, and `allRows_of_open0`, and feeds the result to `nonempty_hyps_of_allRows`.

### Group C: The Single Existential-Witness Chain Where `anyGeometry` Is Actually Used

This is the **only** place in the entire proof where `anyGeometry = True` is actually used (to construct `OAt.geo`):

1. **`divEx_prov` / `divEx_of_ox`** (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:204-213`):
   ```lean
   theorem divEx_prov (𝒮 : Slots) (hOx : 𝒮.Ox = OX anyGeometry) : DivEx 𝒮 :=
     StepW.of_all fun _ _ _ _ w _ _ hpin Z l =>
       let ⟨Y, h1, h2, h3, h4⟩ := exists_divT w hpin.some Z l
       ⟨Y, h1, h2, h3, fun O t hX hp ht => by
         rw [hOx]
         exact ⟨⟨trivial, lamAre_heq hp ht (hX ▸ h4)⟩⟩⟩

   theorem divEx_of_ox : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → ∀ 𝒮 : Slots,
       𝒮.Ox = OX anyGeometry → DivEx 𝒮 :=
     fun _ _ _ 𝒮 hOx => divEx_prov 𝒮 hOx
   ```
   Here `exists_divT` (lines 178-192) builds a `DivX (w.D Z)` starting from `x0` (lines 57-122, which has `Surf := Empty`, `SurfFp := Empty`, `geo := geoExample _`, grafted via `ReQ.reQ` and `GeoGraft.graft`), proving `Nonempty (DivT l.n Y)`, `MjAre`, `kapR`, and `LamAre l.what₂.r.Z Y`. Then `divEx_prov` builds `Nonempty (OAt anyGeometry t O.X)` with `geo := trivial` and `lam := lamAre_heq hp ht (hX ▸ h4)`.
2. **`divEx_geoCl`** (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PublishedInputsImplyConclusion.lean:39-49`):
   ```lean
   theorem divEx_geoCl (h1 : GlobalTheory.NT.RayField) (h2 : GlobalTheory.Published.PrincipalIdealSt) (h3 : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt)
       (R : RPosition) (N : NCondition) (S : SPosition) : DivEx ⟨R, N, S, OX (geoCl anyGeometry)⟩ := by
     have h := GlobalTheory.Mem.Top.DivRec.divEx_of_ox h1 h2 h3 ⟨R, N, S, OX anyGeometry⟩ rfl
     ...
     obtain ⟨o⟩ := hY4 O t e1 e2 e3
     exact ⟨⟨geoCl_of o.geo, o.lam⟩⟩
   ```
3. **Propagation upward to `MemberE`:**
   - `memberE_closing` (`PublishedInputsImplyConclusion.lean:74-83`; `ThirdPlaceSeries/MemberEClosing.lean:17-26`) invokes `divEx_geoCl` twice and passes it into `exists_member_of_construction_steps_secondPass` (`ExistsMemberOfConstructionStepsSecondPass.lean:38-61`), which calls `stepW_core` (`ExistsConstructedCoreOfAllConstructionStages.lean:67-126`, lines 83 & 125 placing `ox` into `Built.ox`) to prove `MemberE (prmR N SExt.none (geoCl anyGeometry)).s`.
   - `memberE_exBL_of_pair` / `memberE_exBL_prm1` (`MemberBuiltLinkedGeometric.lean:40-77`; `ThirdPlaceSeries/ExistsBaseLatticeOfPrime.lean:36-81`) and `member_bundles_large_ue` (`LinkedBundleConstructionExists.lean:25-56`; `ThirdPlaceSeries/MemberBundlesLargeUnramifiedExponents.lean:34-70`) combine `MemberE` with `ExBL` (from `geometric_parameter_uniform` / `movable_geometric`).

---

## 3. Polarity Analysis, Constructions, and Eliminations

### 3.1 Exact Polarity of `Γ : GeoP` Across the Architecture

*(Verified directly from the unfolded definitions in `OverIx.lean`, `ThetaChr.lean`, `DsigEq.lean`, `IsLinked.lean`, `NotBaseCondFalse.lean`, `ValidForConstructedPointClassesEventuallyWorking.lean`, `EventuallyAllScaleContextsAndOfBoth.lean`, and `CoreSlotConstructionMonoFewerCoresBothPasses.lean`; confidence: **100%**.)*

Let `Γ₁ ≤ Γ₂` denote pointwise implication `∀ D J X, Γ₁ D J X → Γ₂ D J X`. Because `OAt Γ t X` contains `geo : Γ ...` covariantly:
- `OAt Γ`, `OX Γ`, `Built`, `BuiltE`, `IsBuiltE`, `GoodE`, `IsGoodE`, `Wit`, `WPt`, `BWit`, and `IsLinked` are all **monotone (covariant / positive)** in `Γ`.
- Setting `Γ := geoCl anyGeometry` (pointwise equivalent to `True`) makes `IsBuiltE p.s`, `IsGoodE p.s`, `WPt p.s K`, and `IsLinked p` the **largest possible** sets/relations (no core or witness is excluded by `Γ`).

Now trace the polarity of `(Q, Q', Lk) = (IsBuiltE p.s, IsGoodE p.s, IsLinked p)` — and hence of `Γ` — in every consumer:

1. **Strictly CONTRAVARIANT (negative) in `Γ` — `Γ = True` is the HARDEST / STRONGEST statement to prove:**
   - `LargeBaseCondition KP Q R` (`EventuallyAllScaleContextsAndOfBoth.lean:42-44`): `∀ ... c, Q ... c → R ... c`. (`Q` is negative; proved antitone in `largeBaseProperty_anti`, `CoreSlotConstructionMonoFewerCoresBothPasses.lean:57-59`.)
   - `RowE Q Lk E` (`ValidForConstructedPointClassesEventuallyWorking.lean:261-262`): `EvP fun κ K => ∀ β, β.Is Q → ∀ c b, Lk K β c b → E ...`. (Both `Q` and `Lk` are negative.)
   - `Row Q Lk H` (`ValidForConstructedPointClassesEventuallyWorking.lean:268-269`): `∃ E, RowE Q Lk E ∧ ∀ 𝒜 σ, IsSel Q Lk E 𝒜 σ → H 𝒜 σ`. Inside `IsSel` (line 264-266), `Built Q Lk` (line 250-252) occurs positively, and `IsSel` sits to the left of `→`, so `Q` and `Lk` occur negatively here too (neg × pos × pos = neg; proved antitone in `row_mono_id`, `CoreSlotConstructionMonoFewerCoresBothPasses.lean:52-55`).
   - `Lg1 KP Q Q' (Row · Lk H)` = `RL.At p (Row · · H)` (`AllRows.lean:15-16`, `GoodReductionCondition.lean:45-46`): proved antitone in `(Q, Q', Lk)` in `eventually_coreProperty_mono_fewerCores` (`CoreSlotConstructionMonoFewerCoresBothPasses.lean:61-66`).
   - Therefore **`Open0`**, **`OpenParameterStatements`**, **`AllRows`**, **`AllRowsAlt`**, **`FunctorialityCondition`**, **`CovolumeBound'`**, **`ExportF`** (`NotBaseCondFalse.lean:55-58`), and **`MultQ`** (`ParMem.lean:139-140`, `∀ q : WPt p.s K, MultEq ...`) are **all strictly contravariant in `Γ`**.
   - **Logical consequence:** Proving `Open0`, `AllRows`, `ExportF`, `MultQ`, `FunctorialityCondition`, and `CovolumeBound'` at `Γ = geoCl anyGeometry` proves them over the **maximal** family of cores/witnesses — **strictly stronger** than proving them for `Γ = geoOf Q`.

2. **BIPOLAR / MIXED in `Γ` (preserved uniformly in `∀ Γ : GeoP`):**
   - `PositionMv (prmR N SExt.none (geoCl Γ)).s` (`PositionMv.lean:13-21`) and `WitMv` (`PositionMv.lean:23-26`): take an existing `x : Wit` (negative) and construct a moved `ox : OAt (geoCl Γ)` (positive). Proved for arbitrary `Γ : GeoP` via `GeoCl.step`.
   - `ExBL KP Q Q' Lk` (`EventuallyAllScaleContextsAndOfBoth.lean:71`, `ValidForConstructedPointClassesEventuallyWorking.lean:259`): `Q` and `Q'` are negative (`LargeBaseCondition`, `∀ β, β.Is (sAnd Q' R) → ...`), while `Lk` (`IsLinked p`) is positive (`∃ b, Lk K β c b`). Proved uniformly for arbitrary `Γ : GeoP` in `geometric_parameter_uniform` (`GeometricParameterUniform.lean:40-48`), because `WitExE` produces `q : WPt p.s K` by transporting the `Built` witness already inside `β.Is (IsGoodE p.s)`.
   - `SecondG KP Q Q'` (`NotBaseCondFalse.lean:68-69`): `Pass KP Q (HasCore (Q ∧ TwAllAt ∧ Q'))` has `Q` negatively on the left and `Q ∧ Q'` positively on the right.

3. **Strictly COVARIANT (positive) in `Γ` — `Γ = True` trivializes ONLY the `OAt.geo` obligation:**
   - `DivEx 𝒮` (`NonzeroPlacesOverPrimes.lean:183-185`): requires producing `Nonempty (𝒮.Ox ...)` = `Nonempty (OAt Γ t O.X)`.
   - `FirstG KP (IsBuiltE 𝒮)` (`NotBaseCondFalse.lean:53`): requires producing `HasCore (IsBuiltE 𝒮)`, i.e., `∃ ... c, IsBuiltE 𝒮 ... c`.
   - Here — and **only** here — setting `Γ := geoCl anyGeometry` discharges the `OAt.geo` obligation trivially via `trivial` + `GeoCl.base`.
   - Crucially, setting `Γ := geoCl anyGeometry` does **not** trivialize `OAt.lam : LamAre t.r.Z O.X` (which is still proved via `lamAre_of_eq` / `lamAre_heq` in `TupPinsOfMuIsW.lean:51-55,209`), nor any of the other 18 fields of `Built` (`rx`, `nx`, `sx`, `ker`, `div`, `th`, `obj`, etc.) or `Core`, nor does it make `IsBuiltE` empty (indeed, `NotBaseCondFalse.lean:225-266` explicitly tests `¬ FirstG KP (fun _ _ _ _ _ => False)`).

4. **EXISTENTIALLY ELIMINATED at `UpperTheory.Top.classSel` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ClassSel.lean:14-28`):**
   ```lean
   theorem classSel : ... →
     ∀ (KP : ∀ B : Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Bd : BdT) (Lk : LkT Bd)
       (H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop) (cT : ℝ → ℝ → ℝ),
       (DC.MinkDiv → GroupRetwisting.BaseCond KP ∧ GroupRetwisting.FirstG KP Q ∧ GroupRetwisting.ExportF KP Q ∧ GroupRetwisting.SecondG KP Q Q') →
       ExBL KP Q Q' Lk → RowL KP Q Q' Lk H →
       ∃ (𝒜 : FamClass) (σ : RawSel Bd 𝒜),
         (DC.MinkDiv → ExD 𝒜 cT) ∧
         (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → DQ.Duty7 Fm ∧ DQ.MtStableF Fm) ∧
         IsSel Q' Lk (fun _ _ _ _ _ => True) 𝒜 σ ∧ H 𝒜 σ
   ```
   `nonempty_hyps_of_allRows` (`NonemptyHypsOfAllRows.lean:44-96`, and `_alt` in `ThirdPlaceSeries/NonemptyHypsOfAllRows.lean:49-101`) discards the `IsSel Q' Lk ...` component (binding it to `-` at line 44 / line 49) and retains only `(𝒜, σ)` and the 44 properties packaged into `Hyps` / `HypsAlt`. At this cut, `Q`, `Q'`, `Lk`, `p`, and `Γ` **disappear completely** from the types.

### 3.2 Exhaustive Repo-Wide Inventory of Constructions and Eliminations of `OAt`, `OAt.geo`, `GeoCl`, and `geoOf`

*(**VERIFIED** via fixed-string `git grep -F` across the entire `src/` tree — all 175k files — for `anyGeometry`, `geoCl`, `GeoCl`, `GeoCl.`, `OAt`, `OAt.`, `.ox`, `.Ox`, `Built.mk`, `Wit.mk`, `OAt.mk`, `DivEx`, `oAt_any`, `oAt_geoOf`, `geoOf_surf`, `geoOf_set`, `isGeoOf_set`; confidence: **99%+** that no hidden elimination exists, with the minor caveat noted below for anonymous destructuring.)*

#### Every Construction of `OAt` / `GeoCl` in the Entire Repository:
1. `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:209` (**on RH path**):
   ```lean
   exact ⟨⟨trivial, lamAre_heq hp ht (hX ▸ h4)⟩⟩
   ```
   Constructs `Nonempty (OAt anyGeometry t O.X)`.
2. `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotGeoClFalse.lean:28` & `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PublishedInputsImplyConclusion.lean:49` (**on RH path**):
   ```lean
   -- NotGeoClFalse.lean:28
   theorem geoCl_of {Γ : GeoP} {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} (h : Γ D J X) : geoCl Γ D J X := GeoCl.base h
   -- PublishedInputsImplyConclusion.lean:49
   exact ⟨⟨geoCl_of o.geo, o.lam⟩⟩
   ```
   Lifts `OAt anyGeometry` into `OAt (geoCl anyGeometry)` via `GeoCl.base`.
3. `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DivisionGeometryScalarsTransferSetDivision.lean:105-108` (**on RH path**):
   ```lean
   refine ⟨⟨?_, ?_⟩⟩
   · exact (by with_unfolding_all exact ((GeoCl.step (Γ := Γ) (D := (w.st Z).toD7) N h hp.geo) :))
   · exact (by with_unfolding_all exact ((lamAre_copy ... hp.lam) : _))
   ```
   Moves `OAt (geoCl Γ)` across `setDiv` via `GeoCl.step` (uniformly in `Γ : GeoP`).
4. `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotLamAreShift.lean:152-161` (**NOT on RH path — never called anywhere in `src/`**):
   ```lean
   theorem oAt_any ... : ∃ l, Nonempty (OAt anyGeometry t (...)) := by
     ... exact ⟨_, ⟨trivial, lamAre_set ...⟩⟩
   theorem oAt_geoOf (Q) ... : ∃ l, Nonempty (OAt (geoOf Q) t (...)) := by
     ... exact ⟨_, ⟨geoOf_set hc hX _, lamAre_set ...⟩⟩
   ```

#### Every Elimination / Projection of `OAt`, `OAt.geo`, `GeoCl`, and `geoOf` in the Entire Repository:
- **Eliminators of `GeoCl` (`GeoCl.rec`, `GeoCl.casesOn`, `cases`/`induction`/`rcases` on `GeoCl`):** **ZERO** anywhere in the entire repository. The only occurrences of `GeoCl` outside `import ...NotGeoClFalse` in all of `src/` are its definition (`NotGeoClFalse.lean:21-28`) and `GeoCl.step` (`DivisionGeometryScalarsTransferSetDivision.lean:106`).
- **Projections of `OAt.geo`:** **ONLY TWO** in the entire repository:
  1. `PublishedInputsImplyConclusion.lean:49`: `geoCl_of o.geo`
  2. `DivisionGeometryScalarsTransferSetDivision.lean:106`: `GeoCl.step (Γ := Γ) ... hp.geo`
  **Both merely pass the proof term `o.geo` / `hp.geo` straight into a `GeoCl` constructor (`base` / `step`) to repackage a new `OAt`. Zero content is ever extracted from `OAt.geo` anywhere on the path to `riemannHypothesis` (or anywhere else in `src/`).**
- **Projections of `.ox` across the entire repository** (excluding the unrelated matrix-block field `.ox` in `CellVolumeMulCoef.lean:331,333`):
  1. `LinkOfClosedAtFamily.lean:61`, `PositionStageMovesGeometric.lean:53`, `ThirdPlaceSeries/SlotMvPin.lean:33`, `ThirdPlaceSeries/SlotMvPrmRNel.lean:35`: pass `x.ox` to `divisionGeometryScalars_transfer_setDivision` (transport only).
  2. **`ParameterOfDiscreteSeriesRay.lean:107`** and **`ThirdPlaceSeries/ParameterOfDiscreteSeriesRay.lean:72`**:
     ```lean
     exact logLam_twArgs ... q.O.X q.x.ox.lam
     ```
     **This IS on the path and genuinely eliminates `OAt.lam` (`LamAre`), never touching `OAt.geo`.**
- **Uses of `geoOf` (`OverIx.lean:16`):** Only referenced in `OverIx.lean:16` (its definition) and `NotLamAreShift.lean:26-36,157-161` (`geoOf_set`, `geoOf_surf`, `oAt_geoOf`), none of which is called anywhere in `src/`! (Other matches for the substring `geoOf` in `RingKrullDimIntegers.lean:600`, `AffineOpenChartCompStructureEqSpMap.lean:503`, `GeoOfMatch.lean:7` are unrelated definitions in different namespaces.)

*(Methodological caveat: Because Lean is not installed, we verified non-elimination syntactically via repo-wide fixed-string greps for `OAt`, `GeoCl`, `OX `, `(OX`, `.ox`, `.Ox`, `OAt.mk`, `Built.mk`, `Wit.mk`, and `cases ... with | mk`. In principle, a term could destructure a local variable of type `OAt` via anonymous `.1` or `let ⟨a, b⟩ := ...` without naming `OAt` or `.geo`; however, the only ways to obtain a term of type `OAt` are via `Built.ox`, `Wit.ox`, `DivEx`, `PositionMv`, or a direct `OAt` hypothesis, and we inspected **every** occurrence of `.ox`, `.Ox`, `OAt`, and `DivEx` in the repository — leaving zero uninspected access paths. Confidence: **99%+**.)*

---

## 4. Independence of the Final Bundle (`Hyps`, `HypsAlt`, `DRS`, `S0.NL`, `Closed`, `LinkN`) from `Γ`, and the `trivial trivial` Arguments in `plugWin`

*(All facts in Section 4 are **VERIFIED** directly from source; confidence: **100%**.)*

### 4.1 Does `Hyps (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DRS` (or `HypsAlt S0.NL DefiniteSideCondition`) Mention `Γ`?

**No — it is syntactically impossible for any of them to mention `Γ`, `GeoP`, `anyGeometry`, `geoCl`, `OAt`, `OX`, `Prm`, or `prmR`.**

Verified by computing the full transitive import closure of each defining module:
- `Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw` (`Hyps`): 10,333 transitive imports — **does NOT import** `OverIx`, `NotGeoClFalse`, `NotLamAreShift`, or `Development/.../ThetaChr`.
- `Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DRS` (`DRS`): 10,934 transitive imports — **none** of those modules.
- `Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Hyps` (`HypsAlt`): 14,794 transitive imports — **none** of those modules.
- `Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefiniteSideCondition`: 15,392 transitive imports — **none** of those modules.
- `Formalism.SharpRestriction.ParamsHeightRankConstant` (`Closed`): 285 transitive imports — **none** of those modules.
- `Formalism.SharpRestriction.GlobalTheoremInputs` (`LinkN`): 310 transitive imports — **none** of those modules.

*(Note: `Formalism.LocalToGlobal.ThetaChr` appears in the closure of `Hyps`/`DRS`, but reading it verified it defines `LocalGlobalCompatibilityData` / `Tied` / `C2` and has no connection to `GeoP` or `Prm`.)*

### 4.2 Unfolding `S0.NL`, `Closed`, `LinkN`, `DRS`, and `Hyps` / `HypsAlt`

- **`S0.NL`** (`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/GeometricWeakTiesOfStrong.lean:36`):
  ```lean
  def NL (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm
  ```
  This is definitionally equal to `fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm` (the exact type expected by `plugAll` / `every_character_of_green_v_win`).

- **`Closed`** (`src/Formalism/SharpRestriction/ParamsHeightRankConstant.lean:157-161`):
  ```lean
  abbrev FamClass : Type 1 := ∀ {eps : ℝ}, FamP eps → Prop

  def Closed (𝒞 : FamClass) (P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop) : Prop :=
    ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ ε1 → ∃ K : TransportedAlt, ∀ (Fm : FamP eps) (CH : ℝ),
      𝒞 Fm → Fm.Large K CH → P Fm CH
  ```
  Asserts that for all sufficiently small `eps > 0`, there is a largeness threshold `K : TransportedAlt` such that every family `Fm` in `𝒞` that is `K`-large (with parameter `CH`) satisfies `P Fm CH`.

- **`LinkN`** (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:40-47`):
  ```lean
  def LinkN_at {D : D7} (L : SizeData₂ D) (j : ℕ) (C : ℝ) : Prop :=
    Summable (vvTerm D) →
      etaSum L j ≤ (L.dZ0 j : ℝ) * (C * ((D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L ^ 2 +
        Real.log L.sc.x ^ 2 * L.Nc) + ∑' l, vvTerm D l)

  def LinkN {eps : ℝ} (Fm : FamP eps) : Prop :=
    ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ShaFinOdd (Fm.D x i) →
      ∀ j ∈ SizeData₂.lifts (Fm.D x i), LinkN_at (Fm.L x i) j C
  ```
  Asserts an eventual explicit upper bound on the twisted-ramification sum `etaSum L j` in terms of `L.dZ0 j`, scale parameters, and the Shafarevich–Tate length series `∑' l, vvTerm D l`, whenever `ShaFinOdd` holds.

- **`DRS`** (`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/DRS.lean:21-31`) and **`DefiniteSideCondition`** (`ThirdPlaceSeries/DefiniteSideCondition.lean:25-35`):
  ```lean
  def DRS : R1.DefT := fun D O c b C CH =>
    ∀ (hok1 : b.P.A3.fam3.Ok3 1) (hsep : b.P.A3.fam3.TypesSep3)
      (hP : CovolumeOntoIsometryConditions (qS b).Rl ... C CH) (hI : PassIn3 (qS b).Rl ... C CH)
      (lam0 C0 ce Sw C1 : ℝ) (H : ∀ u, (ofRecord D O.L b.DH.1.1 b.DH.1.2).NumFacts ...)
      (NuC : ...) (I : DivisionCompatibilityDataThreeSided ...),
      DivTied3 ... NuC I → HEq I b.P.I →
      ∀ u, RowsU b.C.toS.c (pkOf (qS b) hok1 hsep C CH hP hI) (RecNums.ofNum ...) (I.wU u) (Cons.nuOf O.L u (I.eNu u))
  ```
  Asserts that for every bundle `b` satisfying the admissibility/covolume/pass-in/division-compatibility premises, the definite-side row bound `RowsU` holds for every word `u`.

- **`Hyps N DR`** (`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/APerTw.lean:23-92`) and **`HypsAlt N DR`** (`ThirdPlaceSeries/Hyps.lean:22-91`):
  Packages **44 fields** consisting of:
  - Data: a family class `𝒜 : FamClass`, a raw bundle selection `σ : RawSel Bundle 𝒜` (where `Bundle` in `ColumnCompatibleSelection.lean:63-70` bundles `R : RecT`, `S : STiesR`, `P : RowSideFamily`, `pin`, `DH`, `C`, `B : RealTB`), a threshold function `cT : ℝ → ℝ → ℝ`, counting-constant map `c30` with `hc30`, and positive constant `cIc` with `hcI : 0 < cIc`.
  - Existence/design input: `hEx : MinkDiv → UpperTheory.Top.ExS 𝒜 cT` (`ExS.lean:10-12`: produces `DesignChoices` for every `la > 1` and `FReq` with `HostExW`).
  - Pointwise and `Closed`-class analytical/arithmetic/representation-theoretic properties along `(𝒜, σ)`: `hduty`, `hRB`, `hTw`, `hPA`, `hLamP`, `hDivG`, `hDcPtG`, `hTu`, `hn4`, `hLit` (`LitThin`, `MainSup.lean:88-90`), `hWu` (`WuDecayOfGap`, `WuDecayAll.lean:25-27`), `hRF` (`RowsFinDim`, `RowsDef.lean:67-81`), `hTF`, `sTy`/`sNG`/`sM` (`RowsPos.lean:18-47`), `sLp`, `sO`, `h30`, `hInstR` (`VolSigIndep ∧ ClassItemsAt`, `PNamed.lean:14-22`), `selJ`, `jOn`, `hMt`, `rRows` (`H_rRows DR`, `CountsIrreducibilityConstants.lean:193-195` bundling `RowsAt4` and `DR`), `aPt0`, `aPtTw`, `aPer0`, `aPerTw`, `aP10`, `aAtG`, `aC2`, `hServ` (`ServT`, `CountsIrreducibilityConstants.lean:129-143`), `irrC`, `zL`, `tie` (`RealPlaceSecondLayerConditions`, `LinkTied.lean:51-53`), `hU` (`∀ D, MassRatioUnderVolume D`, `MassRatioUnfoldedOfTheoremTwo.lean:12`), `hG` (`∀ D, GenusMassAt D 2`, `DiscreteSeriesOfFormalDegree.lean:112-114`), and `nRest : N (D3 3 𝒜)`.

  **Verified:** None of the 44 fields of `Hyps` or `HypsAlt` is literally `True`.

### 4.3 What Are the Two `trivial` Arguments Passed to `GlobalTheory.Fc.shape_of` in `plugWin`?

In `src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:8-11`:
```lean
theorem UpperTheory.Top.plugWin (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (Hyps (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DRS)) : Formalism.HC.ZeroFreeAll :=
  h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
    (GlobalTheory.Fc.shape_of _ _ _ _ (UpperTheory.Top.shapeWin hG) trivial trivial h) fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)
```
And identically on the `Main.lean` track in `ThirdPlaceSeries/TopPlug.lean:12-15`:
```lean
theorem UpperTheory.Top.zero_free_all_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)) : Formalism.HC.ZeroFreeAll :=
  h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
    (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (_root_.UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h) fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)
```

Unfolding `shape_of`, `TopShape`, and `shapeWin`:
- `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ShapeOf.lean:6,14`:
  ```lean
  theorem GlobalTheory.Fc.of_hyps (V NR : Prop) (N : FamClass → Prop) (G : Prop) (t : TopShape V NR N G) (hV : V) (hR : NR) (h : Hyps N DRS) : G
  theorem GlobalTheory.Fc.shape_of : ∀ (V NR : Prop) (N : FamClass → Prop) (G : Prop), TopShape V NR N G → V → NR → Hyps N DRS → G
  ```
- `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/TopShape.lean:15-92`:
  ```lean
  set_option linter.unusedVariables false in
  def TopShape (V NR : Prop) (N : FamClass → Prop) (G : Prop) : Prop :=
    ∀ (𝒜 : FamClass) ... (hVC : V) ... (nR : NR) ... , G
  ```
- `src/Development/AutomorphicArithmetic/CharacterBoxes/ShapeWin.lean:27-28`:
  ```lean
  theorem UpperTheory.Top.shapeWin : GlobalTheory.GLq.Green → GlobalTheory.Fc.TopShape True True (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) UpperTheory.Top.TopG := by
    intro hGreen 𝒜 cT hEx ... hVC ... nR ...
  ```
  (And identically in `ThirdPlaceSeries/ShapeOf.lean:24,31`, `ThirdPlaceSeries/TopShapeAlt.lean:24,50,84`, `ThirdPlaceSeries/TopShape.lean:33-34`.)

**Verified:**
- The two `trivial` arguments are `hV : V` and `hR : NR` where `V := True` and `NR := True`.
- Neither `V` nor `NR` is a field of `Hyps` / `HypsAlt`; both are **extra hypothesis parameters** of `TopShape V NR N G` that `shapeWin` (and `shape_closed_link_n_of_green`) intros at line 28 (resp. line 34) and **never uses**.
- Because `V` and `NR` occur **negatively** (as premises) in `TopShape V NR N G`, instantiating `V := True` and `NR := True` makes `shapeWin` **strictly stronger** (it proves `TopG` *without* needing two legacy hypotheses that were eliminated from an earlier version of the argument). Passing `trivial trivial` at the call site simply discharges those unused `True` premises.

---

## 5. Logical Evaluation: Is the Critic's Inference Valid?

### What Is Verified vs. What Is Inferred

- **VERIFIED from source (confidence: 99–100%):**
  1. The critic's **factual premises** about `Γ` are accurate: `anyGeometry` is `fun _ _ _ => True` (`OverIx.lean:19`); `geoCl anyGeometry` is passed into `prmR` / `prm1` / `parametersOfExtension` on both the `EveryCharacterE.lean` and `Main.lean` (`ThirdPlaceSeries`) tracks; `divEx_prov` fills `OAt.geo` with `trivial` (`TupPinsOfMuIsW.lean:209`, lifted via `GeoCl.base` in `PublishedInputsImplyConclusion.lean:49`); `geoOf` (`OverIx.lean:16`) and `geoOf_surf` (`NotLamAreShift.lean:30`) are never called anywhere on the path to `riemannHypothesis`; and `OAt.geo` / `GeoCl` is never eliminated to extract any mathematical property.
  2. However, `OAt.lam` (`LamAre`) is **not** trivialized and **is** eliminated on the RH path (`ParameterOfDiscreteSeriesRay.lean:107`, `ThirdPlaceSeries/ParameterOfDiscreteSeriesRay.lean:72`).
  3. Every universal/consumption lemma (`Open0`'s 12 theorems, `open_and_linked_of_stronger_extension`, `rowFun_at_gridA`, `linked_bundles_l3_of_open`, `allRows_of_open0`, `ExportF`, `MultQ`, `ExBL`, `PositionMv`, etc.) is proved uniformly in `∀ Γ : GeoP` (or `∀ Γ : GeoP` for `geoCl Γ`) and is **contravariant** in `Γ` wherever `Γ` restricts a quantified domain.
  4. The final hypothesis bundle `Hyps S0.NL DRS` (and `HypsAlt S0.NL DefiniteSideCondition`) does **not** mention `Γ` (nor transitively import `OverIx` or `NotGeoClFalse`), contains no `True` fields, and `Γ` is existentially eliminated at `classSel`. The `trivial trivial` arguments in `plugWin` / `zero_free_all_of_green_v_win` discharge two unused `True` premise slots in `TopShape`, strengthening `shapeWin`.

- **INFERRED (logical conclusion; confidence: 100% for the logical validity of the inference step itself, conditional on Lean kernel checking):**
  1. **The critic's inference (`Γ := True ⇒ witness is bunk ⇒ RH proof is invalid/vacuous`) is logically INVALID.**
     Schematically, the proof executes a valid cut with an auxiliary predicate `Γ` that does not appear in the final conclusion `C` (`Nonempty (Hyps ...)` → `RiemannHypothesis`):
     - Existential branch (`MemberE` via `divEx_geoCl`): proves `∃ x, A(x) ∧ Γ(x)` at `Γ := geoCl anyGeometry` (where `A(x)` is all non-`geo` data including `LamAre`, `KerT`, `EntC`, `RowsT`, `NX`, `SX`, `DivT`, `ThT`, `ObjT`, `GoodO`).
     - Universal branch (`Open0`, `AllRows`, `ExportF`, `MultQ`, `ExBL`): proves `∀ Γ, (∀ x, A(x) ∧ Γ(x) → B(x))`, which when instantiated at `Γ := geoCl anyGeometry` yields the **strongest** instance `∀ x, A(x) → B(x)` (requiring *no* `geoOf` hypothesis at all!).
     - Cut (`classSel`): combines `∃ x, A(x)` and `∀ x, A(x) → B(x)` to deduce `∃ x, A(x) ∧ B(x)` → `Nonempty (Hyps S0.NL DRS)` → `RiemannHypothesis`.
     Choosing `Γ := True` does **not** introduce vacuity or unsoundness: it shows that the `geoOf Q` condition (and the `OAt.geo` field) is **logically superfluous** to the formalized proof — a vestigial parameter from a refactored architecture whose downstream consumers never needed it. Calling a proof invalid because an unused auxiliary predicate was set to `True` commits a **polarity / existential-elimination fallacy**.
  2. **Lean kernel soundness caveat:** In Lean 4's dependent type theory, a closed theorem `theorem riemannHypothesis : RiemannHypothesis` with no free hypotheses **cannot be "vacuous"** due to a trivial intermediate witness. Once the Lean kernel verifies a closed proof term of Mathlib's `RiemannHypothesis` using only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and no `sorry`, every intermediate witness (`anyGeometry`, `geoCl`, `x0`, etc.) has already been legitimately eliminated inside the proof; the resulting theorem is valid regardless of whether an intermediate witness is "degenerate" or "trivial". *(Scope boundary: because Lean is not installed and Task B audits only `Γ`, this report does **not** independently verify axiom cleanliness, absence of `sorry`/environment hacks, or full typechecking of the 17.4M-line codebase; those belong to separate audit tasks.)*

---

## VERDICT

The critic's factual observation that `anyGeometry` is `fun _ _ _ => True`, that `geoCl anyGeometry` is instantiated on the proof path (via `divEx_prov` filling `OAt.geo` with `trivial` and `divEx_geoCl` wrapping it in `GeoCl.base`), and that `geoOf` / `OAt.geo` are never eliminated on the path to `riemannHypothesis` is **verified from source**, yet her conclusion that this renders the proof of `RiemannHypothesis` vacuous or invalid is **logically invalid**. Every downstream theorem consuming `prmR N S Γ` / `parametersOfExtension N S Γ` (`Open0`'s 12 component lemmas, `open_and_linked_of_stronger_extension`, `rowFun_at_gridA`, `linked_bundles_l3_of_open`, `allRows_of_open0`, `ExportF`, `MultQ`, `ExBL`, `PositionMv`) is proved uniformly for arbitrary `Γ : GeoP` — with `Γ` occurring contravariantly in the universally quantified bundle/row conditions, so that `Γ = True` yields the **strongest** (hardest-to-prove) universal statements while only dropping an unused `geoOf` obligation on the existential side (leaving `OAt.lam` and all other structure fields intact and genuinely used). The parameter `Γ` is completely existentially eliminated at `UpperTheory.Top.classSel` before constructing `Hyps S0.NL DRS` / `HypsAlt S0.NL DefiniteSideCondition` (neither of which mentions `Γ`, contains any `True` field, or even transitively imports `OverIx` or `NotGeoClFalse`), and the two `trivial` arguments in `plugWin` / `zero_free_all_of_green_v_win` merely discharge unused `True` premise slots in `TopShape` / `TopShapeAlt`. Thus `Γ := geoCl anyGeometry` reveals a vestigial, unused geometry slot rather than a logical flaw — and as a matter of Lean's kernel soundness, a closed kernel-checked theorem of Mathlib's `RiemannHypothesis` with no hypotheses (assuming standard axioms and no `sorry`, which were outside this read-only source check) cannot be invalidated by a trivial or degenerate intermediate witness.
