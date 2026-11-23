# Fact-Check Report: Sections 5 and 6 of Nielsen's Critique of Alpöge's Lean 4 Riemann Hypothesis Formalization

- **Source repository audited**: `~/rh-audit/src/omega` (Lean sources under `src/`, ~175k files; declaration index at `~/rh-audit/index/decls.txt`).
- **Critique text audited**: J. L. Nielsen, *[quotation from the paper omitted]* (`~/rh-audit/nielsen/paper.txt`, Sections 5–6, lines 225–315).
- **Method**: Read-only static inspection of actual Lean 4 terms and types (Lean is not installed). Repo-wide occurrence counts come from exact fixed-string `git grep -n -F` / `git grep -n -w -F` searches across `src/`. All file paths below are relative to `~/rh-audit/src/omega/` unless stated otherwise.

---

## Item 1 (Sec. 5): `Holds R F`, `WeightCaseCondition`, and Construction Sites of `InGeo`

**Verdict: PARTLY TRUE**

### 1.1 Verification of `Holds R F`, `WeightCaseCondition`, and `InGeo`

1. **`WeightCaseCondition` takes `InGeo z.geo` and concludes `Holds z.R z.F` — TRUE.**
   In `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonzeroPlacesOverPrimesLifts.lean:102-105`:
   ```lean
   def WeightCaseCondition : Prop := StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
     (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt →
       GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) →
       Holds z.R z.F
   ```
   (Here `GlobalTheory.Mem.R3.Holds` is defined at `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/StableIffCarrierEq.lean:87-91`.)

2. **`exists_pre2_of_fine_of_resChar_mem` produces `Holds z'.R z'.F` at line 217 out of `WeightCaseCondition` applied to `InGeo z'.geo` — TRUE (with a small qualification on "first produced").**
   In `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConstructionStartingChoicesOfFineAdelicData.lean:195-217`:
   ```lean
   theorem exists_pre2_of_fine_of_resChar_mem : ... → WeightCaseCondition → StepW Start fun K B f T w => ...
   ...
     have hGeo' : GlobalTheory.RealGeo.InGeo z'.geo := ResStd.res_inGeo z hEx hle hc hGeo
     have hCore' : CoreP z' := hCore
     have hStd' : z'.Std := ResStd.res_std z hEx hle hc hStd
     have hH : Holds z'.R z'.F := hHW' Z hX _ z' hGT hGA hKap hEx' hGeo' hCore' hG2 hW.symm hsub
   ```
   Qualification: `exists_pre2_of_fine_of_resChar_mem` is the first site on the construction pipeline that *instantiates* `WeightCaseCondition` on a concrete datum `z'` to obtain a term `hH : Holds z'.R z'.F` (packaged into `Pre2` at line 233). `WeightCaseCondition` itself is proved by `atDat_holds` / `holdsW` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HoldsFromPrintedInputs.lean:58-96`) and `atDat_holds_alt` / `w_of_multEq_and_test_at_weights` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/WeightSetResidueCharacteristic.lean:18-68`), which take `g4 : InGeo z.geo` and feed it through `lUnif_atDat`, `atDat_lIntegral`, and `rational_data_sized_family` to prove `Holds z.R z.F`.

3. **`InGeo` is a 7-field structure on `GeoHalf` — TRUE.**
   In `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/JEvExists.lean:119-127`:
   ```lean
   structure InGeo {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {ph : Fin D.R.m → ℂ}
       (B : GeoHalf T R ph) : Prop where
     jEvExists : JEvExists T R B.κ B.v₀
     jEvBar : JEvBar T R B.κ
     evInj : EvInj T R B.v₀
     jUnif : JUnif T R B.κ B.v₀
     geoAct : GeoAct T R B.κ B.v₀
     latFull : LatFull T B.κ
     dimMatch : DimMatch T R B.κ
   ```

### 1.2 All Construction Sites of `InGeo` (Discrepancy with the Paper)

The paper states (`paper.txt:243-245`): *[quotation from the paper omitted]* This is **incomplete and partly inaccurate** in two ways:

1. **There is a third, primary from-scratch construction site missed by the paper**, which is in fact the one that constructs `InGeo z.geo` for `Fine z` feeding `exists_pre2_of_fine_of_resChar_mem`.
2. **In the two sites named by the paper, only 4 of the 7 fields are filled by lemmas at those sites**, while the other 3 (`jEvBar`, `evInj`, `geoAct`) are direct projections from a hypothesis `hR` (`p.PointConditions'` or `p.Rows`) — though those 3 fields of `hR` are themselves proved by substantive lemmas upstream.

Below is the complete classification of every site in the tree that constructs a value of type `InGeo ...`. **None** of them uses `trivial`, `rfl`, or `fun x => x.elim`.

#### Site A (Missed by Paper — Primary From-Scratch Construction): `GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral`

In `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeometricHalfCoreFormsUniformisationIntegral.lean:60-76`:
```lean
theorem inGeo_and_lUnif_and_lIntegral : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) ...
    (B : GeoHalf T R ph), PreChar R → R.grp_chiW → T.pb = R.C.P.pb → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV →
    InGeo B ∧ R.LUnif ∧ R.LIntegral := by
  intro hP D G _ _ Pl0 T0 A T _ R ph B hC hχ hp hn
  have ht : TieIn T R B.κ B.v₀ := ⟨B.fw.laws, B.fw.alg_eq, B.fw.kap, B.fw.hv₀, B.fw.chiR, B.fw.x0⟩
  have hJ := GlobalTheory.CuspValues.jEvExists_and_jEvBar D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hI := GlobalTheory.MemberEvalInj.evInj_of_tieIn D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hU := GlobalTheory.ReadingSpan.jUnif hP D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp hJ.1 hJ.2 hI hn
  have hL := GlobalTheory.MemberLatFull.latFull_of_tieIn D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hG := GlobalTheory.geoAct_of_ties_of_equivAll T R B.κ B.v₀ B.O hC.lev hC.models.inf hC.models.HW ht hp B.pins B.equivAll
  ...
  refine ⟨⟨hJ.1, hJ.2, hI, hU, hG, hL, B.fw.dimMatch⟩, ...⟩
```

- **Field classification**: All 7 fields are supplied by lemmas with substantive proofs (zero `trivial`/`rfl`/`elim`):
  - `jEvExists`, `jEvBar`: `GlobalTheory.CuspValues.jEvExists_and_jEvBar` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/JEvExistsAndJEvBar.lean:85`).
  - `evInj`: `GlobalTheory.MemberEvalInj.evInj_of_tieIn` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EvInjOfTieIn.lean:15`).
  - `jUnif`: `GlobalTheory.ReadingSpan.jUnif` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinrankLeOfAntilinear.lean:96`, using `CuspRapidDecay`).
  - `geoAct`: `GlobalTheory.geoAct_of_ties_of_equivAll` (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeoActOfTiesOfEquivAll.lean:17`).
  - `latFull`: `GlobalTheory.MemberLatFull.latFull_of_tieIn` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralZpowOfPowEqOne.lean:376`).
  - `dimMatch`: `FWTie.dimMatch` (`src/Formalism/LocalToGlobal/IndefiniteReal/FWExist.lean:790-793`), proved as `fun i => (finrank_of_isKsForm (R.FW i) (t.ks i)).trans (t.e i).finrank_eq.symm` from the `FWTie` linear equivalence `t.e i` and `t.ks i`.
- **Where its further hypotheses come from**: Its hypotheses are `GlobalTheory.Published.CuspRapidDecay`, `B : GeoHalf T R ph`, `PreChar R`, `R.grp_chiW`, `T.pb = R.C.P.pb`, and `8 * D.R.f * D.R.r + 4 ≤ D.R.nV`. It is called at four places:
  1. `datExS_evLg` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFineAdelicDatumOfHyp.lean:144-145`), which proves `DatExS` (used directly on the live route to feed `exists_pre2_of_fine_of_resChar_mem`). Here `h3 : CuspRapidDecay` is a published input; `hGeo.some : GeoHalf ...`, `hPre`, and `hch'.base.grp.chiW` come from `charW_seed_std` (lines 125–140) fed by `geometricExistence_core_forms_analytic_phaseOne` (line 123); `C.pb = R.C.P.pb` comes from `character_value_mem_smallField_of_infPart_eq_one` (lines 106, 115, 145); and `hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV` comes from `eventually_definiteSpaces_standard_and_large` (lines 88, 96).
  2. `geometricHalf_coreForms_of_weakCharacterisation` / `inGeo_stepW` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeometricHalfCoreFormsOfWeakCharacterisation.lean:19-44`), called by `geometricHalf_to_analyticData_enlargedBase` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeometricHalfToAnalyticDataEnlargedBase.lean:57,90`), where the `GeoHalf` datum is built from `exists_fw`, `exists_omOver`, and `ties_enl` (lines 65–90).
  3. `exists_geoHalf` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsGeometricHalfPhaseOneOverLawfulCore.lean:29-40`), called via `GeometricExistenceCoreFormsAnalyticPhaseOne.lean:27` (which supplies `hGeoEx` in (1) above).
  4. `exists_framed` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ThetaSeriesRationalityAndCoefficientBound.lean:55-57`), where `g : GeoHalf` comes from `exists_framed_half` + `geoHalf_upd` applied to an existing `RealSide` carrying `X.inGeo`.

#### Sites B and C (Named by Paper): `InGeoGeoHalf.lean` and `RationalHypothesisInHalfGeometry.lean`

In `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/InGeoGeoHalf.lean:15-29` (`GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0`, taking `hR : p.PointConditions'`) and identically in `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RationalHypothesisInHalfGeometry.lean:16-30` (`GlobalTheory.UnframePt.inGeo_geoHalf`, taking `hR : p.Rows`):
```lean
theorem GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 : GlobalTheory.Published.CuspRapidDecay → ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x)
    (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p → ∀ (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m),
    RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j → InGeo (geoHalf p) := by
  intro hDec eps Fm x hx i p hR _hM t j h0
  have hJ : JEvExists p.T p.R.toRealDat p.κ p.v₀ :=
    GlobalTheory.ConjReading.jEvExists p.T p.R.toRealDat p.κ p.v₀ p.O h0.core.lev h0.core.models p.fw p.pins
  exact
    { jEvExists := hJ
      jEvBar := hR.jEvBar
      evInj := hR.evInj
      jUnif := GlobalTheory.ReadingSpan.jUnif hDec _ _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ h0.core.lev h0.core.models h0.tieIn
        hR.ties.pb hJ hR.jEvBar hR.evInj h0.size
      geoAct := hR.geoAct
      latFull := GlobalTheory.IntCuspLat.latFull_of_tie p.fw
      dimMatch := p.fw.dimMatch }
```

- **Field classification**:
  - **4 fields filled by substantive lemmas at this site**: `jEvExists` (`GlobalTheory.ConjReading.jEvExists`, `Proofs/TwistedOperators/JEvExistsAndJEvBar.lean:45`), `jUnif` (`GlobalTheory.ReadingSpan.jUnif`, `Proofs/IwasawaDecomposition/FinrankLeOfAntilinear.lean:96`), `latFull` (`GlobalTheory.IntCuspLat.latFull_of_tie`, `Proofs/DivisorProofs/ExistsSmulNonnegOfSpan.lean:285`), and `dimMatch` (`FWTie.dimMatch`, `Formalism/LocalToGlobal/IndefiniteReal/FWExist.lean:790`).
  - **3 fields filled by direct projections from `hR`**: `jEvBar := hR.jEvBar`, `evInj := hR.evInj`, `geoAct := hR.geoAct`.
- **Where those further hypotheses come from**:
  - For `InGeoGeoHalf.lean` (`p.PointConditions'`, defined at `ThirdPlaceSeries/Realised.lean:63-80`): `p.PointConditions'` is built by `pRows_of_parts_alt` (`ThirdPlaceSeries/PRowsOfParts.lean:15-36`, lines 21–23: `jEvBar := hF.2.1`, `geoAct := hF.2.2.1`, `evInj := hF.2.2.2`) from `hF : FiringPointSummands`. That `hF` is produced by `atAll_fourRows'` (`ThirdPlaceSeries/DeliveryFourRows.lean:22-23`, called by `ThirdPlaceSeries/EvWPRowsOfRows.lean:17`) → `fire_alt` (`ThirdPlaceSeries/Fire.lean:14-20`), which proves those three fields by substantive lemmas:
    ```lean
    GlobalTheory.ConjReading.jEvBar B.T _ B.κ B.v₀ B.O c.lev c.models B.fw B.pins,
    GlobalTheory.GeometricAction.geoAct B.T _ B.κ B.v₀ B.O c.lev c.models B.fw B.pins B.equivAll,
    GlobalTheory.EvalAtUnitVectorFinal.evInj_of_isModels_of_tie B.T _ B.κ B.v₀ c.models B.fw
    ```
  - `h0 : RatHyp0 ...` is supplied by `ratHyp0_at_point_alt` (`ThirdPlaceSeries/RatHyp0AtPoint.lean`, called in `ThirdPlaceSeries/PointCases.lean:85` and `ThirdPlaceSeries/RowAtOf.lean:23`) or `ratHyp0_at_point` (`Proofs/DivisorProofs/BadPrimeMemExceptionalSet.lean:19`).
  - `hDec : CuspRapidDecay` comes from the published-hypotheses bundle (`EveryCharacterOfLiteratureOfVWin.lean:773`).

#### Transport / Repackaging Sites (Copying an Existing `InGeo`)

All remaining occurrences of `InGeo` construction in the tree merely transport an already-given `InGeo` hypothesis across scalar updates, restrictions, or base changes (copying the 7 fields):
- `Definitions/AutomorphicMembership/InGeoIff.lean:56-64` (`inGeo` / `inGeo_iff`)
- `Definitions/AutomorphicMembership/InGeoGeoScalIff.lean:30-33`
- `Definitions/AutomorphicMembership/OmPinsTr.lean:158-167` (`inGeo_tr`)
- `Proofs/IwasawaDecomposition/GeoHalfUpd.lean:58-63` (`geoHalf_upd`)
- `Proofs/IwasawaDecomposition/ColumnParamsInstanceData.lean:94-97` (`inGeo_new`, `⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩`)
- `Proofs/IwasawaDecomposition/ConstructionStartingChoicesOfFineAdelicData.lean:73-75` (`res_inGeo`)
- `Definitions/AutomorphicMembership/ComplexSidePlacesIffMemNonzeroIndexPlaces.lean:66,71,137,205,244`
- `Definitions/AutomorphicMembership/IntertwinersExistScalarUpdateInvariant.lean:188` (`restrictEx_inGeo`)
- `Definitions/AutomorphicMembership/NonzeroIndexPlacesTransferAlongSameFiniteGroup.lean:144` (`inGeo_transfer`)
- `Proofs/IwasawaDecomposition/ExistsMovedRowLiftDataToFittingStages.lean:88` (`cp_inGeo`)
- `Proofs/IwasawaDecomposition/ExistsGeoExtN.lean:19-36` (`geo_copy`).

---

## Item 2 (Sec. 5): `GeoTiedP`, `divXFl` / `tiedX_fl`, and Dead Extraction Lemmas

**Verdict: TRUE**

1. **Definition of `GeoTiedP` (`src/Formalism/LocalToGlobal/LatticeGeometry/GeoTiedP.lean:124-128`)**:
   ```lean
   def GeoTiedP (X : DivX D) (inK : X.Lev → ℕ → Prop) : Prop :=
     ∃ (F : ShimFam D X.geo X.Lev) (ePl : ∀ (p : ℕ) [Fact p.Prime], X.PlP p ≃ PlL D p)
       (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (F.U (datW D F.κg j)).Comp),
       TiedX (jC := F.jC) (ng := F.ng) X F.levPr F.levPr_prime F.κg ePl F.U eC ∧ ComplexEmbeddingsCompatible F.jC ∧ CuspTieX X ∧
         IsoInv F ∧ LevInTie F inK
   ```

2. **Every from-scratch construction of `GeoTiedP` in the repository builds it on `divXFl` via `tiedX_fl`**:
   Repo-wide `git grep -n -w -F` for `GeoTiedP`, `GeoTiedPL`, `GeoOver`, `divXFl`, and `tiedX_fl` finds exactly two from-scratch construction sites of `GeoTiedP`:
   - `geoTiedP_satisfiable` (`src/Formalism/LocalToGlobal/LatticeGeometry/GeoTiedP.lean:179-185`):
     ```lean
     theorem geoTiedP_satisfiable ... :
         ∃ X : DivX D, GeoTiedP X (fun _ _ => True) :=
       ⟨divXFl D jc X0, famFlJ D jc KO eO kL kL_eO, fun p _ => Equiv.refl _, fun _ _ _ => Equiv.refl _,
         tiedX_fl D jc X0, hjc, fun _ _ _ _ _ => trivial, isoInv_famFlJ D jc KO eO kL kL_eO,
         levInTie_famFlJ D jc KO eO kL kL_eO⟩
     ```
   - `geoOver_stages` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:155-166`, consumed in `exists_divT` at lines 184–189 to construct `DivT.geo : GeoTiedP Y inK`):
     ```lean
     theorem geoOver_stages (X : Stages) (X₀ : DivX X.toD7) : GeoOver (fun _ => True) X₀ := by
       ...
       refine ⟨divXFl D jc X₀, fun _ _ => True, ⟨divXFl D jc X₀, (divXFl D jc X₀).iMj, (divXFl D jc X₀).iMj_mem, rfl⟩,
         ⟨famFlJ D jc X.B.Ks eO kL hk, fun p _ => Equiv.refl _, fun _ _ _ => Equiv.refl _, tiedX_fl D jc X₀, hjc,
           fun _ _ _ _ _ => trivial, isoInv_famFlJ D jc X.B.Ks eO kL hk, levInTie_famFlJ D jc X.B.Ks eO kL hk⟩, trivial⟩
     ```
   Here `divXFl` (`src/Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean:829-861`) sets `geo := geoDegenerate D.what₂.LL D.what₂.Tau` (line 831), `Lev := Unit` (line 832), `Comp := fun _ => PUnit` (line 854), `degHH := fun _ _ _ => 0` (line 856), and `iMj := fun j _ => (0 : (X0.MjH j).V →ₗ[D.what₂.LL] D.what₂.LL)` (line 860), and `tiedX_fl` (`Inhabited.lean:868-890`) certifies `TiedX` on `divXFl` by `rfl`/`HEq.rfl` and `shimUFl`.

   The only other declarations returning `GeoTiedP` are non-constructive transports/projections from an existing witness: `GeoTiedPL.geoTiedP` (`GeoTiedP.lean:146-148`; `GeoTiedPL` is never constructed anywhere in the tree) and `geoTiedP_divTr` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DivisionLocalDataPreservedDivisionLatticeChange.lean:122-138`, transporting an existing `GeoTiedP X inK` across `divTr`).

3. **`GeoTiedP.geoTied` and `GeoTiedP.formsTieX` are never used anywhere**:
   Repo-wide `git grep -n -w -F` for `geoTied` and `formsTieX` confirms each occurs **exactly once** in the entire repository, at its own declaration:
   - `src/Formalism/LocalToGlobal/LatticeGeometry/GeoTiedP.lean:136`:
     ```lean
     theorem GeoTiedP.geoTied {X : DivX D} {inK : X.Lev → ℕ → Prop} (h : GeoTiedP X inK) : GeoTied X := by
     ```
   - `src/Formalism/LocalToGlobal/LatticeGeometry/GeoTiedP.lean:140`:
     ```lean
     theorem GeoTiedP.formsTieX {X : DivX D} {inK : X.Lev → ℕ → Prop} (h : GeoTiedP X inK) :
     ```

---

## Item 3 (Sec. 6): `tiedDataS_assemble_alt` and `.div.geo` Occurrences

**Verdict: TRUE**

1. **`tiedDataS_assemble_alt` receives `geo`, writes `geo := geo`, and asserts `HEq S.geo geo` (proved by `HEq.rfl`)**:
   In `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TiedDataSAssemble.lean:20-53`:
   ```lean
   theorem tiedDataS_assemble_alt ...
       (what₂ : Formalism.L2.Rows.RowsCompatible D host cf tp) (inK : Y.Lev → ℕ → Prop) (geo : Formalism.L2.Geo.GeoTiedP Y inK) ... :
       ∃ S : _root_.Formalism.L2.TiedDataSAlt ex, ...
         S.inK = inK ∧ HEq S.geo geo ∧ P _ _ _ (he ▸ S.tw) := by
     cases h
     subst he
     first
     | exact ⟨{ ... inK := inK, geo := geo, tw := tw, ... },
           rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩
     | exact ⟨{ ... inK := inK, geo := geo, tw := tw, ... },
           rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩
   ```

2. **Exact repo-wide count of `.div.geo` is 4**:
   Running `git grep -n -F '.div.geo' -- src/` returns **exactly four lines** in the entire tree, matching the paper's exact description ([quotation from the paper omitted]):
   1. `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ThetaChr.lean:59`:
      ```lean
        geo : HEq S.geo q.x.div.geo
      ```
   2. `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsTiedDataReciprocity.lean:85`:
      ```lean
            ⟨O, q.O.ex.kap_def, hze⟩ q.x.div.inK q.x.div.geo (q.w.tw q.Z) he tw emt g hherm hforms
      ```
      (argument to `tiedDataS_assemble`, line 83)
   3. `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/CoreAltAltBis.lean:48`:
      ```lean
        geo : HEq S.geo q.x.div.geo
      ```
   4. `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TiedDataSAssemble.lean:76`:
      ```lean
            ⟨O, q.O.ex.kap_def, hze⟩ q.x.div.inK q.x.div.geo (q.w.tw q.Z) he tw emt g hherm hforms
      ```
      (argument to `tiedDataS_assemble_alt`, line 74).

---

## Item 4 (Sec. 6): `GeoCl` Line Count and Absence of Elimination

**Verdict: PARTLY TRUE**

- **Line count discrepancy (6 lines, 7 token occurrences)**: Running `git grep -n -w -F 'GeoCl' -- src/` returns **6 lines** (not 7), containing **7 occurrences** of the token `GeoCl` because `NotGeoClFalse.lean:24` contains `GeoCl` twice:
  1. `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotGeoClFalse.lean:21`:
     ```lean
     inductive GeoCl (Γ : GeoP) : ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop
     ```
  2. `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotGeoClFalse.lean:22`:
     ```lean
       | base {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} : Γ D J X → GeoCl Γ D J X
     ```
  3. `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotGeoClFalse.lean:24`:
     ```lean
           {J : Formalism.L2.Pj.Core D} {X : DivX D} : GeoCl Γ D J X → GeoCl Γ (setDiv D N h) (coreS N h J) (divTr N h X)
     ```
  4. `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotGeoClFalse.lean:26`:
     ```lean
     def geoCl (Γ : GeoP) : GeoP := GeoCl Γ
     ```
  5. `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotGeoClFalse.lean:28`:
     ```lean
     theorem geoCl_of {Γ : GeoP} {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} (h : Γ D J X) : geoCl Γ D J X := GeoCl.base h
     ```
  6. `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DivisionGeometryScalarsTransferSetDivision.lean:106`:
     ```lean
       · exact (by with_unfolding_all exact ((GeoCl.step (Γ := Γ) (D := (w.st Z).toD7) N h hp.geo) :))
     ```
  (Non-word substring matches for `GeoCl` elsewhere are only 47 `import ...NotGeoClFalse` lines and `GeoClass` in `Formalism/SharpRestriction/Divisibility/HeightShare.lean:376,379`.)

- **Substantive claim — TRUE**: Every occurrence of `GeoCl` is its inductive definition (`NotGeoClFalse.lean:21-24`), its `geoCl` alias (`:26`), or a constructor call (`GeoCl.base` at `:28`, `GeoCl.step` at `DivisionGeometryScalarsTransferSetDivision.lean:106`). Checking all 118 repo-wide occurrences of `geoCl` / `geoCl_of` and all occurrences of `OAt` (`OverIx.lean:44-49`, whose field `geo : Γ ...` carries `geoCl Γ`) confirms that `geoCl` is only passed as an opaque `GeoP` parameter (typically `geoCl anyGeometry`) or introduced via `geoCl_of` (`PublishedInputsImplyConclusion.lean:49`) and `GeoCl.step` (`DivisionGeometryScalarsTransferSetDivision.lean:106`). **No proof does case analysis or induction on `GeoCl` / `geoCl`.**

---

## Item 5 (Sec. 6): Six Dead Lemmas Occurring Exactly Once

**Verdict: TRUE**

Exact repo-wide `git grep -n -w -F` searches confirm that **each of the six declarations occurs exactly once** in the entire source tree — solely at its own declaration — and is never called anywhere:

1. **`geoOf_surf`** (1 occurrence) — `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotLamAreShift.lean:30`:
   ```lean
   theorem geoOf_surf {Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D} {D : D7} {J} {X : DivX D} (h : geoOf Q D J X) :
       Nonempty X.Surf ∧ Nonempty X.SurfFp := by
   ```
2. **`HasTrueSurf.secondChernDegree_vanishes_trueSurfaces`** (1 occurrence) — `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/SecondChernDegreeVanishesTrueSurfaces.lean:355` (the capitalized filename/import `SecondChernDegreeVanishesTrueSurfaces` differs in case):
   ```lean
   theorem HasTrueSurf.secondChernDegree_vanishes_trueSurfaces (h : HasTrueSurf X) (H : IndefiniteRowSideFullHecke.ZeroSectionBase.Ch2HodgeVanishes) :
       Formalism.MainNotions.WeightThresholdDefs.Conclusion4b X := IndefiniteRowSideFullHecke.ZeroSectionBase.recordVanishes_of H h.recordIsGeometric
   ```
3. **`HasTrueSurf.degCh2_eq_zero`** (1 occurrence) — `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/SecondChernDegreeVanishesTrueSurfaces.lean:364`:
   ```lean
   theorem HasTrueSurf.degCh2_eq_zero (h : HasTrueSurf X) (H : Formalism.MainNotions.WeightThresholdDefs.Conclusion4b X) (p : ℕ)
       [Fact p.Prime] {T : Scheme.{0}} [Algebra (ZMod p) Γ(T, ⊤)] (hT : IsProjSurface (ZMod p) T)
       (P : PPAS T) (hg : 1 ≤ P.g) (hP : IsProjOver (toSpZ P.A.left)) :
       degCh2 (ZMod p) (omega P.A) P.g = 0 := by
   ```
4. **`GeoTiedP.geoTied`** (1 occurrence) — `src/Formalism/LocalToGlobal/LatticeGeometry/GeoTiedP.lean:136`:
   ```lean
   theorem GeoTiedP.geoTied {X : DivX D} {inK : X.Lev → ℕ → Prop} (h : GeoTiedP X inK) : GeoTied X := by
   ```
5. **`GeoTiedP.formsTieX`** (1 occurrence) — `src/Formalism/LocalToGlobal/LatticeGeometry/GeoTiedP.lean:140`:
   ```lean
   theorem GeoTiedP.formsTieX {X : DivX D} {inK : X.Lev → ℕ → Prop} (h : GeoTiedP X inK) :
   ```
6. **`degree_value_of_determinant`** (1 occurrence) — `src/Formalism/SharpRestriction/Divisibility/PlaceRankTwoOne.lean:349`:
   ```lean
   theorem degree_value_of_determinant {D : D7} {large₂ : SizeData₂ D} {X : DivX D} {Lc : Loc D X} (h : PointsLemma D large₂ X Lc) : FrobeniusOrbitPlaceCount D large₂ X := by
   ```

---

## Item 6 (Sec. 6): `degHH_def` in `PlaceRankTwoOne.lean` — Structure, Vacuity, Construction, and Consumption

**Verdict: TRUE**

### 6.1 Structure and Field Definition

`degHH_def` is a field of **`structure Formalism.MainNotions.placeRankTwoOne.Loc (D : D7) (X : DivX D)`**, declared in `src/Formalism/SharpRestriction/Divisibility/PlaceRankTwoOne.lean:100,142-146`:
```lean
structure Loc (D : D7) (X : DivX D) where
  ...
  degHH_def : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c τ (s : X.geo.Fn (X.Yv j c)), IsNV X j c τ s →
    ∀ (r : (D.what₂.LL →+* ℂ) → ℝ) (ρ : D.what₂.places.Pl → ℝ), (∀ σ, 0 < r σ) →
      (∀ σ y, X.geo.pn (X.Yv j c) σ _ (metH j c τ σ) (X.geo.cx (X.Yv j c) σ s) y = r σ ^ 2) →
      (∀ w y, vF j c τ w s y = ρ w) → (Function.support ρ).Finite →
      X.degHH j c τ = degLine D r ρ
```

### 6.2 Vacuity for the Degenerate Model

For `divXFl` (`src/Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean:829-861`), `geo := geoDegenerate D.what₂.LL D.what₂.Tau` (line 831). In `geoDegenerate` (`Inhabited.lean:241-306`):
- Line 269: `pts := fun _ _ => PUnit`
- Line 283: `pn := fun _ _ _ _ _ _ => 0`

Since `D.what₂.embLL : D.what₂.LL →+* ℂ` is a concrete complex embedding of `D.what₂.LL` and `PUnit.unit : X.geo.pts (X.Yv j c) D.what₂.embLL`, the two hypotheses `(∀ σ, 0 < r σ)` and `(∀ σ y, X.geo.pn ... = r σ ^ 2)` yield `0 < r D.what₂.embLL` and `0 = r D.what₂.embLL ^ 2`, a contradiction. Thus `degHH_def` has unsatisfiable hypotheses and holds vacuously for `divXFl`. (Note also that for `divXExample` / `x0`, which use `geoExample` at `Formalism/LocalRingCardinality/SpanPowerMembership/DivXExample.lean:11-79` and `TupPinsOfMuIsW.lean:57-106`, `Comp := fun _ => Empty`, so `degHH_def` would likewise be vacuous over `c : X.Comp j`.)

### 6.3 Construction and Consumption of `placeRankTwoOne.Loc`

- **Construction sites**: **NONE.** Repo-wide search for `degHH_def` returns only its own declaration (`PlaceRankTwoOne.lean:142`), and inspecting all 12 files in the entire repository that import `Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne` confirms that `placeRankTwoOne.Loc` (and `placeRankTwoOne.LocF`) is **never constructed anywhere** (neither with named fields nor via an anonymous constructor `⟨...⟩`). Likewise, the field `degHH_def` is never projected or invoked anywhere.
- **Consumption sites (as an uninstantiated parameter or record field only)**:
  1. `src/Formalism/SharpRestriction/Divisibility/PlaceRankTwoOne.lean:150,387-388,454-480`: parameter `Lc : Loc D X` and family type `LocF Fm := ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i)` used in definitions (`HHPsi`, `PointsLemma`, `LocClass`, `ClosedPeriodValue`, `ClosedDeterminantValue`, `ClosedLiftNorm`, `ClosedAbsoluteShare`).
  2. `src/Formalism/SharpRestriction/Divisibility/FlipOneTwo.lean:49,81,199`: parameter `Lc : placeRankTwoOne.Loc D V` of `sizeConstantAtParamsWeight.Loc` and field `fl : placeRankTwoOne.LocF Fm` of `sizeConstantAtParamsWeight.LocF`.
  3. `src/Formalism/SharpRestriction/Divisibility/AdmissibleRank/LogDiscriminantLeSquareSizeFamily.lean:151,203,219`: parameter `Lc : placeRankTwoOne.Loc D V` / `Y : sizeConstantAtParamsWeight.LocF Fm` in helper theorems for `sizeConstantAtParamsWeight.adm5`.
  4. `src/Formalism/SharpRestriction/AdmissibleParameterJoins/DIVfromGLb.lean:158,181,225,294,304,314`: parameter `Lc : placeRankTwoOne.Loc D X` / `XF : placeRankTwoOne.LocF Fm` in `SupTie`, `supBound_of_size_packet`, `thirdAdmissible_of_sup`, `supBound_mono`, `thirdAdmissible_of_sizes`, and `thirdAdmissible_family`.
  5. `src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FlatSectionAndDegree.lean:105,135`: parameter `Lc : placeRankTwoOne.Loc D X` in `ModuliTie` (line 125) and existential `∃ XF : placeRankTwoOne.LocF Fm, ...` in `TiedClass` (line 135). Neither `ModuliTie` nor `TiedClass` is referenced anywhere outside this file.
  6. `src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsAbelianGaloisHost.lean:206`: unused section variable `(Lc : placeRankTwoOne.Loc D X)`.

---

## Item 7 (Sec. 6): The Degree Equation `X.degHH j c τ = dFl D large₂ j`

**Verdict: PARTLY TRUE**

The core claim — that the degree equation `X.degHH j c τ = dFl D large₂ j` is **never proved anywhere** — is **TRUE**. The narrower wording that it *[quotation from the paper omitted]* is slightly imprecise: it also appears as a hypothesis in two more definitions (`ShareFromInputs` and `SlopeFamilyStatement`), as the conclusion of four unproved `Prop` definitions (`TowerRallisLemma`, `FlatLineDegreeFamilyStatement`, `ClosedFlatLineDegree`, and `GaloisCuspidalOfInput.DegreeCompatibility`), and as the conclusion of one unused, tautological projection theorem (`degree_value_of_determinant`).

### Exhaustive Repo-Wide Inventory

Running `git grep -n -w -F 'dFl' -- src/` returns **exactly 6 lines** in the entire repository (lines 156, 343, 344, 347 of `PlaceRankTwoOne.lean`, line 30 of `GaloisCuspidalOfInput.lean`, and line 46 of `DescentConstants.lean`):
1. `src/Formalism/SharpRestriction/Divisibility/PlaceRankTwoOne.lean:156`:
   ```lean
   def dFl (j : ℕ) : ℝ :=
     (pS D j - qS D j) / 2 * large₂.logOm + qS D j * (2 * Real.log (rdK D) - Real.log D.host.rdE)
   ```
2. `src/Formalism/SharpRestriction/Divisibility/PlaceRankTwoOne.lean:343-344` (inside `def PointsLemma`, lines 336–344):
   ```lean
   def PointsLemma : Prop :=
     ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (c : X.Comp j) τ,
       (∃ s : X.geo.Fn (X.Yv j c), ... ∧ degLine D r ρ = dFl D large₂ j) ∧
       X.degHH j c τ = dFl D large₂ j
   ```
3. `src/Formalism/SharpRestriction/Divisibility/PlaceRankTwoOne.lean:347` (inside `def FrobeniusOrbitPlaceCount`, lines 346–347):
   ```lean
   def FrobeniusOrbitPlaceCount : Prop :=
     ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (c : X.Comp j) τ, X.degHH j c τ = dFl D large₂ j
   ```
4. `src/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/GaloisCuspidalOfInput.lean:30` (inside `def DegreeCompatibility`, lines 26–32, specialized to `j = D.R.m`):
   ```lean
   def DegreeCompatibility (large₂ : SizeData₂ D) (V : DivX D) (ell : D.what₂.Tau → HLat D.what₂.LL) : Prop :=
     DegreeHermitianFormula D ell → ... → placeRankTwoOne.Conclusion1 D large₂ →
     ∀ e : V.Comp D.R.m ≃ XDef D, (∀ c τ, V.degHH D.R.m c τ = degHHc D ell (e c) τ) →
       (∀ (c : V.Comp D.R.m) τ, V.degHH D.R.m c τ = placeRankTwoOne.dFl D large₂ D.R.m) ∧ ...
   ```
5. `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/DescentConstants.lean:46`:
   ```lean
   def cFlat (j : ℕ) : ℝ := |placeRankTwoOne.dFl D L j|
   ```
   (defines a numeric constant, not the degree equation).

Checking every repo-wide reference to `placeRankTwoOne.PointsLemma`, `placeRankTwoOne.FrobeniusOrbitPlaceCount`, `DegreeValueFamily`, `FrobeniusOrbitPlaceCountCondition`, and `DegreeCompatibility`:
- **As a hypothesis**:
  - `SlopeBoundFamilyStatement` (`PlaceRankTwoOne.lean:429-431`): `... → DegreeValueFamily Fm → FamilyEstimateFour Fm → ConclusionF5 Fm → ConclusionF6 Fm`
  - `sizeConstantAtParamsWeight.admitted` (`FlipOneTwo.lean:132,189-192`): `... ∧ FrobeniusOrbitPlaceCountCondition D L V ∧ ...` (where `FrobeniusOrbitPlaceCountCondition := placeRankTwoOne.FrobeniusOrbitPlaceCount D L V`)
  - `ShareFromInputs` (`PlaceRankTwoOne.lean:383-385`): `... → FrobeniusOrbitPlaceCount D large₂ X → ...`
  - `SlopeFamilyStatement` (`PlaceRankTwoOne.lean:448-450`): `... → DegreeValueFamily Fm → ...`
- **As the conclusion of unproved `Prop` definitions** (each occurs only at its own definition / inside `PlaceRankTwoOne.lean` or `GaloisCuspidalOfInput.lean`, and none is proved anywhere):
  - `TowerRallisLemma` (`PlaceRankTwoOne.lean:376`), `FlatLineDegreeFamilyStatement` (`PlaceRankTwoOne.lean:426`), `ClosedFlatLineDegree` (`PlaceRankTwoOne.lean:482-483`), and `DegreeCompatibility` (`GaloisCuspidalOfInput.lean:26-32`).
- **Sole theorem whose conclusion is the degree equation**:
  - `degree_value_of_determinant` (`PlaceRankTwoOne.lean:349-351`):
    ```lean
    theorem degree_value_of_determinant ... (h : PointsLemma D large₂ X Lc) : FrobeniusOrbitPlaceCount D large₂ X := by
      intro j hj hj' c τ
      exact (h j hj hj' c τ).2
    ```
    This merely projects the second conjunct of `PointsLemma` (which already contains `X.degHH j c τ = dFl D large₂ j` verbatim at line 344), and `degree_value_of_determinant` is never called anywhere.

Thus **no theorem in the repository ever proves `X.degHH j c τ = dFl D large₂ j`** from any non-circular premises (nor is `PointsLemma`, `DegreeValueFamily`, `ClosedFlatLineDegree`, or `DegreeCompatibility` ever proved).

---

## Item 8 (EXTRA): What Is Actually on the Route from `riemannHypothesis` (`src/Main.lean`)?

**Answer Summary**:
- **OFF THE ROUTE (NO)**: `SlopeBoundFamilyStatement`, the degree equation `X.degHH j c τ = dFl D large₂ j` (including `DegreeValueFamily`, `ClosedFlatLineDegree`, `DegreeCompatibility`), `placeRankTwoOne.PointsLemma`, and `FrobeniusOrbitPlaceCount` (both `placeRankTwoOne.FrobeniusOrbitPlaceCount` and its unrelated homonym `UnusedSlot33.FrobeniusOrbitPlaceCount`). None of these is taken as a hypothesis or used anywhere on the route from `riemannHypothesis`.
- **ON THE ROUTE (YES)**:
  1. **`InGeo`**: Taken as a hypothesis (e.g., in `WeightCaseCondition`, `LowerUnitaryCaseCondition`, `exists_framed_half`) and **discharged on the route by substantive proofs** — both via `inGeo_and_lUnif_and_lIntegral` (for `Fine z` and `DatExt`) and via `inGeo_geoHalf_of_ratHyp0` (for `ExportedStatement` / `SurjectiveOntoX`) — conditional on the repository's published-literature hypotheses (such as `CuspRapidDecay`), which are themselves supplied upstream by `EveryCharacterOfLiteratureOfVWin.lean` from `OpenLiteratureStatements`.
  2. **`GeoTiedP`**: Required as a record field (`DivT.geo`, `TiedDataSAlt.geo`) on the route and **discharged degenerately/vacuously on `divXFl` (`geoDegenerate`) via `tiedX_fl`** in `geoOver_stages` (`TupPinsOfMuIsW.lean:155-166`), then copied untouched through `tiedDataS_assemble_alt` (`geo := geo`, `HEq.rfl`) without `GeoTiedP.geoTied` or `GeoTiedP.formsTieX` ever being called.
  3. **Unrelated homonyms of `PointsLemma`**: While `placeRankTwoOne.PointsLemma` (from Sec. 6) is completely off the route, the repository defines ~30 unrelated `PointsLemma` predicates in other `Formalism.MainNotions.*` namespaces; at least one (`PlaceDegreeData.PointsLemma`) appears on the live route (discharged from `SiegelWeilUnitaryConvergent` in `CountConstantsOfSiegelWeil.lean:18-24`).

### 8.1 Methodology and Its Limits

- **How "on the route" was decided**:
  1. **Forward textual call-chain verification**: Starting from `riemannHypothesis` (`src/Main.lean:4`), we read every intermediate declaration along the route specified in the prompt and traced both of its main sub-branches (the producer of `HypsAlt`, `nonempty_hyps_definite_side_of_closed_bound`, and its consumer, `shape_closed_link_n_of_green`), verifying each function/theorem application directly in the Lean proof terms.
  2. **Exhaustive reverse textual reachability**: For each target claimed to be *off* the route, we ran repo-wide fixed-string `git grep` across all ~175k files in `src/` for every occurrence of the target identifier and every file importing its defining module, verifying that no chain of callers connects any declaration mentioning it to `riemannHypothesis`.
  *(Note: module-level transitive `import` reachability from `src/Main.lean` is uninformative because `src/Main.lean:2` imports `Supplements.Kernels.MainTheoremsAll`, which transitively imports 175,187 local modules — virtually the entire repository. Actual proof-term call tracing plus reverse caller analysis is therefore required.)*
- **Limits**: Because Lean is not installed, we cannot elaborate proof terms or query the Lean kernel's exact constant-dependency set (`ConstantInfo.value`). Purely textual tracing could in principle miss dependencies introduced implicitly by typeclass synthesis, tactic/macro expansion, or definitional unfolding of abbreviations. However, (a) every on-route step cited below is an explicit identifier application verified verbatim in the Lean source, and (b) every off-route target has **zero** callers anywhere outside its own defining module(s), ruling out implicit call paths.

### 8.2 The Top-Level Route Verified from `src/Main.lean`

1. `src/Main.lean:4`: `theorem riemannHypothesis : RiemannHypothesis := rhOfAll`
2. `src/Supplements/Kernels/MainTheorems.lean:7,9`: `allChi := UpperTheory.FinalTheorems.everyCharacter`, `rhOfAll := Formalism.VW.rh_of_every allChi`
3. `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7-11`:
   ```lean
   theorem UpperTheory.FinalTheorems.everyCharacter_of_row (h : ...) : UpperTheory.EveryCharacter :=
     UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩ (UpperTheory.One.vwin_of_row h)
   theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=
     UpperTheory.FinalTheorems.everyCharacter_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
   ```
4. `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810-813`:
   `every_character_of_literature_of_vWin` calls `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` with the published-results bundles (`published_results_eigen O`, `published_results_first O`), `theta_integrals_agree_and_local_matching_of_literature O`, `topCovolSlim2_use_alt_alt ...`, `local_langlands_gl_recT_exists_of_literature O`, and `hV`.
5. `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69-73`:
   ```lean
   theorem every_character_of_theta_integrals_local_matching ... : UpperTheory.EveryCharacter :=
     _root_.UpperTheory.Top.every_character_of_green_v_win (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) hV
       (_root_.UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound P F hA hM hX hL ...)
   ```
6. `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12-18`:
   ```lean
   theorem UpperTheory.Top.zero_free_all_of_green_v_win ... : Formalism.HC.ZeroFreeAll :=
     h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
       (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (_root_.UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h)
       fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)
   theorem UpperTheory.Top.every_character_of_green_v_win ... : UpperTheory.EveryCharacter :=
     UpperTheory.Top.imprimitive (_root_.UpperTheory.Top.zero_free_all_of_green_v_win hG hV h)
   ```
7. `src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:26-34`:
   `zeroFreeAll_of_topG` invokes `zeroFreeOn_of_tiedWin_cyc` with `level_gm_le_on_family_scales`, `formB`, and `h : TopG` (supplied by `shape_closed_link_n_of_green` in `ThirdPlaceSeries/TopShape.lean:33-55` via `forall_goal_of_shape_of_hyps` in `ThirdPlaceSeries/ShapeOf.lean:24-32`).

### 8.3 Target-by-Target Route Audit

#### (A) Off the Route: `SlopeBoundFamilyStatement`, the Degree Equation, `placeRankTwoOne.PointsLemma`, and `FrobeniusOrbitPlaceCount`

- **`SlopeBoundFamilyStatement`**: Mentioned *only* in `Formalism/SharpRestriction/Divisibility/PlaceRankTwoOne.lean:429` (its definition) and `PlaceRankTwoOne.lean:480` (inside `placeRankTwoOne.ClosedAbsoluteShare`, which has **0** external occurrences). **Off the route.**
- **The degree equation `X.degHH j c τ = dFl D large₂ j`**: As established in Item 7, every declaration containing it lives exclusively in `PlaceRankTwoOne.lean` (`PointsLemma`, `FrobeniusOrbitPlaceCount`, `degree_value_of_determinant`, `TowerRallisLemma`, `ShareFromInputs`, `ConclusionF3`, `DegreeValueFamily`, `FlatLineDegreeFamilyStatement`, `SlopeBoundFamilyStatement`, `SlopeFamilyStatement`, `ClosedSlopeBound`, `ClosedAbsoluteShare`, `ClosedFlatLineDegree`), `FlipOneTwo.lean` (`FrobeniusOrbitPlaceCountCondition`, `admitted`, `Stmt`, `KudlaFamilyStatement`, `ClosedAbsoluteShare`), and `GaloisCuspidalOfInput.lean` (`DegreeCompatibility`). The only file importing `FlipOneTwo.lean` is `LogDiscriminantLeSquareSizeFamily.lean`, which uses only `sizeConstantAtParamsWeight.{RR, PP, Loc, LocF, QNorm, TheoremI2Hypotheses, adm3, adm5, adm6, adm9}` and never mentions `admitted` or `FrobeniusOrbitPlaceCountCondition`. The only file importing `GaloisCuspidalOfInput.lean` is `Formalism/LocalToGlobal/GlobalTheory/GL4/MemDualCrdLat.lean`, which never mentions `DegreeCompatibility`. **Off the route.**
- **`FrobeniusOrbitPlaceCount`**:
  - `Formalism.MainNotions.placeRankTwoOne.FrobeniusOrbitPlaceCount` (`PlaceRankTwoOne.lean:346`): **Off the route** (dead code, as above).
  - Homonym `Formalism.MainNotions.UnusedSlot33.FrobeniusOrbitPlaceCount` (`Formalism/SharpRestriction/GlobalSchurBounds/ConclusionR7abs.lean:94`, conjunct of `ConclusionOnD` at line 292): `ConclusionR7abs.lean` is imported only by `Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/PairwiseIndependenceComplementHolds.lean:2`, which never mentions `FrobeniusOrbitPlaceCount` or `ConclusionOnD`. **Off the route.**
- **`PointsLemma`**:
  - `Formalism.MainNotions.placeRankTwoOne.PointsLemma` (`PlaceRankTwoOne.lean:336`): Mentioned only at `PlaceRankTwoOne.lean:336,349,376,417` — zero callers anywhere in the repository. **Off the route.**
  - *Homonym clarification*: The identifier `PointsLemma` is reused across ~30 unrelated `Formalism.MainNotions.*` namespaces. At least one unrelated homonym **is** on the live route: `Formalism.MainNotions.PlaceDegreeData.PointsLemma` (`Formalism/SharpRestriction/CuspSpanNormBounds/PlaceDegreeData.lean:364`) is used in `CountConstantsOfSiegelWeil.lean:18,24` (`CountE.count_class_of_count` from `BridgeCountE.lean:86`, taking `PlaceDegreeData.PointsLemma` proved by `count_typed_of_volumeStep` in `CountTypedOfVolumeStep.lean:14` from `SiegelWeilUnitaryConvergent`) to produce `HypsAlt.h30` (`CountAllPointsClass`, `ThirdPlaceSeries/Hyps.lean:55`, consumed in `ThirdPlaceSeries/LinkAltAltBis.lean:30,47`). None of these homonyms involves `degHH` or `dFl`.

#### (B) On the Route: `InGeo` (Discharged by Substantive Proofs)

`InGeo` appears on the live route under `nonempty_hyps_definite_side_of_closed_bound` (`SiegelEisensteinSecondTermHypotheses.lean:44-68`) along **two verified textual chains**:

1. **Chain 1 — `Fine z` / `WeightCaseCondition` / `LowerUnitaryCaseCondition` / `DatExt` (via `inGeo_and_lUnif_and_lIntegral`)**:
   - `SiegelEisensteinSecondTermHypotheses.lean:68` → `HypothesesNonemptyOfUnramifiedExponents.lean:43` (`large_unramified_exponent_bundles_exist_alt`) → `MemberBundlesLargeUnramifiedExponents.lean:54,61`:
     - Line 54 calls `compatibleSystem_weightOne_saturated` (`LocalTypeDictionary/CompatibleSystemWeightOneSaturated.lean:14-15`) → `exists_bare_form_of_saturation` (`LocalTypeDictionary/ExistsBareFormOfSaturation.lean:19-25`):
       - Line 21: `have holdsW : WeightCaseCondition := _root_.GlobalTheory.T.w_of_weight_residue_char hH.h1 hH.h3 hH.multW` (takes `InGeo z.geo` as a hypothesis to produce `Holds z.R z.F`).
       - Line 22: `have holdsL : LowerUnitaryCaseCondition := _root_.GlobalTheory.T.lu_of_multiplicity_equal hH.h1 hH.h3 hH.multL` (takes `InGeo z.geo` as a hypothesis to produce `HoldsL z.R z.F`).
       - Line 23: `have datS : DatExS := GlobalTheory.T.exists_fineAdelicDatum_of_hypotheses ...` → `datExS_of_harishChandra_casselmanWallach` / `datExS_evLg` (`Proofs/IwasawaDecomposition/ExistsFineAdelicDatumOfHyp.lean:81-151`), which **discharges `InGeo hGeo.some`** at lines 144–145 via **`GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral`** (`GeometricHalfCoreFormsUniformisationIntegral.lean:60-76`).
       - Line 25: `have hPr := GlobalTheory.T.constructionStartingChoices_of_fine_adelicData ... holdsW` = `exists_pre2_of_fine_of_resChar_mem` (`ConstructionStartingChoicesOfFineAdelicData.lean:195-240`), which transports `InGeo z.geo` to `hGeo' : InGeo z'.geo` (line 214) and feeds it into `holdsW` (line 217) to produce `Holds z'.R z'.F`.
     - Line 61 (`member_exists_baseLattice_alt`, `ThirdPlaceSeries/ExistsBaseLatticeOfPrime.lean:62-63,67`) and `CompatibleSystemWeightOneSaturated.lean:15` also call `fineAdelicDatum_extends_to_larger_field_of_hypotheses` / `adelicData_extend_largerFields_of_hypotheses` → `datExt0_of_hypotheses` (`AdelicDataExtendLargerFieldsOfHyp.lean:31`) → `exists_ext_build` (`ExistsExtendedColumnDataAllClausesButPlaces.lean:33`) → `datExt_rest` (`ExistsExtendedAdelicDataWithIntertwinersOverEnla.lean:69`) → `geometricHalf_to_analyticData_enlargedBase` (`GeometricHalfToAnalyticDataEnlargedBase.lean:57,90`) → `inGeo_stepW` → `geometricHalf_coreForms_of_weakCharacterisation` (`GeometricHalfCoreFormsOfWeakCharacterisation.lean:28`) → **`inGeo_and_lUnif_and_lIntegral`**.

2. **Chain 2 — `InGeoGeoHalf.lean` (`inGeo_geoHalf_of_ratHyp0`)**:
   - `SiegelEisensteinSecondTermHypotheses.lean:51` and `HypothesesNonemptyOfUnramifiedExponents.lean:45` call `ontoX_and_lamLow_of_unitaryGroupHypotheses'` (`ThirdPlaceSeries/SurjectiveAndLowWeightOfUnramifiedExponents.lean:16-19`) → `ontoX_of_hypotheses_alt_alt` (`ThirdPlaceSeries/OntoXOfPrints.lean:28,36`) → `exportSt_of_reciprocity_and_casselman_wallach` (`ThirdPlaceSeries/ExportStOfReading.lean:15`) → `exportSt_of_hypotheses_alt` (`ThirdPlaceSeries/ExportStOfPrints.lean:27-35`):
     - Line 32 calls `at_statement_of_low_weight_twAdm` → `rowAt_of_alt` (`ThirdPlaceSeries/RowAtOf.lean:18-23`) → `rat_unframe_alt` (`ThirdPlaceSeries/RatUnframe.lean:18,29`) → **`inGeo_geoHalf_of_ratHyp0` (`ThirdPlaceSeries/InGeoGeoHalf.lean:15-29`)**.
     - Line 34 calls `baseGe_of_cuspRapidDecay_artin_rayClassField_seriesRat` → `baseGe_of_alt` (`ThirdPlaceSeries/BaseGeOfSteps.lean:48-50`) → `ThirdPlaceSeries/KerRatAt.lean:34` → **`inGeo_geoHalf_of_ratHyp0` (`InGeoGeoHalf.lean:15-29`)**.
   - As shown in Item 1, `InGeo (geoHalf p)` here is discharged by substantive lemmas (`ConjReading.jEvExists`, `ReadingSpan.jUnif`, `IntCuspLat.latFull_of_tie`, `FWTie.dimMatch`) together with `p.PointConditions'` fields `jEvBar`, `evInj`, `geoAct` (themselves proved by substantive lemmas in `ThirdPlaceSeries/Fire.lean:14-20`, invoked along the live route via `LinkedBundlesL3OfOpen.lean:42` / `RowFunAtGridA.lean:46` → `EvWPRowsOfRows.lean:17` → `DeliveryFourRows.lean:23`).

- **How `InGeo` is discharged**: By **substantive proofs** (not vacuously), using published-literature hypotheses (such as `CuspRapidDecay`) that are supplied by `EveryCharacterOfLiteratureOfVWin.lean` from `OpenLiteratureStatements` (itself discharged in `MainConclusion.lean:8,11` from `galoisLocalGlobalStrong_recParameter` and `recTExists`).

#### (C) On the Route: `GeoTiedP` (Discharged Degenerately/Vacuously on `divXFl` via `tiedX_fl`, Never Unpacked)

`GeoTiedP` is required on the live route as a field of `DivT` (`Definitions/AutomorphicMembership/TiedColumnData.lean:133`: `geo : Formalism.L2.Geo.GeoTiedP Y inK`) and `TiedDataSAlt` (`ThirdPlaceSeries/LinkedFamiliesFixedValues.lean:35`: `geo : Geo.GeoTiedP Y inK`), which enters `RecTAlt` → `BundleCondition` → `HypsAlt.σ` (`ThirdPlaceSeries/Hyps.lean:24`).

- **Exact verified call chain where `GeoTiedP` is discharged**:
  - `SiegelEisensteinSecondTermHypotheses.lean:68` (`nonempty_hyps_definite_side_of_closed_bound`)
  - → `HypothesesNonemptyOfUnramifiedExponents.lean:43` (`large_unramified_exponent_bundles_exist_alt`)
  - → `MemberBundlesLargeUnramifiedExponents.lean:61` (`member_exists_baseLattice_alt`)
  - → `ThirdPlaceSeries/ExistsBaseLatticeOfPrime.lean:70,53` (`exists_baseLattice_of_prime_alt` → `exists_baseLattice_of_pair_alt`)
  - → `ThirdPlaceSeries/MemberEClosing.lean:21,24` (`memberE_closing_alt_alt`)
  - → `Proofs/IwasawaDecomposition/PublishedInputsImplyConclusion.lean:39-49` (`divEx_geoCl`, which also wraps `anyGeometry` via `geoCl_of` = `GeoCl.base`)
  - → `divEx_of_ox` → `exists_divT` (`Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:178-192`)
  - → **`geoOver_stages`** (`TupPinsOfMuIsW.lean:155-166`), which discharges `GeoTiedP` **exclusively via the degenerate model `divXFl`** (`Inhabited.lean:829-861`, with `geoDegenerate`, `Comp := PUnit`, `degHH := 0`, `iMj := 0`) and `tiedX_fl` (`Inhabited.lean:868-890`) with `inK := fun _ _ => True`.
- **Exact verified call chain where `GeoTiedP` is copied downstream**:
  - `ExistsBaseLatticeOfPrime.lean:55` (and `MemberBundlesLargeUnramifiedExponents.lean:62` → `ThirdPlaceSeries/ExistsWeilBlockNeAtMember.lean:31`)
  - → `geometric_parameter_uniform_alt` (`ThirdPlaceSeries/ExBLIsLinkedPrmRStatement.lean:18` → `ExBLIsLinkedPrmR.lean:25`)
  - → `exBL_isLinked_alt` (`ThirdPlaceSeries/ExistsLinkedOfEq.lean:48`)
  - → `WPt.exists_recPinE_alt` (`ThirdPlaceSeries/ExistsRecPinE.lean:25`)
  - → `WPt.exists_pinned_spectral_data_compatible` (`ThirdPlaceSeries/TiedDataSAssemble.lean:55,74-76`)
  - → **`tiedDataS_assemble_alt`** (`TiedDataSAssemble.lean:20-53`), which passes `q.x.div.geo` straight into `TiedDataSAlt.geo` via `geo := geo` and `HEq.rfl`.
- **How `GeoTiedP` is discharged**: **Degenerately / vacuously** via `divXFl` (`geoDegenerate`) and `tiedX_fl`, and because `GeoTiedP.geoTied` and `GeoTiedP.formsTieX` are never called anywhere, the route never extracts any geometric consequences from `GeoTiedP`.

---

## Summary Table

| Item | Paper Section / Claim Summary | Verdict | Key Citations & Notes |
| --- | --- | --- | --- |
| **1** | (Sec. 5) `Holds R F` produced at `ConstructionStartingChoicesOfFineAdelicData.lean:217` from `WeightCaseCondition` (`NonzeroPlacesOverPrimesLifts.lean:102`) out of 7-field `InGeo`; paper says constructed in 2 places (`InGeoGeoHalf.lean`, `RationalHypothesisInHalfGeometry.lean`), each field from a lemma | **PARTLY TRUE** | `Holds`/`WeightCaseCondition`/`InGeo` structure verified (`JEvExists.lean:119-127`, `ConstructionStartingChoicesOfFineAdelicData.lean:217`). **Discrepancies**: paper misses the primary from-scratch constructor `inGeo_and_lUnif_and_lIntegral` (`GeometricHalfCoreFormsUniformisationIntegral.lean:60-76`, used in `ExistsFineAdelicDatumOfHyp.lean:144-145`); and in the 2 paper-named sites, 3 fields (`jEvBar`, `evInj`, `geoAct`) are direct projections from `hR` (proved upstream in `Fire.lean:14-20`), while 4 are lemmas. Zero fields use `trivial`/`rfl`/`elim`. |
| **2** | (Sec. 5) `GeoTiedP` (`GeoTiedP.lean:124`) built on `divXFl` via `tiedX_fl`; `GeoTiedP.geoTied` and `GeoTiedP.formsTieX` never used | **TRUE** | Both from-scratch constructors (`GeoTiedP.lean:179-185`, `TupPinsOfMuIsW.lean:155-166`) use `divXFl` + `tiedX_fl`. `GeoTiedP.geoTied` (`:136`) and `GeoTiedP.formsTieX` (`:140`) occur once each (unused). |
| **3** | (Sec. 6) `tiedDataS_assemble_alt` stores `geo := geo`, asserts `HEq S.geo geo`; `.div.geo` occurs 4 times in tree | **TRUE** | `TiedDataSAssemble.lean:30,40,46,48,51,53` (`HEq.rfl`). Exact count of `.div.geo` = 4 (`ThetaChr.lean:59`, `ExistsTiedDataReciprocity.lean:85`, `CoreAltAltBis.lean:48`, `TiedDataSAssemble.lean:76`). |
| **4** | (Sec. 6) `GeoCl` appears on 7 lines, only definition/constructors; no case analysis or induction | **PARTLY TRUE** | Exact word-match count is **6 lines** (containing **7 occurrences**, since `NotGeoClFalse.lean:24` has `GeoCl` twice): `NotGeoClFalse.lean:21,22,24,26,28` and `DivisionGeometryScalarsTransferSetDivision.lean:106`. No proof eliminates `GeoCl` / `geoCl`. |
| **5** | (Sec. 6) Six named lemmas each occur exactly once (only at declaration) | **TRUE** | All 6 verified count = 1: `NotLamAreShift.lean:30`, `SecondChernDegreeVanishesTrueSurfaces.lean:355,364`, `GeoTiedP.lean:136,140`, `PlaceRankTwoOne.lean:349`. |
| **6** | (Sec. 6) `degHH_def` in `PlaceRankTwoOne.lean` has `0 < r σ` & `pn ... = r σ ^ 2`, vacuous for degenerate `pn = 0`; identify structure, construction, consumption | **TRUE** | Field of `placeRankTwoOne.Loc` (`PlaceRankTwoOne.lean:100,142-146`). Vacuous for `divXFl` (`geoDegenerate.pn = 0`, `Inhabited.lean:283,831`). `placeRankTwoOne.Loc` is **never constructed anywhere**; consumed only as an uninstantiated parameter/field in 5 files (`PlaceRankTwoOne`, `FlipOneTwo`, `LogDiscriminantLeSquareSizeFamily`, `DIVfromGLb`, `FlatSectionAndDegree`, plus unused variable in `IsAbelianGaloisHost:206`). `degHH_def` is never projected. |
| **7** | (Sec. 6) `X.degHH j c τ = dFl D large₂ j` occurs only as a hypothesis (`PlaceRankTwoOne.lean:429`, `FlipOneTwo.lean:191`) and is never proved | **PARTLY TRUE** | **Never genuinely proved anywhere**: **TRUE** (`degree_value_of_determinant` at `PlaceRankTwoOne.lean:349` only projects `.2` from `PointsLemma` and is unused). Narrower wording slightly imprecise: also a hypothesis in `ShareFromInputs` (`:385`) and `SlopeFamilyStatement` (`:450`), and the conclusion of unproved `def`s (`TowerRallisLemma`, `FlatLineDegreeFamilyStatement`, `ClosedFlatLineDegree`, `GaloisCuspidalOfInput.DegreeCompatibility:30`). |
| **8** | (EXTRA) Are `SlopeBoundFamilyStatement`, the degree equation, `PointsLemma`, `FrobeniusOrbitPlaceCount`, `InGeo`, or `GeoTiedP` on the live route from `riemannHypothesis`? | **SPLIT (NO for Sec. 6 `PlaceRankTwoOne` items; YES for `InGeo`, `GeoTiedP`, and unrelated homonymous `PointsLemma`)** | **OFF ROUTE**: `SlopeBoundFamilyStatement`, `X.degHH = dFl`, `placeRankTwoOne.PointsLemma`, `FrobeniusOrbitPlaceCount` (both `placeRankTwoOne` and `UnusedSlot33`). **ON ROUTE**: (1) `InGeo` — discharged by **substantive proofs** (`inGeo_and_lUnif_and_lIntegral` via `ExistsFineAdelicDatumOfHyp.lean:144` / `GeometricHalfToAnalyticDataEnlargedBase.lean:57,90`, and `inGeo_geoHalf_of_ratHyp0` via `OntoXOfPrints.lean:36` → `ExportStOfPrints.lean:32,34`); (2) `GeoTiedP` — discharged **degenerately** on `divXFl` + `tiedX_fl` (`TupPinsOfMuIsW.lean:155-192` via `MemberEClosing.lean:21,24`) and stored via `TiedDataSAssemble.lean:20-76` without unpacking; (3) unrelated homonymous `PlaceDegreeData.PointsLemma` (`CountConstantsOfSiegelWeil.lean:18-24`). |
