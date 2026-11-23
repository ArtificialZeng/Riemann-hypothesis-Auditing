# Independent Source Fact-Check: Nielsen's Paper, Sections 2, 3, and 4

**Target repository**: `~/rh-audit/src/omega` (Lean 4 sources under `src/`).  
**Reference paper**: J. L. Nielsen, *The Invalidity of Alpöge's Proof of the Riemann Hypothesis* (`~/rh-audit/nielsen/paper.txt`).  
**Method**: Read-only direct inspection of Lean 4 definitions, types, and proof terms. All paths are relative to `~/rh-audit/src/omega/`.

---

## 1. (Sec. 2) `divEx_of_ox`: discarded hypotheses, definitions of the three `Prop`s, and callers

**Verdict: TRUE**

### 1.1 `divEx_of_ox` ignores its three hypotheses and calls `divEx_prov`

In `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:211-213`:

```lean
211: theorem divEx_of_ox : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → ∀ 𝒮 : Slots,
212:     𝒮.Ox = OX anyGeometry → DivEx 𝒮 :=
213:   fun _ _ _ 𝒮 hOx => divEx_prov 𝒮 hOx
```

All three arguments (`RayField`, `PrincipalIdealSt`, `CMCurveGoodOutsidePrimeSt`) are bound to `_` and discarded; the body immediately calls `divEx_prov 𝒮 hOx`.

### 1.2 Definitions of the three `Prop`s

All three are formalized statements of classical/published theorems (passed as function-type hypotheses at `divEx_of_ox`, not axioms):

1. **`GlobalTheory.NT.RayField`** — `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LFunctionPositiveConductorFourEight.lean:84-91` (aliased as `GlobalTheory.Published.RayClassFieldSt` at `src/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/NonemptyAlgHomOfIsRayOfDvd.lean:17`, `def RayClassFieldSt : Prop := GlobalTheory.NT.RayField`):
   ```lean
   84: def RayField : Prop :=
   85:   ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ →
   86:     ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
   87:       (∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → UnramIn L 𝔭) ∧
   88:       Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ IsFrob L 𝔭 σ} = ⊤ ∧
   89:       ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
   90:         ((∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) ↔
   91:           ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I * Ideal.span {β} = Ideal.span {α})
   ```
   This is the existence of the ray class field of modulus `𝔮` for every number field `K`.

2. **`GlobalTheory.Published.PrincipalIdealSt`** — `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/IsPrincipalMapOfAlgHom.lean:13-15`:
   ```lean
   13: def PrincipalIdealSt : Prop :=
   14:   ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [Algebra K L],
   15:     IsRayField K L ⊤ → ∀ 𝔞 : Ideal (𝓞 K), (𝔞.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal
   ```
   This is the Principal Ideal Theorem for totally complex number fields (every ideal of `𝓞 K` becomes principal in the Hilbert class field `L`, where `IsRayField K L ⊤`).

3. **`GlobalTheory.Published.CMCurveGoodOutsidePrimeSt`** — `src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean:31-38`:
   ```lean
   31: def IsGoodCMCurve (p : ℕ) (F : IntermediateField ℚ ℂ) (A : WeierstrassCurve F) : Prop :=
   32:   ∃ (_ : NumberField F) (_ : A.IsElliptic) (L : PeriodPair), IsIntegersLattice p L ∧
   33:     F = ℚ⟮(latticeCurve L).j⟯ ∧ (A.j : ℂ) = (latticeCurve L).j ∧ HasGoodReductionOutside p A
   35: def CMCurveGoodOutsidePrimeSt : Prop :=
   36:   ∀ p : ℕ, p.Prime → p % 4 = 3 → 3 < p →
   37:     ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (A : WeierstrassCurve F),
   38:       IsGoodCMCurve p F A ∧ HasMinimalDiscriminant A (-(p : F) ^ 3)
   ```
   This asserts that for every prime `p ≡ 3 (mod 4)` with `p > 3`, there is a CM elliptic curve over `ℚ(j(𝓞_{ℚ(√(-p))}))` with good reduction outside `p` and minimal discriminant `-p^3`.

### 1.3 Callers of `divEx_of_ox` and origin of its three arguments

Repository-wide search (`git grep -n -w -F 'divEx_of_ox'`) finds **one direct caller**:

- **`GlobalTheory.Mem.Top.Closing.divEx_geoCl`** — `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PublishedInputsImplyConclusion.lean:39-49`:
  ```lean
  39: theorem divEx_geoCl (h1 : GlobalTheory.NT.RayField) (h2 : GlobalTheory.Published.PrincipalIdealSt) (h3 : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt)
  40:     (R : RPosition) (N : NCondition) (S : SPosition) : DivEx ⟨R, N, S, OX (geoCl anyGeometry)⟩ := by
  41:   have h := GlobalTheory.Mem.Top.DivRec.divEx_of_ox h1 h2 h3 ⟨R, N, S, OX anyGeometry⟩ rfl
  ...
  49:   exact ⟨⟨geoCl_of o.geo, o.lam⟩⟩
  ```

`git grep -n -w -F 'divEx_geoCl'` finds **two calling theorems** (each calling `divEx_geoCl p1 p2 p3 _ _ _` twice, and also passing `p1 p2 p3` to `GlobalTheory.T.exists_member_of_construction_steps_secondPass`, where they are genuinely used to build `KPxCond.baseCond_KPx hR hP hC h2b` in `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMemberOfConstructionStepsSecondPass.lean:45`):

1. **Live `everyCharacter` route**:
   - `memberE_closing_alt_alt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MemberEClosing.lean:17-26`, lines `19, 21, 24`: `... (divEx_geoCl p1 p2 p3 _ _ _)`)
   - Called solely by `exists_baseLattice_of_pair_alt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExistsBaseLatticeOfPrime.lean:53`: `exact _root_.GlobalTheory.Mem.Top.Closing.memberE_closing_alt_alt hA.a1 hA.a2 hA.a3 ...`), where `hA : HypAAlt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/HypA.lean:13-16`: `a1 : GlobalTheory.NT.RayField`, `a2 : GlobalTheory.Published.PrincipalIdealSt`, `a3 : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt`).
   - Through `exists_baseLattice_of_prime_alt` (`ExistsBaseLatticeOfPrime.lean:70`) → `member_exists_baseLattice_alt` (`line 81`) → `member_bundles_large_unramified_exponents_alt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MemberBundlesLargeUnramifiedExponents.lean:43-46, 61`), `hA` is produced by `GlobalTheory.T.compatibleSystem_member_hypotheses P.globalArtinReciprocity P.cMCurveGoodOutsidePrimeSt ...` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/CompatibleSystemHypothesesOfLocalInputs.lean:10-17, 24-25`):
     ```lean
     15:   ⟨ar.rayClassFieldSt, ar.principalIdealSt, cm, hm, cd, cw, ...⟩
     ```
   - Tracing `P` up via `large_unramified_exponent_bundles_exist_alt` (`MemberBundlesLargeUnramifiedExponents.lean:69-70`) → `hypotheses_nonempty_of_unramified_exponents_alt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/HypothesesNonemptyOfUnramifiedExponents.lean:43`) → `nonempty_hyps_definite_side_of_closed_bound` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:68`) → `every_character_of_theta_integrals_local_matching` (`line 73`) → `every_character_of_literature_of_vWin` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810-811`), `P := published_results_eigen O` (`lines 666-726`):
     - **`h1` (`RayField`)**: `ar.rayClassFieldSt` (`GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt`, proved in `src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemConnectedComponentOfOneOfPos.lean:381-437`) applied to `P.globalArtinReciprocity` (`EveryCharacterOfLiteratureOfVWin.lean:690, 243-244`: `GlobalTheory.globalArtinReciprocity_holds`), which is proved in `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlobalArtinReciprocityHolds.lean:5` := `CompanionTheory.FamInh.globalArtin` (`src/CompanionTheory/AutomorphicTheory/PlaceSeparation/IsOpenQuotientMapArt0.lean:233-234`: `theorem globalArtin : GlobalTheory.Published.GlobalArtinReciprocity := fun E Ω _ _ _ _ _ => ⟨(art0 E Ω)⁻¹, isGlobalArtin_inv⟩`).
     - **`h2` (`PrincipalIdealSt`)**: `ar.principalIdealSt` (`GlobalTheory.Published.GlobalArtinReciprocity.principalIdealSt`, proved via group transfer in `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrincipalIdealSt.lean:12-79`) applied to the same proved `P.globalArtinReciprocity`.
     - **`h3` (`CMCurveGoodOutsidePrimeSt`)**: `P.cMCurveGoodOutsidePrimeSt` (`EveryCharacterOfLiteratureOfVWin.lean:713, 277-278`: `GlobalTheory.Published.cmCurveGoodOutsidePrime`), proved in `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmCurveGoodOutsidePrime.lean:47-101`.
     - Notably, none of these three arguments depends on the open literature bundle `O : OpenLiteratureStatements` (`EveryCharacterOfLiteratureOfVWin.lean:215-218`); all three are discharged by closed proofs inside the repo before being forwarded to (and ignored by) `divEx_of_ox`.

2. **Parallel `everyE₂` route**:
   - `memberE_closing` (`PublishedInputsImplyConclusion.lean:74-83`, lines `78, 81`) ← `published_inputs_imply_conclusion` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PublishedInputsImplyConclusionStatement.lean:33-34`) ← `memberE_exBL_of_pair` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MemberBuiltLinkedGeometric.lean:57`) ← `memberE_exBL_prm1` (`line 75`) ← `member_built_linked_geometric` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MemberBuiltLinkedGeometricStatement.lean:9-10`) ← `member_bundles_large_ue` (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LinkedBundleConstructionExists.lean:34, 54`), where `hA : HypA` is built identically by `hypA_of_artinReciprocity` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ArchimedeanInputsImply.lean:22-29`, line `27`: `⟨ar.rayClassFieldSt, ar.principalIdealSt, cm, ...⟩`).

---

## 2. (Sec. 2) `divEx_prov` fills `OAt.geo` with `trivial` and `OAt.lam` with `lamAre_heq ...`

**Verdict: TRUE** *(minor line-number and wrapper precision noted below)*

In `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean:19, 44-49`:

```lean
19: def anyGeometry : GeoP := fun _ _ _ => True
...
44: structure OAt (Γ : GeoP) {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0)
45:     (X : DivX (w.D Z)) : Type 1 where
46:   geo : Γ (w.st Z).toD7 t.r.z.core.toCore X
47:   lam : LamAre t.r.Z X
49: def OX (Γ : GeoP) : OComponent₂ := fun _ _ _ _ _ _ _ O t => OAt Γ t O.X
```

In `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:204-209`:

```lean
204: theorem divEx_prov (𝒮 : Slots) (hOx : 𝒮.Ox = OX anyGeometry) : DivEx 𝒮 :=
205:   StepW.of_all fun _ _ _ _ w _ _ hpin Z l =>
206:     let ⟨Y, h1, h2, h3, h4⟩ := exists_divT w hpin.some Z l
207:     ⟨Y, h1, h2, h3, fun O t hX hp ht => by
208:       rw [hOx]
209:       exact ⟨⟨trivial, lamAre_heq hp ht (hX ▸ h4)⟩⟩⟩
```

- After `rw [hOx]`, the target is `Nonempty (OAt anyGeometry t O.X)`. The outer `⟨...⟩` is `Nonempty.intro`; the inner `⟨trivial, lamAre_heq hp ht (hX ▸ h4)⟩` fills `OAt.geo : True` with `trivial` and `OAt.lam : LamAre t.r.Z O.X` with `lamAre_heq hp ht (hX ▸ h4)`.
- **Minor details vs. paper prose** (`paper.txt:128-134`):
  - The declaration `theorem divEx_prov` begins on line **204**, while the quoted line `exact ⟨⟨trivial, lamAre_heq hp ht (hX ▸ h4)⟩⟩` is on line **209** (with a closing `⟩` for the outer tuple).
  - The paper writes *[quotation from the paper omitted]* — strictly, `divEx_prov` proves `anyGeometry` directly via `trivial`, and `GeoCl.base` (`geoCl_of o.geo`, where `geoCl_of := GeoCl.base` in `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotGeoClFalse.lean:28`) is applied one step later in `divEx_geoCl` (`PublishedInputsImplyConclusion.lean:49`).

---

## 3. (Sec. 3) Field-value table for `geoDegenerate`, `divXFl`, and `x0`

**Verdict: TRUE**

Every row in the paper's table (plus `inter` and `dim` in the text of Sec. 3) matches the Lean source (noting that function-typed fields are constant functions `fun ... => <value>`).

### 3.1 `geoDegenerate` (`src/Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean:241-306`)

```lean
241: @[reducible] def geoDegenerate (F : Type) [Field F] [NumberField F] [StarRing F] (Tau : Type) [Fintype Tau] : DV.Geo F where
```

| Claimed field(s) | Claimed value | Exact source (`Inhabited.lean`) | Match |
|---|---|---|---|
| `Var` | `ℕ` | `242: Var := ℕ` | Yes |
| `Fn` | base field `F` | `244: Fn := fun _ => F` | Yes |
| `H0` | `⊤` | `252: H0 := fun _ _ => ⊤` | Yes |
| `Eff, nef, big, bpf, nefA` | `True` | `249: Eff := fun _ _ => True`; `262: nef := fun _ _ => True`; `263: big := fun _ _ => True`; `264: bpf := fun _ _ _ => True`; `295: nefA := fun _ _ => True` | Yes (all 5) |
| `phiBir, phiNoContr, vanishOn, mSmooth, mPsh` | `True` | `265: phiBir := fun _ _ _ => True`; `266: phiNoContr := fun _ _ _ _ => True`; `267: vanishOn := fun _ _ _ _ => True`; `285: mSmooth := fun _ _ _ _ => True`; `286: mPsh := fun _ _ _ _ => True` | Yes (all 5) |
| `vol, arVol, arTop, hdim` | `0` | `271: vol := fun _ _ => 0`; `294: arVol := fun _ _ => 0`; `293: arTop := fun _ _ => 0`; `268: hdim := fun _ _ _ => 0` | Yes (all 4) |
| `pn, pnK` | `0` | `283: pn := fun _ _ _ _ _ _ => 0`; `284: pnK := fun _ _ _ _ _ _ => 0` | Yes (both) |
| `pts, Cl, Met` | `PUnit` | `269: pts := fun _ _ => PUnit`; `257: Cl := fun _ => PUnit`; `279: Met := fun _ _ _ => PUnit` | Yes (all 3) |
| `inter` | `flagDegZ` formula | `261: inter := fun N v => if h : 0 < Formalism.DegreeFormula.dimFl Tau N then flagDegZ Tau N (v ⟨0, h⟩) else flagDegZ Tau N 0` | Yes (`flagDegZ` defined at `214-221`) |
| `dim` | `dimFl` | `243: dim := fun N => Formalism.DegreeFormula.dimFl Tau N` | Yes (`dimFl` at `Formalism/DegreeFormula/FlagDegFormula.lean:9`) |

*(Note for completeness: `Dv := fun N => Tau → Fin N → ℤ` at line `247` and `Adl := fun N => Tau → Fin N → ℤ` at line `290` also carry weight-tuple types rather than `PUnit`, and `inter` uses only the 0-th argument `v ⟨0, h⟩`.)*

### 3.2 `divXFl` (`src/Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean:829-861`)

```lean
829: def divXFl : DivX D :=
830:   { X0 with
831:     geo := geoDegenerate D.what₂.LL D.what₂.Tau
```

| Claimed field(s) | Claimed value | Exact source (`Inhabited.lean`) | Match |
|---|---|---|---|
| `Lev` | `Unit` | `832: Lev := Unit` | Yes |
| `Mp, CurveM, Comp` | `PUnit` | `846: Mp := fun _ _ _ _ _ => PUnit`; `849: CurveM := fun _ _ _ _ _ _ => PUnit`; `854: Comp := fun _ => PUnit` | Yes (all 3) |
| `degM, degHH` | `0` | `850: degM := fun _ _ _ _ _ _ _ _ => 0`; `856: degHH := fun _ _ _ => 0` | Yes (both) |
| `iMj` | `0` (zero map) | `860: iMj := fun j _ => (0 : (X0.MjH j).V →ₗ[D.what₂.LL] D.what₂.LL)` | Yes |
| `iMj_mem` | `Submodule.mem_top` | `861: iMj_mem := fun _ _ _ => Submodule.mem_top` | Yes |

### 3.3 Seed `x0` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:57-121`)

```lean
57: def x0 (Z : ReadL R F X0 Y) (hP : Pins R F cG) (hH : Holds R F) : DivX D where
58:   geo := Formalism.BasicNotions.Examples₂.geoExample _
```

| Claimed field(s) | Claimed value | Exact source (`TupPinsOfMuIsW.lean`) | Match |
|---|---|---|---|
| `Lev, Comp, Surf, SurfFp, QPl` | `Empty` | `59: Lev := Empty`; `105: Comp := fun _ => Empty`; `117: Surf := Empty`; `120: SurfFp := Empty`; `95: QPl := fun _ => Empty` | Yes (all 5) |
| `surfCh2, surfFpCh2` | `0` | `118: surfCh2 := fun _ => 0`; `121: surfFpCh2 := fun _ => 0` | Yes (both) |

*(Note: `x0.geo` is `geoExample _` which has `Var := Empty` at `src/Formalism/LocalRingCardinality/SpanPowerMembership/DivXExample.lean:11-12`; `x0.surfDegOm := fun _ => 0` at line `119`. In `exists_divT` at `TupPinsOfMuIsW.lean:182-183`, `reQ` subsequently replaces `x0.QPl` with a non-empty subtype before `graft`, while `Surf`, `SurfFp`, `surfCh2`, `surfFpCh2` remain `Empty`/`0` — see Item 4.)*

---

## 4. (Sec. 3) `geoOver_stages` and `graft`

**Verdict: PARTLY TRUE**

### 4.1 `geoOver_stages`

In `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/GeoTiedPGraft.lean:45-46`:

```lean
45: def GeoOver (Q : DivX D → Prop) (X₀ : DivX D) : Prop :=
46:   ∃ (X : DivX D) (inK : X.Lev → ℕ → Prop), Keeps X X₀ ∧ GeoTiedP X inK ∧ Q X
```

In `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:155-166`:

```lean
155: theorem geoOver_stages (X : Stages) (X₀ : DivX X.toD7) : GeoOver (fun _ => True) X₀ := by
...
160:   let jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ) :=
161:     fun p _ la => Classical.choose (GlobalTheory.WittFracPlace.exists_jcPin D p la)
162:   have hjc : ComplexEmbeddingsCompatible jc := GlobalTheory.ShFam.PinPlace.pinned_tiedFor D jc
163:     (fun p _ la => Classical.choose_spec (GlobalTheory.WittFracPlace.exists_jcPin D p la))
164:   refine ⟨divXFl D jc X₀, fun _ _ => True, ⟨divXFl D jc X₀, (divXFl D jc X₀).iMj, (divXFl D jc X₀).iMj_mem, rfl⟩,
165:     ⟨famFlJ D jc X.B.Ks eO kL hk, fun p _ => Equiv.refl _, fun _ _ _ => Equiv.refl _, tiedX_fl D jc X₀, hjc,
166:       fun _ _ _ _ _ => trivial, isoInv_famFlJ D jc X.B.Ks eO kL hk, levInTie_famFlJ D jc X.B.Ks eO kL hk⟩, trivial⟩
```

- **Accurate**: `geoOver_stages` does indeed produce `divXFl D jc X₀` (built on `geoDegenerate`) as the geometric companion and proves `GeoOver (fun _ => True)` with `Q := fun _ => True` discharged by `trivial` (and `CuspTieX` discharged by `fun _ _ _ _ _ => trivial`, `inK := fun _ _ => True`; note `hjc : ComplexEmbeddingsCompatible jc` is non-trivially proved via `exists_jcPin`/`pinned_tiedFor`).
- **Imprecision**: `geoOver_stages` proves `GeoOver (fun _ => True) X₀` — i.e., `GeoOver (fun _ => True)` is a predicate on the input seed `X₀` (not on `divXFl`), and `divXFl D jc X₀` is the existential witness `X` inside `GeoOver`.

### 4.2 `graft`

In `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/GeoTiedPGraft.lean:12-22`:

```lean
12: def graft (Xg X₀ : DivX D) (iM : ∀ j (c : Xg.Comp j), (X₀.MjH j).V →ₗ[D.what₂.LL] Xg.geo.Fn (Xg.Yv j c))
13:     (hiM : ∀ j c x, iM j c x ∈ Xg.geo.H0 (Xg.Yv j c) (Xg.Lw j c (DV.kapW D j))) : DivX D :=
14:   { Xg with
15:     MjH := X₀.MjH, MjH_good := X₀.MjH_good, jM := X₀.jM, jM_basis := X₀.jM_basis, jM_lat := X₀.jM_lat
16:     MjLat_sub := X₀.MjLat_sub, jM_metric := X₀.jM_metric
17:     Qp := X₀.Qp, degreeZero_partial_set_empty := X₀.degreeZero_partial_set_empty, Qp_muAt := X₀.Qp_muAt, Qp_g := X₀.Qp_g
18:     QPl := X₀.QPl, finQ := X₀.finQ, qv := X₀.qv, qv_gt := X₀.qv_gt, qv_char := X₀.qv_char
19:     nu := X₀.nu, nu_ne := X₀.nu_ne, nu_abs := X₀.nu_abs, ZQ := X₀.ZQ, quotientLocalValueFirst := X₀.quotientLocalValueFirst, typeDim := X₀.typeDim
20:     iMj := iM, iMj_mem := hiM
21:     logLam := X₀.logLam, logLam_base := X₀.logLam_base
22:     kapR := X₀.kapR, kapR_pos := X₀.kapR_pos, kapR_conj := X₀.kapR_conj }
```

Comparing `graft` against all fields of `structure DivX` (`src/Formalism/LocalRingCardinality/DataDIV.lean:418-544`):

- **Accurate**: Every geometric field (`geo`, `Lev`, `levPr`, `shv`, `shv_N`, `shv_lev`, `PlP`, `plpFin`, `plpNe`, `wtP`, `divisorWeight_*`, `plP`, `jC`, `Mp`, `md`, `vdd`, `vdd_unram`, `phiFr_unram`, `vdd_nonneg`, `CurveM`, `degM`, `htMdl`, `htCurve`, `htCurve_deg`, `Comp`, `compFin`, `degHH`, `Yv`, `Ybd`, `Lw`, `Surf`, `surfCh2`, `surfDegOm`, `SurfFp`, `surfFpCh2`) is kept from `Xg` (and `iMj`, `iMj_mem` are supplied as arguments `iM`, `hiM`, which `geoOver_stages` instantiates to `(divXFl D jc X₀).iMj = 0` and `Submodule.mem_top`).
- **Three discrepancies with the paper's summary**:
  1. `graft` does **not** take *only* lattice (`MjH`, `jM`, ...) and numerical (`logLam`, `kapR`) fields from `X₀`: lines `17-19` also take all 15 ramified-prime / local-character-divisor fields (`Qp`, `degreeZero_partial_set_empty`, `Qp_muAt`, `Qp_g`, `QPl`, `finQ`, `qv`, `qv_gt`, `qv_char`, `nu`, `nu_ne`, `nu_abs`, `ZQ`, `quotientLocalValueFirst`, `typeDim`) from `X₀`.
  2. In `exists_divT` (`TupPinsOfMuIsW.lean:182-188`), `geoOver_stages` and `graft` are applied not directly to `X₁ := x0 ...`, but to `X₂ := GlobalTheory.Mem.HD.ReQ.reQ l.n.tp hp w.I.sel pin.above X₁`:
     ```lean
     182:   let X₁ := x0 l.what₂.r.Z l.what₂.r.z.pins l.what₂.r.intersectionNumber_baseChange
     183:   let X₂ := GlobalTheory.Mem.HD.ReQ.reQ l.n.tp hp w.I.sel pin.above X₁
     184:   obtain ⟨X, inK, ⟨Xg, iM, hiM, rfl⟩, hG, -⟩ := geoOver_stages (w.st Z) X₂
     ```
     `reQ` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RamifiedRationalPrimesOfTupleBaseTupleEqEmpty.lean:156-180`) overwrites those 15 `Qp`/`QPl`/`qv`/`nu`/`ZQ`/`quotientLocalValueFirst`/`typeDim` fields with arithmetic/local-integral data (`Qp := qpSet Tp`, `QPl := fun μ => {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}`, etc.) while leaving `MjH`, `jM`, `logLam`, `kapR`, `Surf`, `SurfFp`, `surfCh2`, `surfFpCh2`, `vdd` unchanged (`lines 251-297`).
  3. `divXFl D jc X₀` (`Inhabited.lean:829-861`) is itself `{ X0 with ... }` and does not override `Surf`, `surfCh2`, `surfDegOm`, `SurfFp`, `surfFpCh2`, or `vdd`, so `Xg` (= `divXFl D jc X₂`) inherits those fields from `x0` via `X₂` (which is why `Keeps (divXFl D jc X₀) X₀` holds by `rfl` at `TupPinsOfMuIsW.lean:164`).

---

## 5. (Sec. 4) `DivEx`, `exists_divT` discharges, and seed `x0` lattice definitions

**Verdict: PARTLY TRUE** *(all six quoted proof terms and definitions are verbatim TRUE; the summary of `DivEx`'s signature is slightly compressed)*

### 5.1 `DivEx` and `DivT`

In `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonzeroPlacesOverPrimes.lean:183-185`:

```lean
183: def DivEx (𝒮 : Slots) : Prop := StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (l : Lv4 𝒮 K w Z), ∃ Y : DivX (w.D Z),
184:   Nonempty (DivT l.n Y) ∧ MjAre l.what₂.r.Z Y ∧ (∀ σ, Y.kapR σ = kapSharp (w.D Z)) ∧
185:     ∀ (O : Obj2 (w.D Z)) (t : RowsT K w Z l.Wt O.p0), O.X = Y → O.p0 = l.p0 → HEq t l.what₂ → Nonempty (𝒮.Ox K B f T w Z l.Wt O t)
```

In `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/TiedColumnData.lean:127-133`:

```lean
127: structure DivT {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) (Y : DivX (w.D Z)) :
128:     Type 1 where
129:   Qp : TC.QpIs w.I Y.Qp
130:   chr : DivisorCharacterCompatibility (w.D Z) (TC.cf w.I w.l Z) nch n.tp Y
131:   loc : Formalism.L2.DIV.QLocTiedC chr w.I.sel
132:   inK : Y.Lev → ℕ → Prop
133:   geo : Formalism.L2.Geo.GeoTiedP Y inK
```

- **Precision note**: `DivEx` asks for `Y` with (1) `Nonempty (DivT l.n Y)` — which bundles `geo : GeoTiedP Y inK` **together with** non-geometric ramified-prime/local-character fields `Qp`, `chr`, `loc` — (2) `MjAre l.what₂.r.Z Y`, (3) `∀ σ, Y.kapR σ = kapSharp (w.D Z)`, and (4) `∀ O t, ... → Nonempty (𝒮.Ox ...)` (abstracted over the slot `𝒮.Ox`, which becomes `OAt Γ t O.X` — carrying `geo : Γ ...` and `lam : LamAre t.r.Z O.X` — when `𝒮.Ox = OX Γ`, `OverIx.lean:44-49`). It is `exists_divT` (below) that directly states `LamAre` as its fourth conjunct.

### 5.2 Discharges in `exists_divT`

In `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:178-192`:

```lean
178: theorem exists_divT {𝒮 : Slots} {K : Ctx} (w : ColW B f T) (pin : ColPin w) (Z : w.Lt) (l : Lv4 𝒮 K w Z) :
179:     ∃ Y : DivX (w.D Z), Nonempty (DivT l.n Y) ∧ MjAre l.what₂.r.Z Y ∧ (∀ σ, Y.kapR σ = kapSharp (w.D Z)) ∧
180:       LamAre l.what₂.r.Z Y := by
...
188:   refine ⟨GlobalTheory.GeoGraft.graft Xg X₂ iM hiM,
189:     ⟨{ Qp := qpIs_qpSet w pin Z l.n.tp l.n.xi hp, chr := chr, loc := ⟨h1, ?_⟩, inK := inK, geo := hG }⟩,
190:     GlobalTheory.Mem.R3.exists_mjHTie l.what₂.r.Z _ rfl HEq.rfl, fun _ => rfl,
191:     lamAre_of_eq l.what₂.r.Z l.what₂.r.intersectionNumber_baseChange _ rfl⟩
```

All three lattice-side discharges match the paper **verbatim**:
- `MjAre`: `GlobalTheory.Mem.R3.exists_mjHTie l.what₂.r.Z _ rfl HEq.rfl` (line `190`).
- `∀ σ, Y.kapR σ = kapSharp (w.D Z)`: `fun _ => rfl` (line `190`).
- `LamAre`: `lamAre_of_eq l.what₂.r.Z l.what₂.r.intersectionNumber_baseChange _ rfl` (line `191`).

### 5.3 Seed `x0` definitions and `mjH`

In `TupPinsOfMuIsW.lean:84, 112, 114` and `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MapSeqIndAll.lean:137`:

```lean
-- TupPinsOfMuIsW.lean:
84:   MjH := mjH Z
...
112:   logLam := logLamOf Z hH
113:   logLam_base := fun _ _ => if_pos rfl
114:   kapR := fun _ => kapSharp D

-- MapSeqIndAll.lean:
137: def mjH (_Z : ReadL R F X0 Y) (j : ℕ) : HLat D.what₂.LL := mjLat R F j
```

All four definitions match the paper **verbatim**. Because `reQ`, `divXFl`, and `graft` preserve `MjH`, `jM`, `logLam`, and `kapR` definitionally, the `rfl` / `HEq.rfl` arguments in `exists_divT` typecheck on `Y = graft Xg X₂ iM hiM`.

---

## 6. (EXTRA) Are `mjLat R F j`, `logLamOf`, and `kapSharp` degenerate or substantive? What is proved and what is assumed?

**Verdict: SUBSTANTIVE ROW-SIDE OBJECTS WITH REAL PROOFS — NOT DEGENERATE STUBS, BUT COPIED INTO `DivX` WITHOUT A GEOMETRIC LINK**

### 6.1 Definitions: substantive arithmetic ("row-side") objects, not trivial stubs

Unlike `geoDegenerate` (`PUnit`, `0`, `True`), none of `mjLat R F j`, `logLamOf`, or `kapSharp` is a trivial/degenerate stub. Each is defined from the row-side automorphic/Hecke-module data (with fallback defaults only outside the active index range or positivity domain):

1. **`mjLat R F j`** — `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MapSeqIndAll.lean:22-23, 65-67, 134-137`:
   ```lean
   22: def unitLat (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) : HLat K :=
   23:   HLat.ofCoord (Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))) fun _ => 1
   65: def latSeq : ℕ → HLat K
   66:   | 0 => unitLat K (Module.finrank ℂ (W 0))
   67:   | j + 1 => if h : j < m then HLat.ofCoord (M ⟨j, h⟩) (X ⟨j, h⟩) else unitLat K (Module.finrank ℂ (W (j + 1)))
   134: def mjLat (R : RealDat3 D A3 Ks) (F : Face3 D A3) : ℕ → HLat D.what₂.LL :=
   135:   latSeq (m := D.R.m) (d := fun i => (s0Of R F).dW i) (fun i => (s0Of R F).M i) (fun i => (s0Of R F).XW i) D.what₂.Mj
   137: def mjH (_Z : ReadL R F X0 Y) (j : ℕ) : HLat D.what₂.LL := mjLat R F j
   ```
   For `1 ≤ j ≤ D.R.m` (`j = i + 1`), `mjLat R F (i + 1) = HLat.ofCoord ((s0Of R F).M i) ((s0Of R F).XW i)` (`src/Formalism/LocalToGlobal/Divisibility/RowSideTie.lean:27-33`, `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/StableIffCarrierEq.lean:239`: `def s0Of ... := (R.toCx3 F).data F.cr false`). Its components come from `R.toCx3 F` (`src/Formalism/LocalToGlobal/IndefiniteReal/ZeroPartEigenvalueConvention.lean:120-142`) and `CxData.data` (`src/Formalism/LocalToGlobal/IndefiniteReal/PartsOrth.lean:165-186`):
   - **Dimension `dW i`**: `Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 false i)` (`ZeroPartEigenvalueConvention.lean:132`), where `WL` is the level-and-idempotent subspace `(R.FW i).Wgood F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)` (`src/Formalism/LocalToGlobal/IndefiniteReal/LinksDefs.lean:669-670`, `src/Formalism/LocalToGlobal/IndefiniteReal/GramCEqTranspose.lean:76-91`).
   - **Integral lattice `(s0Of R F).M i`**: `(R.FW i).Mcoord F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) (R.toRealDat.bL F.lv2 false i)` (`ZeroPartEigenvalueConvention.lean:136`), the coordinate preimage of `Mj := (Submodule.span (𝓞 LL) MK) ⊓ typeP ⊓ good` (`GramCEqTranspose.lean:54-55, 93-97, 133-135`), where `MK` consists of `Ks`-rational forms whose non-archimedean local norms are `≤ 1`.
   - **Archimedean frames `(s0Of R F).XW i`**: `fun v => frameOf (Matrix.gram ℂ (X.bW false i v))` (`PartsOrth.lean:165-166`), where `frameOf A := (CFC.sqrt A)⁻¹` (`src/Formalism/LocalToGlobal/Divisibility/Frames.lean:22`) is the inverse square root of the Gram matrix of the rescaled embedded basis vectors `bC F.lv2 false i σ k = (√|F.P0|)⁻¹ • (R.FW i).j σ (bL ... k)` in the Hilbert space `(R.HW i σ).H` (`LinksDefs.lean:677-678`, `ZeroPartEigenvalueConvention.lean:134`).
   - Only outside `1 ≤ j ≤ D.R.m` does `latSeq` insert `unitLat`.

2. **`logLamOf Z hH`** — `TupPinsOfMuIsW.lean:30-49`:
   ```lean
   30: theorem nonempty_ix (hH : Holds R F) : Nonempty A3.fam3.base3.Ix :=
   31:   GlobalTheory.Div.nonempty_ix_of_pos A3 F.P0 F.ψ0 (R.toCx3 F).zs hH.ok hH.prim.block (hH.prim.pos false)
   35: def labOf (Z : ReadL R F X0 Y) (hH : Holds R F) (σ : D.what₂.FT) : A3.fam3.base3.Ix :=
   36:   if h : ∃ c, Bl.OverIx Z σ c then h.choose else (nonempty_ix hH).some
   45: def logLamOf (Z : ReadL R F X0 Y) (hH : Holds R F) (j : ℕ) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ) : ℝ :=
   46:   if e = D.what₂.embLL then Real.log (D.what₂.lamP D.what₂.mu0 j σ)
   47:   else if h : j - 1 < D.R.m then
   48:     if D.what₂.isot j σ = ⊥ then 0 else Real.log ((s0Of R F).lam ⟨j - 1, h⟩ A3.A.μ0 (labOf Z hH σ) (InfinitePlace.mk e))
   49:   else 0
   ```
   At `e = D.what₂.embLL`, it records `Real.log (D.what₂.lamP D.what₂.mu0 j σ)` (where `lamP` is tied by `Read.lam : DV.LamDef D`, `StableIffCarrierEq.lean:185`, to the normalized trace `lamTr` of `thetaP ∘ thetaT` on `isot j σ`, `src/Formalism/LocalRingCardinality/DataKap.lean:125-131`). At other embeddings `e ≠ D.what₂.embLL`, it selects a Hecke-type index `labOf Z hH σ` satisfying `OverIx Z σ c` (`OverIx.lean:29-31`, covering `D.what₂.isot (i + 1) σ` via `Z.jW i`), and records `Real.log ((s0Of R F).lam ⟨j - 1, h⟩ A3.A.μ0 (labOf Z hH σ) (InfinitePlace.mk e))` (the row-side infinite-place eigenvalue `R.lam3`, `ZeroPartEigenvalueConvention.lean:141`).

3. **`kapSharp D`** — `src/Formalism/LocalRingCardinality/DataKap.lean:155-170, 225`:
   ```lean
   155: def lamProd (D : D7) {n : ℕ} (ty : Fin n → D.what₂.FT) : ℝ :=
   156:   ∏ σ, ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ)
   ...
   165: def iiStar : EE →ₗ[ℂ] EE := S.iotaQ D.what₂.mu0 ∘ₗ LinearMap.adjoint (S.iotaQ D.what₂.mu0)
   167: def kapRatio {n : ℕ} (ty : Fin n → D.what₂.FT) : ℝ := (LinearMap.det S.iiStar).re / DV.lamProd D ty
   169: def kapOf {n : ℕ} (ty : Fin n → D.what₂.FT) : ℝ :=
   170:   if 0 < S.kapRatio ty then S.kapRatio ty ^ ((n : ℝ)⁻¹) else 1
   ...
   225: def kapSharp (D : D7) : ℝ := (RowSide.sharp D).kapOf D.what₂.ft
   ```
   where `RowSide.sharp D` (`src/Formalism/LocalRingCardinality/PrincipalHermitianLattice.lean:67-84, 118-136`) packages `D.what₂.Amb`, `Mult`, `io`, `iota`, `Qsp`, and `iotaQ`. Thus `kapSharp D` is the `Drows`-th root of `Re(det(iotaQ ∘ iotaQ*)) / ∏_{σ,j} lamP(μ0, j, ft σ)` (defaulting to `1` if nonpositive). In `x0`, `kapR` is set to the constant function `fun _ => kapSharp D` across all embeddings (`TupPinsOfMuIsW.lean:114`).

### 6.2 Real proofs on this route about `mjLat`, `logLamOf`, and `kapSharp`

Genuine, non-trivial proofs exist on this route establishing all `DivX` lattice/metric axioms for `x0` and spectral properties of `kapSharp`:

- **`mjH_good`** (`MapSeqIndAll.lean:153-156`): proves `∀ j, (mjH Z j).Good` (`(∀ v, IsUnit (A.X v).det) ∧ A.L.FG ∧ Submodule.span K A.L = ⊤`, `src/Formalism/LocalRingCardinality/DataArith.lean:80`). Uses `ofCoord_good` (`MapSeqIndAll.lean:25-27`), `frame_gram_unit` (`src/Formalism/LocalToGlobal/IndefiniteReal/CxLemmas.lean:154-156`, positive-definite Gram matrix ⇒ invertible `frameOf` determinant), `RealDat3.kForm_of` (`src/Formalism/LocalToGlobal/IndefiniteReal/BaseLiftsPackageOfPrimitiveLinks.lean:98`), and `unitLat_good` (`MapSeqIndAll.lean:29-34`).
- **`jM_basis`** (`MapSeqIndAll.lean:158-166`) via **`jW_basis`** (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ClosureImageSpan.lean:81-93`): proves linear independence and full `ℂ`-span of `jM Z j ((mjH Z j).b k)` in `D.what₂.Mj j`, using injectivity of `Y.mj.eW i` (from `Y.mj.eW_norm i`), `eW_jW_eq`, `goodForm_li`, `goodForm_span` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LiftMatrixComputesLiftRational.lean:246-272`), and `Y.mj.eW_range i`.
- **`jM_lat`** (`MapSeqIndAll.lean:168-174`) and **`mjLat_sub`** (`MapSeqIndAll.lean:176-179`) via **`jW_lat`** (`ClosureImageSpan.lean:110-146`): proves `OLatTie D.what₂.embLL (D.what₂.MjLat (i+1)) (Z.jW i) ((s0Of R F).M i)` (`RowSideTie.lean:46-49`), identifying the integral lattice `(mjH Z (i+1)).L` with the `𝓞 LL`-span of `D.what₂.MjLat (i+1)` under `jM Z (i+1)`. This relies on three real algebraic proofs:
  - `chiKs` (`ClosureImageSpan.lean:95-106`, showing character values descend to `Ks`),
  - `GlobalTheory.GoodLatDescent.span_MK_good` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SpanGoodEqMj.lean:105-256`, proving `Submodule.span (𝓞 LL) {y | y ∈ A.MK ∧ y ∈ A.Wgood ...} = A.Mj ...` via `Ks`-coordinate maps, denominator clearing, and flatness `Module.Flat.exists_factorization_of_comp_eq_zero_of_free` over `𝓞 Ks`),
  - `closure_image_span` (`ClosureImageSpan.lean:15-44`) and `oLatTie_of_closure` (`LiftMatrixComputesLiftRational.lean:60-133`).
- **`jM_metric`** (`MapSeqIndAll.lean:181-185`) via **`jW_norm`** (`ClosureImageSpan.lean:150-167`): proves that at `InfinitePlace.mk D.what₂.embLL`, the coordinate Hermitian norm `cnorm (fcoord (mjH Z j).b (mjH Z j).X ... x)` equals `‖jM Z j x‖`. Uses `norm_w0C_sq` (`ClosureImageSpan.lean:55-66`, via `majAt_gram` at `CxLemmas.lean:140-152`), `liftWeight_complexPoint_eq_twist` (`LiftMatrixComputesLiftRational.lean:290-298`), `Y.mj.eW_norm i`, and cancellation of `RealDat.nP F.lv2 false > 0`.
- **`nonempty_ix`** (`TupPinsOfMuIsW.lean:30-31`) via **`nonempty_ix_of_pos`** (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonemptyFiniteTypeIndexOfRowsPos.lean:22-37`): proves `Nonempty A3.fam3.base3.Ix` from `hH.ok`, `hH.prim.block`, and `hH.prim.pos false`.
- **`kapOf_pos`** (`DataKap.lean:172-176`) and **`RowLatticeBoundForBasis.kap_eq`** (`DataKap.lean:178-221`): proves `0 < kapSharp D` and proves via orthonormal-basis diagonalization that `kap = S.kapOf ty` whenever `RowLatticeBoundForBasis b ty kap` holds with `0 < n`.

### 6.3 Summary of what is assumed vs. what is proved

- **Immediate assumptions of `x0`'s lattice lemmas**:
  - From `Y : Read ...` and `Z : ReadL ...` (`StableIffCarrierEq.lean:116-218`): `Y.mj : GlobalTheory.RealGeo.MjTie R F` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/JEvExists.lean:50-55`, giving the embedding `eW` of `D.what₂.Mj (i+1)` into `(R.HW i (sg0 D A)).H` with its range, norm scaling `eW_norm`, and `MK ∩ Wgood` lattice characterization `eW_lat`), plus `Z.jW_read` (`StableIffCarrierEq.lean:214-215`) and `R.hv0`.
  - From `hH : Holds R F` (`StableIffCarrierEq.lean:87-91`, fields `PrimRows3` and `UnusedChoiceStatements` at `BaseLiftsPackageOfPrimitiveLinks.lean:199-228`): specifically `hH.prim.mLat` (`MLat`), `hH.prim.unif` (`LUnif`), `hH.aux.levelW` (`LLevelW`), `hH.aux.integral` (`LIntegral`), and (for `nonempty_ix`) `hH.ok`, `hH.prim.block`, `hH.prim.pos false`.
  - From `hP : Pins R F cG` (`StableIffCarrierEq.lean:81-85`, `Keep` at `lines 63-79`): specifically `hP.char.base.lev`, `hP.char.base.grp.chiW`, `hP.keep.valKs`, `hP.keep.levKs` (all used in `jM_lat`/`mjLat_sub` via `jW_lat` and `chiKs`).
- **Upstream provenance of `Holds R F` and `Pins R F cG`**:
  - In `exists_divT` (`TupPinsOfMuIsW.lean:182`), `hP := l.what₂.r.z.pins` comes from `z : Dat ...` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/FieldValuesMemFixedField.lean:44`), and `hH := l.what₂.r.intersectionNumber_baseChange` comes from `r : RowsAre ...` (`line 64`).
  - `Holds` is first produced in `exists_pre2_of_fine_of_resChar_mem` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConstructionStartingChoicesOfFineAdelicData.lean:195-240`, line `217`) via `WeightCaseCondition` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonzeroPlacesOverPrimesLifts.lean:102-105`), which takes row-side hypotheses including `GlobalTheory.RealGeo.InGeo z.geo` (`JEvExists.lean:119-127`, a 7-field condition on `GeoHalf`).
  - `WeightCaseCondition` is itself proved on the live route (`ExistsBaseLatticeOfPrime.lean:62` via `w_of_weight_residue_char` / `atDat_holds_alt`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/WeightSetResidueCharacteristic.lean:18-55`): `LUnif` is proved from `InGeo.jUnif` and `z.geo` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LUnifAtDat.lean:25-45`), `LIntegral` from `InGeo.latFull` and `z.geo` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AtDatLIntegral.lean:18-22`), `MLat` from `LIntegral` (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LMLatOfLIntegral.lean:83-96`), and `LLevelW` via `levelW_of_irr` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/RationalDataSizedFamily.lean:22-24`).
- **What is proved vs. what is NOT proved (the structural boundary)**:
  - **Proved**: `mjLat R F j`, `logLamOf`, and `kapSharp` are genuine row-side objects with genuine proofs connecting the row-side coordinate lattices `(s0Of R F).M`/`XW` and automorphic spaces `R.FW` to `D.what₂.Mj` and `D.what₂.MjLat` (assuming the row-side data `Dat`/`Pins`/`Read`/`ReadL` and `InGeo z.geo`).
  - **Not proved**: Nothing on this route relates `mjH Z j` to any non-degenerate geometric object in `DivX.geo`. Because `x0` installs `mjH Z`, `logLamOf Z hH`, and `fun _ => kapSharp D` directly into `DivX` alongside `geoDegenerate`/`divXFl` (where `iMj := 0`, `Inhabited.lean:860`), the `DivX`-to-row-side identifications required by `exists_divT` (`MjAre`, `Y.kapR σ = kapSharp`, `LamAre`) are discharged definitionally (`rfl` / `HEq.rfl`) by matching the installed row-side objects against themselves.

---

## Summary Table

| Item | Claim Checked | Verdict | Key Citation & Code Evidence |
|---|---|---|---|
| 1a | `divEx_of_ox` ignores 3 hypotheses (`fun _ _ _`), calls `divEx_prov` | **TRUE** | `TupPinsOfMuIsW.lean:211-213`: `fun _ _ _ 𝒮 hOx => divEx_prov 𝒮 hOx` |
| 1b | 3 `Prop`s are published-theorem statements; callers & origin of args | **TRUE** | Ray class field, PIT, CM curve; called via `divEx_geoCl` ← `memberE_closing(_alt_alt)`; args come from closed repo proofs (`globalArtin`, `cmCurveGoodOutsidePrime`) |
| 2 | `divEx_prov` fills `OAt.geo := trivial`, `OAt.lam := lamAre_heq ...` | **TRUE** | `TupPinsOfMuIsW.lean:204,209`: `exact ⟨⟨trivial, lamAre_heq hp ht (hX ▸ h4)⟩⟩`; `GeoCl.base` is in `divEx_geoCl:49` |
| 3 | Field table for `geoDegenerate`, `divXFl`, and `x0` (every row) | **TRUE** | All rows verified verbatim in `Inhabited.lean:241-306,829-861` and `TupPinsOfMuIsW.lean:57-121` |
| 4 | `geoOver_stages` proves `GeoOver (fun _ => True)` for `divXFl`; `graft` takes only lattice/num from seed | **PARTLY TRUE** | `geoOver_stages` proves `GeoOver ... X₀` witnessed by `divXFl`; `graft` (`GeoTiedPGraft.lean:12-22`) also takes 15 `Qp`/`QPl`/local fields from `X₂ = reQ ... X₁`; `divXFl` inherits `Surf*`/`vdd` from `X₂` |
| 5 | `DivEx` structure; `exists_divT` discharges via `rfl`/`HEq.rfl`; `x0` defs | **PARTLY TRUE** | All 6 proof terms & `x0`/`mjH` defs verbatim TRUE (`TupPinsOfMuIsW.lean:84,112,114,190-191`); `DivT` also carries `Qp`/`chr`/`loc`, and `DivEx:185` uses `𝒮.Ox` (instantiated to `OAt`) |
| 6a | `mjLat`, `logLamOf`, `kapSharp`: degenerate or substantive? | **SUBSTANTIVE** | Real row-side Hermitian lattices (`HLat.ofCoord`/`Mcoord`/`frameOf`), eigenvalues, & spectral root (`DataKap.lean:165-170,225`), not `PUnit`/`0` stubs |
| 6b | Real proofs & assumptions on this route | **REAL PROOFS (ROW-SIDE ONLY)** | `mjH_good`, `jM_basis`, `jM_lat` (`span_MK_good`), `jM_metric`, `kap_eq` are real proofs from `Pins`/`Holds`/`InGeo`; no bridge to `DivX.geo` (`iMj := 0`) |
