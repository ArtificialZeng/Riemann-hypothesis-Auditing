# Soundness-Hygiene Audit (Task D): `~/rh-audit/src/omega`

## Scope, Methodology, and Verification Boundary

- **Target audited**: Read-only source inspection of `~/rh-audit/src/omega` at commit `c7d25b3bf` (`175,189` tracked `.lean` files totaling `17,374,250` lines: `175,187` original submission files under `src/`, plus Comparator's `src/Challenge.lean` and `ci/Audit.lean`; plus `24` non-`.lean` config/CI/doc files).
- **What is VERIFIED from source**:
  - Exhaustive single-pass and targeted Python/PCRE2 lexical & structural scans across all `175,189` `.lean` files and all `24` non-`.lean` files (verified with regex self-tests against positive controls).
  - Direct line-by-line source inspection of `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `comparator.json`, `verify`, `ci/*`, `.github/*`, `src/Statements.lean`, `src/Challenge.lean`, `src/Main.lean`, `src/Supplements/Kernels/*`, `src/BuildAid/*`, all metaprogramming files (`CutCptCopy.lean`, `Imports.lean`, `OwnStruct.lean`, `EvalFrameOrd.lean`, `FramesTildeGammaValues.lean`, `ExistsGIs.lean`), representative `Fact`/priority/core-type instances, and the top-level discharge chain into `Main.lean`.
  - Exact count of comment-marker lines (`--`, `/-`, `-/`) across all `175,189` `.lean` files: **1 line total**, exclusively `src/Challenge.lean:18` (`--` and `/-` appear `0` times in the `175,187` submission files), eliminating comment-hiding or comment-stripping ambiguity.
- **What is INFERRED / NOT VERIFIED (no Lean installation, no network)**:
  - Because Lean is not installed, we did **not** compile the project, run `#print axioms`, run `leanchecker`, or replay `.olean` files through external kernels. Thus we cannot confirm from execution that the codebase actually compiles cleanly under Lean `v4.33.1`, nor can we observe runtime/kernel behavior (e.g., whether any term triggers a Lean `v4.33.1` kernel/runtime bug).
  - Because network access is disabled, we did **not** independently verify on GitHub that `lake-manifest.json`'s commit SHAs (e.g., `mathlib` rev `0df444a360eaa60ab8c11dca51a86af692955474`) correspond to unmodified upstream `leanprover-community/mathlib4` commits.
  - Because `src/` has 17.4M lines, we verified the absence of soundness-breaking syntax globally via exhaustive automated scans, and verified the discharge of literature/published hypothesis bundles along the top-level call chain by direct reading, rather than manually inspecting every intermediate proof body.

---

## 1. Soundness-Breaking and Trust-Expanding Primitives

**VERIFIED from exhaustive scan over all `175,189` `.lean` files (`17,374,250` lines):**

| Construct / Pattern | Total Matches | In `Main` Closure (`175,187` files) | Risk Assessment | Representative `file:line` & Snippet |
|---|---:|---:|---|---|
| `\baxiom\b` (exact) | **0** | **0** | Clean | None. Case-insensitive `\baxiom\b` yields only 2 section markers: `src/GroundTheory/LocalFields/LocalAxiom.lean:120` (`section Axiom`) and `:157` (`end Axiom`). |
| `\bsorry\b` | **5** | **0** | Clean | All 5 are in unimported Comparator harness `src/Challenge.lean:19,21,23,25,27`, e.g. `src/Challenge.lean:19`: `theorem riemannHypothesis : RiemannHypothesis := by sorry` |
| `sorryAx` | **0** | **0** | Clean | — |
| `\badmit\b` | **0** | **0** | Clean | — |
| `\bnative_decide\b` | **0** | **0** | Clean | — |
| `ofReduceBool` (`Lean.ofReduceBool`) | **0** | **0** | Clean | — |
| `ofReduceNat` (`Lean.ofReduceNat`) | **0** | **0** | Clean | — |
| `trustCompiler` (`Lean.trustCompiler`) | **0** | **0** | Clean | — |
| `implemented_by` | **0** | **0** | Clean | — |
| `\bextern\b` | **0** | **0** | Clean | — |
| `\bunsafe\b` | **0** | **0** | Clean | Note: `allowUnsafeReducibility` is a `set_option` (37 hits), audited in §2. |
| `unsafeCast` | **0** | **0** | Clean | — |
| `lcProof` | **0** | **0** | Clean | — |
| `\bopaque\b` | **0** | **0** | Clean | — |
| `\bcsimp\b` | **0** | **0** | Clean | — |
| `skipKernelTC` / `debug.skipKernelTC` | **0** | **0** | Clean | — |
| `addDeclWithoutChecking` | **0** | **0** | Clean | — |
| `postulate`, `reduceBool`, `reduceNat`, `panic!`, `unreachable!`, `dbg_trace` | **0** | **0** | Clean | — |
| `\bpartial\b` | **2** | **2** | Benign (meta-only) | See below. |
| `\bdecide\b` (all forms) | **8,187** | **8,187** | Benign (kernel-checked) | Breakdown below. |

### Detailed Inspection of Non-Zero Category 1 Hits

1. **`sorry` (5 occurrences, 0 in `Main` closure)**:
   - Exclusively in `src/Challenge.lean:19,21,23,25,27`. Verified via the `src/` import graph that `Main`'s transitive import closure comprises `175,187` of `175,188` modules under `src/`, with `Challenge` being the sole excluded module.

2. **`partial` (2 occurrences, strictly in metaprogramming helpers)**:
   - `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:41`:
     ```lean
     partial def go (env : Environment) (n : Name) (st : NameSet × NameSet × Array Name) : NameSet × NameSet × Array Name :=
     ```
   - `src/Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:18`:
     ```lean
     partial def copyAt (probe : Bool) (e tgt : Expr) (path : String) (fuel : Nat) : StateT (Array String) MetaM Expr := do
     ```
   - **Assessment**: Both are meta-level functions operating on `Environment`/`Expr` inside elaboration helpers (`elab`), not mathematical definitions or proof terms. In Lean 4, `partial` definitions are opaque to the kernel and cannot be unfolded to prove false propositions; here they do not appear in any theorem statement or proof term at all.

3. **`decide` breakdown (8,187 total occurrences; 0 `decide +native`)**:
   - **`decide +kernel`: 151 occurrences** — invokes kernel reduction (not native compilation; never introduces `Lean.ofReduceBool` or `Lean.trustCompiler`). Representative samples:
     - `src/Development/AbelianVarietyTheory/Definitions/Foundations/StrictInterlaceIffDescEnum.lean:1029`:
       ```lean
       {(53 / 2, true), (37 / 2, false), (21 / 2, true), (3 / 2, true), (1 / 2, true), (-1 / 2, true)} := by decide +kernel
       ```
     - `src/Development/AbelianVarietyTheory/Definitions/Foundations/UnitarySixTwoHarishChandraParameter.lean:27`:
       ```lean
       (∀ j ∈ range 5, (grid4.weightX j).card = grid4.rankX j) := by decide +kernel
       ```
   - **`decide +revert`: 8 occurrences** — standard kernel-checked `decide` after reverting local hypotheses. Representative samples:
     - `src/Development/AbelianVarietyTheory/Definitions/Foundations/ActWBOfInvariant.lean:255`:
       ```lean
       have e : (((3 : ℕ) : ZMod 5))⁻¹ = 2 := inv_eq_of_mul_eq_one_right (by decide +revert)
       ```
     - `src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeviIdempotentSplitting.lean:150`:
       ```lean
       theorem neg_eq_one_iff (s : SignType) : -s = 1 ↔ s = -1 := by decide +revert
       ```
   - **`decide := true` (all `decide :=` occurrences): 26 occurrences** — **100% (`26/26`)** appear inside `simp (config := {decide := true})` or `simp_all (config := {decide := true})` (`0` non-`simp` occurrences). Representative samples:
     - `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AlternatingCubeProductValueFderivAtZero.lean:26`:
       ```lean
       simp (config := {decide := true}) [Finset.prod_insert]
       ```
     - `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/HighGOf.lean:74`:
       ```lean
       simp only [map_add, hpd]; simp (config := { decide := true })
       ```
   - **Standard `decide` (~8,002 occurrences)**: Routine finite decidability proofs and `Bool` coercions, all kernel-checked. Representative samples:
     - `src/CompanionTheory/RealGroups/GeneralUnitaryRepresentations/ArchimedeanJacquetSegments/CuspPair.lean:31`:
       ```lean
       have k2 : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
       ```
     - `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/AmpleOnAbelianBase.lean:150`:
       ```lean
       def ind (S : Finset ℕ) : ℕ → Bool := fun q => decide (q ∈ S)
       ```

---

## 2. Metaprogramming, Elaboration, Options, Attributes, and Instances

### 2A. Metaprogramming and Environment Manipulation

**VERIFIED counts across all `175,189` `.lean` files:**
- `addDeclWithoutChecking`: **0** | `addAndCompile`: **0** | `setEnv`: **0** | `Environment.add`: **0** | `initialize`: **0** | `builtin_initialize`: **0** | `run_elab`: **0** | `run_meta`: **0** | `#eval`: **0** | `elab_rules`: **0** | `macro_rules`: **0** | `syntax`: **0** | `syntax_cat` / `declare_syntax_cat`: **0** | `simproc` / `dsimproc` / `register_simp_attr` / `register_tactic_extension`: **0** | `import Lake`: **0**.
- **External (non-Mathlib, non-project) `import` lines**: **15** total:
  - 10 lines: `src/BuildAid/D1.lean`–`D5.lean:1–2` (`import Lean.LibrarySuggestions.Basic`, `import Lean.Elab.Command`).
  - 2 lines: `import Lean` in `src/Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean:1` and `src/Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:1`.
  - 3 lines: `import Batteries.Tactic.OpenPrivate` in `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/HeightVanishingHypotheses.lean:23`, `.../PrimeIndexConstruction/PsOfForm.lean:3`, and `.../OrdinaryJacquetModules/PartPt.lean:3` (supporting `220` `open private` lines).

Every active metaprogramming construct in the repository was individually inspected (including two categories — `run_tac` and `@[positivity]` — not covered by the repository's own `verification/static-scan.txt`):

1. **`run_cmd` / `Lean.modifyEnv` (5 occurrences — all `src/BuildAid/D1.lean`–`D5.lean:4`)**:
   - Example `src/BuildAid/D1.lean:1–4`:
     ```lean
     import Lean.LibrarySuggestions.Basic
     import Lean.Elab.Command

     run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CompanionTheory"
     ```
   - `D2`–`D5` identically add `"CrystallineSemistableComparison"`, `"GlobalTheory"`, `"PositivityTheory"`, `"UpperTheory"`. Imported in `38` files.
   - **Assessment**: Soundness-benign. Modifies only the library-suggestion metadata extension (`nameDenyListExt`), never adding declarations or axioms to the kernel environment.

2. **`addDecl` (2 occurrences) & `elab "cpt_copy_thms"` (1 occurrence)**:
   - `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:78,82,87–89`:
     ```lean
     | .defnInfo d =>
       addDecl (.defnDecl { d with name := n', type := subst tainted d.type, value := subst tainted d.value })
     | .thmInfo t =>
       if defsOnly then continue
       addDecl (.thmDecl { t with name := n', type := subst tainted t.type, value := subst tainted t.value })
     ...
     elab "cpt_copy_thms" : command => do
       let k ← liftCoreM (copyAll false)
       logInfo m!"copied {k} declarations"
     ```
   - Invoked once in the entire repo at `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutMainCpt.lean:944–945` (`set_option maxHeartbeats 0 in` / `cpt_copy_thms`).
   - **Assessment**: Soundness-benign. Calls `Lean.addDecl` (which invokes the Lean kernel typechecker on every added `.defnDecl`/`.thmDecl`), never `addDeclWithoutChecking`.

3. **Custom `elab` tactics/commands (3 additional occurrences)**:
   - `src/Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean:5–8`:
     ```lean
     elab "kexactB " e:term : tactic => withMainContext do
       let g ← getMainGoal
       let v ← Term.elabTermAndSynthesize e none
       g.assign (← instantiateMVars v)
     ```
   - `src/Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:53–64`:
     ```lean
     elab "kcopy " t:term : tactic => withMainContext do
       ...
       g.assign (← instantiateMVars v)
     elab "#kcopy_probe " t:term " : " ty:term : command => Command.runTermElabM fun _ => do
       ...
       logInfo m!"kcopy_probe: {bad.size} refused: {bad.toList}"
     ```
   - **Assessment**: Soundness-benign. `kexactB` and `kcopy` assign elaborated proof terms to a goal metavariable (skipping elaborator `isDefEq` retries to avoid heartbeat blowup; the Lean kernel still checks the resulting proof term). Note `OwnStruct.lean:39` constructs `Expr.proj S i e` after checking `isStructure env S`, which is safe in Lean `v4.33.1` (after the fix for Lean issue #14576 in `v4.32.2`/`v4.33.0`).

4. **Custom `@[positivity]` extension (1 occurrence — missed by `verification/static-scan.txt`)**:
   - `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/EvalFrameOrd.lean:3–18`:
     ```lean
     namespace Mathlib.Meta.Positivity
     open Lean Meta Qq
     @[positivity Formalism.HC.Frame.ord _]
     def evalFrameOrd : PositivityExt where eval {u α} _zα pα? e :=
       ...
       | 0, ~q(ℕ), ~q(Formalism.HC.Frame.ord $a) =>
         assertInstancesCommute
         return .positive q(Formalism.HC.Frame.ord_pos $a)
     ```
   - **Assessment**: Soundness-benign. Standard Mathlib `positivity` tactic extension producing a kernel-checked proof term using `Formalism.HC.Frame.ord_pos`.

5. **Inline `run_tac` blocks (32 occurrences across 17 files — missed by `verification/static-scan.txt`)**:
   - 30 occurrences across 15 files are identical revert-all helpers, e.g. `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsBoundAbsLocalLatticeCompletionEntries.lean:12`:
     ```lean
     | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.LocalLatticeBound.exists_bound_latLoc
     ```
   - `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FramesTildeGammaValues.lean:70–82`: uses `Lean.Meta.mkAppM ``Subsingleton.elim #[fi.toExpr, inst]` and `g.note` to equate two `Fintype` instances.
   - `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsGIs.lean:81–83`:
     ```lean
     run_tac do
       let m ← Lean.Elab.Tactic.getMainGoal
       m.withContext do m.assign (← Lean.Meta.getFVarFromUserName `h)
     ```
   - **Assessment**: Soundness-benign. All 32 execute inside tactic mode and produce ordinary proof terms verified by the Lean kernel.

6. **`macro` definitions (87 occurrences total)**:
   - Breakdown: `40 local tactic`, `10 scoped tactic`, `22 global tactic`, `14 local term`, `1 scoped term`, **0 global term**, **0 command**.
   - Representative samples: `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/PlaceModelImp.lean:27` (`scoped macro:max "kc% " e:term:max : term => `((by kexactB $e))`), `src/Development/WeilBound/CoreStatements/HodgeTatePoints/CbBase.lean:34` (`macro "zz" : tactic => ...`).
   - **Assessment**: Soundness-benign. None alters term parsing globally or command elaboration.

7. **`notation` / `infixl` (1,723 declarations total; 0 global)**:
   - `1,696` `local`/`scoped` `notation` declarations + `27` `local`/`scoped` `infixl` declarations (`0` global `notation`, `0` `infix`/`infixr`/`prefix`/`postfix`). The remaining `15` occurrences of the word `notation` are `open scoped LSeries.notation` (e.g., `src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean:5`).

### 2B. Complete `set_option` Census (88,139 occurrences across 33 distinct options)

**VERIFIED: 0 `debug.*` options (`0` `debug.skipKernelTC`).** All 33 distinct options found across all `175,189` `.lean` files:

| Count | Option | Values Observed / Notes | Representative `file:line` |
|---:|---|---|---|
| 57,556 | `maxHeartbeats` | numeric (incl. `0` in `CutMainCpt.lean:944`) | `src/CompanionTheory/AutomorphicTheory/PieriRules/ThetaBesselIsometries/DualTensorBesselMomentStatement.lean:17` |
| 11,203 | `autoImplicit` | **`false` in all 11,203 (`0` `true`)** | `src/CompanionTheory/SpectralGeometry/LocalGlobalProofs/ConvexCones/ExistsBalancedFormsDominating.lean:7` |
| 7,478 | `maxSynthPendingDepth` | numeric | `src/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/AePolynomialNonvanishingRowsStatement.lean:4` |
| 7,381 | `synthInstance.maxHeartbeats` | numeric | `src/CompanionTheory/AutomorphicTheory/ProductFormulaTheory/GrothendieckRingPolynomial/JacquetFunctionalClass.lean:13` |
| 1,879 | `backward.isDefEq.respectTransparency` | `false` (1,877), `true` (2) | `src/Development/AbelianVarietyTheory/Definitions/Divisors/CapDegUniformiserLine.lean:5` |
| 874 | `linter.unusedSectionVars` | `false` | `src/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean:5` |
| 503 | `linter.unusedVariables` | `false` | `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CupH0NormalCoboundary.lean:12` |
| 272 | `linter.unusedSimpArgs` | `false` | `src/Development/DiscreteGroups/GlobalIrreducibility/DzFeMat.lean:9` |
| 181 | `genSizeOfSpec` | `false` (181) | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/PlaceCharacterEqReferenceIff.lean:28` |
| 179 | `genInjectivity` | `false` (179) | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/PlaceCharacterEqReferenceIff.lean:27` |
| 122 | `linter.style.haveILetI` | `false` | `src/Development/DiscreteGroups/GlobalIrreducibility/ExistsColChar.lean:7` |
| 87 | `backward.isDefEq.respectTransparency.types` | `false` (87) | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomFixedPullbackRepresentableGlue.lean:141` |
| 51 | `synthInstance.maxSize` | numeric | `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StabilizerHaarUnimodularNormal.lean:455` |
| 46 | `linter.dupNamespace` | `false` | `src/Formalism/LocalToGlobal/HilbertRowConditions/AllJoinP.lean:8` |
| 40 | `linter.overlappingInstances` | `false` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CurveDVRSpecialization/ThickOf.lean:5` |
| 38 | `linter.all` | `false` | `src/Development/DiscreteGroups/GlobalIrreducibility/DzCliff.lean:5` |
| 37 | `allowUnsafeReducibility` | `true` (37) — solely before `attribute [local irreducible]` | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsCrisP.lean:49` |
| 34 | `linter.deprecated` | `false` | `src/Development/DiscreteGroups/GlobalIrreducibility/ExistsColChar.lean:6` |
| 34 | `maxRecDepth` | numeric | `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean:159` |
| 33 | `backward.defeqAttrib.useBackward` | `true` (33) | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEtaleNeighbourhoodFinitePieceIsolatedPoint.lean:105` |
| 31 | `hygiene` | `false` (31) — before `local notation`/`local macro` | `src/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BiTrivLiftOfIsNilpotent.lean:27` |
| 23 | `linter.style.longLine` | `false` | `src/Development/DiscreteGroups/GlobalIrreducibility/ExistsColChar.lean:9` |
| 12 | `linter.unusedTactic` | `false` | `src/Development/DiscreteGroups/GlobalIrreducibility/LConvComm.lean:6` |
| 12 | `linter.unreachableTactic` | `false` | `src/Development/DiscreteGroups/GlobalIrreducibility/LConvComm.lean:7` |
| 9 | `linter.unnecessarySeqFocus` | `false` | `src/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean:10` |
| 9 | `pp.fullNames` | `true` | `src/Formalism/LocalToGlobal/InertKernelTheory/DefsRepLt.lean:203` |
| 7 | `quotPrecheck` | `false` (7) — before `local notation` | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniqueVectorFieldOfGlobalOneFormValues.lean:36` |
| 3 | `smartUnfolding` | `false` (3) | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ECure.lean:18` |
| 1 | `warn.classDefReducibility` | `false` | `src/Formalism/SharpRestriction/LevelLetterCocycles/BaseChangeMapMemLattice.lean:34` |
| 1 | `linter.auxLemma` | `false` | `src/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsFormFamilyHypothesesChangedSecondNorm.lean:37` |
| 1 | `genSizeOf` | `false` | `src/Development/WeilBound/CoreStatements/PadicHodgeComparison/EtaleCohomologyComparison/HodgeTateResidues/IsFirstChernClassInJAlt.lean:9` |
| 1 | `linter.unnecessarySimpa` | `false` | `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NewformLiftLevel.lean:20` |
| 1 | `Elab.async` | `false` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/LinkedUnramifiedChains/TeichmullerParts/SubalgebraIntegrality/Decomp.lean:167` |

- **Assessment**: None of the 33 options compromises kernel soundness. All `allowUnsafeReducibility true` (37), `hygiene false` (31), and `quotPrecheck false` (7) uses are strictly elaborator-side controls (`attribute [local irreducible]` and `local notation`/`local macro` definitions).

### 2C. Attributes, Instances, Priorities, `open ... hiding`, `export`, `deriving`

- **`attribute [-instance]` / `attribute [-...]`**: **460** lines across **45** distinct targets (`459` `[-instance]` + `1` `[-simp]` on `LaurentPolynomial.single_eq_C_mul_T`). Top targets are project instances (`Formalism.DoubleCosetMeasures.instMeasGL`: 138; `GlobalTheory.CompHt.fintypePsi`: 115; `UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing`: 106; `UpperTheory.V.Pr.IsCD.toIsDomain`: 97). Occasional Mathlib instances are disabled locally to avoid diamonds (e.g., `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InducedSectionSmooth.lean:265`: `attribute [-instance] Matrix.normedAddCommGroup Matrix.normedSpace in`). Soundness-benign.
- **`@[reducible]` / `@[irreducible]` / `attribute [... reducible/irreducible]`**: **1,043** lines total (`968` inline attributes on newly defined project declarations + `75` `attribute [...]` commands).
  - **Only 1 file applies reducibility changes to Mathlib names**: `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/SymmetricPowerTransfer/GeneralizedEigenspaces/CharacterShapes/FiniteOrbits/FinOrbSubgroupOf.lean:213–214`:
    ```lean
    set_option allowUnsafeReducibility true in
    attribute [local irreducible] cv Kv Ov DX KD RP SA Lsq dcF SD.lvS lev SUA Subgroup.comap MulEquiv.toMonoidHom Subgroup.toGroup Subgroup.subgroupOf
    ```
  - Strictly `local` and kernel-irrelevant (Lean's kernel ignores reducibility attributes).
- **Instance overrides on core Mathlib types (`ℂ`, `ℝ`, `ℕ`, `ℤ`, `ℚ`, `ZMod`, `DirichletCharacter`)**:
  - Total `instance` declarations: **8,199** (`7,538` global, `379` `local`, `222` `scoped`, `60` `private`), plus **51,469** `attribute [... instance]` commands (`50,672` `local`, `797` global).
  - **VERIFIED: 0 overrides of core algebraic/order/topological/measure instances on `ℂ`, `ℝ`, `ℕ`, `ℤ`, `ℚ`, `ZMod`, or `DirichletCharacter`.** The sole single-argument core-looking match (`src/GroundTheory/LocalFields/AbstractLocalReciprocity/ProfiniteInteger.lean:51`: `instance : CharZero ℤ̂`) is on the project-defined `ProfiniteInteger` type (`scoped notation "ℤ̂" => ProfiniteInteger`, line 12).
  - The few `local instance`s mentioning Mathlib types re-register Mathlib's own canonical instances locally, e.g.:
    - `src/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LocalWeightCharts/NilradicalHalfSumNonneg.lean:98–101`:
      ```lean
      local instance instAlgCLM (n : ℕ) :
          Algebra ℂ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := ContinuousLinearMap.algebra
      local instance instModCLM (n : ℕ) :
          Module ℂ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := ContinuousLinearMap.module
      ```
    - `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFS.lean:22`:
      ```lean
      local instance instRealIPS : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
      ```
- **`instance (priority := ...)` (80 occurrences) & `attribute [... instance <priority>]` (473 occurrences)**:
  - Of the `473` attribute-form priority instances, `471` are `local` (e.g., `attribute [local instance 100] LieRing.ofAssociativeRing` × 172; `attribute [local instance 2000] Rep.hV2` × 158) and only `2` are global, both on project structures (`src/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean:22`: `attribute [instance 100] IsFiniteQC.isQuasicoherent`; `src/Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean:34`: `attribute [instance high] LocLat.modO LocLat.towO`).
  - Of the `80` `instance (priority := ...)` declarations, all those targeting Mathlib classes on Mathlib types are either **shortcut aliases for Mathlib's own canonical instances** or **`Prop`-valued classes**:
    - `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean:719–733` (`modTens := TensorProduct.instModule`, `modProd := Prod.instModule`, `modFun := Pi.Function.module ι O M`, `modQuot := Submodule.Quotient.module S`).
    - `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CurveDVRSpecialization/EveryPointSatisfiesFrameCondition.lean:12` & `RatTorsionFree.lean:11` (`Module.IsTorsionFree := DivisionSemiring.to_moduleIsTorsionFree`).
    - `src/GroundTheory/ProfiniteCohomology/PoincareDuality/Induced.lean:220` (`Finite (ULift.{u} (ZMod n))`), `src/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFD.lean:132,263` (`IsDomain`, `UniqueFactorizationMonoid`), `src/ReciprocityTheory/Hypotheses/GalCohDefs.lean:12` (`ContinuousConstSMul`).
  - None alters the definitions in `Statements.lean` or introduces non-canonical algebraic structures on `ℂ`/`ℝ`/`ℕ`.
- **`open ... hiding`**: **2,200** occurrences, mostly project namespaces (`GlobalTheory.SW`: 1,056; `ReciprocityTheory.ChartRestriction.G.Geo.Tor`: 664) plus `open UpperHalfPlane hiding I` (116, avoiding collision with `Complex.I`). **0** occurrences in `Main.lean`, `Statements.lean`, `Challenge.lean`, or `Supplements/`.
- **`export`**: **38** occurrences, **100% (`38/38`)** inside nested project namespaces (`GlobalTheory.*`, `Formalism.*`, `PI.*`), e.g. `src/Formalism/SharpRestriction/CuspSpanNormBounds/MassAndBranchingHypotheses.lean:19` (`[Formalism.MainNotions.VanishingOnXAndXPlusMass] export Formalism.MainNotions.S.UnitaryVolumeMass (embU succMin dualZ)`). **0** at root namespace; **0** re-exporting Mathlib statement names.
- **`deriving instance`**: **0** occurrences (`deriving DecidableEq` appears **21** times on project types, e.g. `src/Formalism/DistinguishedUnitIdeals/Statement.lean:21`).

---

## 3. Name Shadowing, Statement Integrity, and Unicode Hygiene

- **`src/Statements.lean` and `src/Challenge.lean` import ONLY Mathlib**:
  - `src/Statements.lean:1`: `import Mathlib` (no other imports; lines 3–16 define `RiemannZetaZerosOnLine`, `DirichletLNonvanishingRightOfHalf`, `DirichletLZerosOnLine`, `PrimitiveDirichletLZerosOnLine`).
  - `src/Challenge.lean:1`: `import Mathlib` (no other imports). Verified byte-for-byte that lines 1–16 of `src/Challenge.lean` are identical to `src/Statements.lean`; lines 19–27 state the five headline theorems with `:= by sorry`.
- **`src/Main.lean` resolves directly to `Statements.lean` and Mathlib**:
  - `src/Main.lean:1–12`:
    ```lean
    import Statements
    import Supplements.Kernels.MainTheoremsAll

    theorem riemannHypothesis : RiemannHypothesis := rhOfAll
    theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll
    theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi
    theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1
    theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
    ```
  - Verified **0** non-ASCII characters in `src/Main.lean`, `ci/Audit.lean`, `MainTheoremsCritical.lean`, `MainTheoremsAll.lean`, and only standard mathematical Unicode (`¬ χ ℂ ℕ → ∀ ∃ ∨ ≠`) in `src/Statements.lean` and `src/Challenge.lean` (no homoglyphs / zero-width confusables).
- **Global shadowing scan over all `175,189` `.lean` files**:
  - **0** declarations anywhere in the repo named `RiemannHypothesis`, `riemannZeta`, `DirichletCharacter`, `Complex.re`, or `NeZero`.
  - Scoped project-namespace homonyms (cannot shadow Mathlib names in `Main.lean` or `Statements.lean`):
    - `Complex` (1): `src/Formalism/CoboundaryTransfers/StatementAPI.lean:7` (`Formalism.CoboundaryTransfers.Complex`).
    - `LFunction` (2): `src/GroundTheory/AutomorphicForms/GL2/GJLocalZeta.lean:431` (`GroundTheory.Automorphic.GodementJacquet.LFunction`) and `src/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean:363` (`GroundTheory.Global.HeckeCharacter.LFunction`).
    - `IsPrimitive` (4): all inside deep project namespaces (e.g., `GlobalTheory.CuspGL.IsPrimitive`, `Reformulated.AutPerF.IsPrimitive`).
    - `re` (13): all inside deep project namespaces (e.g., `GlobalTheory.SWQ.re`, `Formalism.L2.PairingIndexBounds.F.PtD.re`).
  - Core namespaces reopened: `namespace Complex` occurs once inside `namespace GroundTheory.Global` (`src/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean:3,73` — full namespace `GroundTheory.Global.Complex`, proving `units_noSmallSubgroups`); `namespace Matrix` occurs inside `GroundTheory.Global` (`.../SemilocalAlgebras/Infinite.lean:5,10`); `namespace Real` (`AnalyticChartsRealizationCompPointEq.lean:78`) and `namespace Std` (4 files) are nested inside project namespaces for project structures named `Real`/`Std`; `namespace Mathlib.Meta.Positivity` occurs once (`EvalFrameOrd.lean:3`).
  - **Root-namespace audit**: All `499` non-private, non-instance root-namespace declarations across the repository were audited; outside `Statements.lean`, `Main.lean`, `Challenge.lean`, and `Supplements/Kernels/MainTheorems.lean` (`allChi`, `rhOfAll`, `critAll`, `claimAll`), **0** collide with any Mathlib or `Statements.lean` name.

---

## 4. Build Configuration, Dependencies, and CI Hygiene

- **`lean-toolchain:1`**: `leanprover/lean4:v4.33.1`.
- **`lakefile.toml`**:
  - Line 4: `moreLeanArgs = ["--tstack=400000"]` (thread stack size only; **0** `-D` flags, **0** `--plugin`, **0** `--load-dynlib`, **0** `weakLeanArgs`).
  - Lines 6–11: `[leanOptions]` sets `autoImplicit = false`, `relaxedAutoImplicit = false`, `maxSynthPendingDepth = 3`, `pp.unicode.fun = true`, `maxHeartbeats = 4000000` (plus `GroundTheoryFields` line 41: `synthInstance.maxHeartbeats = 400000`).
  - Lines 13–16: single `[[require]]` pinning `name = "mathlib"`, `git = "https://github.com/leanprover-community/mathlib4"`, `rev = "0df444a360eaa60ab8c11dca51a86af692955474"`.
  - Lines 62–66: marked Comparator block registering `Challenge` (`roots = ["Challenge"]`).
- **`lake-manifest.json`**:
  - Pins `mathlib` at `https://github.com/leanprover-community/mathlib4` rev `0df444a360eaa60ab8c11dca51a86af692955474`, plus 8 standard inherited dependencies (`plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, `Cli`), all `"type": "git"` from `https://github.com/leanprover-community/...` or `https://github.com/leanprover/...`. **0** local path or override dependencies. *(Unverified offline: exact GitHub commit content for those SHAs.)*
- **Checked-in build artifacts / `.lake`**:
  - **None**. No `.lake` directory exists in the workspace (`.gitignore:1` excludes `.lake/`), and `git ls-files` contains **0** `.olean`, `.ilean`, `.so`, `.dylib`, `.a`, `.o`, `.c`, `.cpp`, `.bin`, `.exe`, `.tar`, `.gz`, or `.zst` files.
- **CI / Verification scripts (`ci/`, `.github/`, `verify`, `comparator.json`)**:
  - `ci/Audit.lean:1–8` imports `Main`, checks `example : RiemannHypothesis := riemannHypothesis`, and runs `#print axioms` on all 5 theorems; `ci/parts.py:354–365` asserts all 5 appear and depend only on a subset of `{"propext", "Quot.sound", "Classical.choice"}`.
  - `.github/actions/toolchain/runner.sh:53–56` downloads official `lean-4.33.1-linux.tar.zst` with SHA-256 verification.
  - **Caveat (toolchain age, inferred from Lean release history noted in `verification/NOTES.md:91–107`, not independently verified offline)**: `v4.33.1` includes the fix for wrong-structure projection soundness bug #14576, but predates later `v4.34.1` runtime fixes; `comparator.json:11–17` accordingly specifies replay through four independent kernels (`leanchecker-paranoid`, `nanoda_bin`, `con-leche`, `con-ron`) against `Challenge` with permitted axioms `["propext", "Quot.sound", "Classical.choice"]`. Nothing in our static scan suggests any construct targeting a runtime or kernel bug.

---

## 5. Hypothesis Leakage and Suspicious Typeclass Instances

- **Closedness of top-level theorems (VERIFIED by direct reading)**:
  - `src/Main.lean:4–12` (`riemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`), `src/Supplements/Kernels/MainTheorems.lean:7–16` (`allChi`, `rhOfAll`, `critAll`, `claimAll`), and `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:10–14` (`UpperTheory.FinalTheorems.everyCharacter`, `UpperTheory.FinalTheorems.riemannHypothesis`) contain **0** `variable` commands, **0** enclosing `section` hypotheses, **0** `[Fact ...]` parameters, and compile with `autoImplicit = false` (`lakefile.toml:7–8`).
  - All five headline theorems in `Main.lean` are completely closed, hypothesis-free `Prop` statements (the only typeclass binder is `[NeZero N]` bound inside the universal quantifiers of the three Dirichlet $L$-function definitions in `src/Statements.lean:7,11,15`).
  - `src/Supplements/Kernels/MainTheoremsAll.lean:1–2` and `MainTheoremsCritical.lean:1–4` import `MainTheorems` plus four auxiliary `SmallClassNumbers` modules (`ClassNumberThree`, `LenEqZeroIff`, `OnePoint`, `CorGKOf`) that do not modify or add hypotheses to `Main.lean`.
- **Audit of `Fact`, `Inhabited`, `Nonempty`, and `False`/`Empty` instances**:
  - **0** `Inhabited` or `Nonempty` instances targeting `False`, `Empty`, `PEmpty`, `RiemannHypothesis`, `DirichletCharacter`, or `Prop`.
  - The 4 instances mentioning `Empty`/`PEmpty` are benign: colimit preservation over `Discrete PEmpty.{1}` (`src/Development/EtaleCohomology/EtaleSheaves/DescEqvPf.lean:40,44`) and vacuous `∀ k : Empty, Fintype ...` (`src/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ScaledRankOneLeStandardRankOne.lean:362`; `.../NotIsArithVarNoBlocks.lean:76`).
  - All **117** `Fact` instances were enumerated. Most are routine primality/order/irreducibility facts (e.g., `Fact (Nat.Prime 5)`, `Fact (D.host.g k).Prime`). The `18` instances wrapping larger mathematical properties — in `src/Formalism/LocalToGlobal/SiegelLatticeTheory/WeightedGaugeFactors/FactsDS.lean:16–40` (10 instances), `FactsCC.lean:85`, `FactsFD.lean:102`, `FactsGV.lean:6`, and `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/{CoefWeightedLocUncond,GaugeVolUD,HermRepUnram,InstFactDecLow,KFinDenseMain,RhsWLimOfLeaves}.lean` — were **directly read and verified**: every single one is constructed as `⟨proved_theorem⟩` (e.g., `FactsDS.lean:16`: `instance factCoefWeightedLoc : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc⟩`). Because `Fact P` requires an actual term of type `P` (and there are `0` axioms/`sorry`s in the `Main` closure), these cannot smuggle unproven assumptions.

---

## 6. Literature/Published Hypothesis `structure ... : Prop` Bundles and Top-Level Discharge

- **Repository census**: **4,073** `structure ... : Prop` and **40** `class ... : Prop` declarations (`262` with literature/published/hypothesis-related names), plus **1,567** declarations under `GlobalTheory.Published.*` (`912 theorem`, `593 def`, `11 abbrev`, `7 lemma`, `6 structure`, `4 instance`, **0 `axiom`**).
- **VERIFIED top-level discharge chain (none assumed at top level)**:
  1. `src/Main.lean:4`: `theorem riemannHypothesis : RiemannHypothesis := rhOfAll`
  2. `src/Supplements/Kernels/MainTheorems.lean:7,9`:
     ```lean
     theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter
     theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi
     ```
  3. `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7–11`:
     ```lean
     theorem UpperTheory.FinalTheorems.everyCharacter_of_row (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) : UpperTheory.EveryCharacter :=
       UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩ (UpperTheory.One.vwin_of_row h)

     theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=
       UpperTheory.FinalTheorems.everyCharacter_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
     ```
  4. **Discharge of the three top-level inputs (all confirmed to be closed `theorem`s, not axioms or variables)**:
     - **`UpperTheory.Zero.LLC.recTExists`** (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20–66`):
       ```lean
       theorem UpperTheory.Zero.LLC.recTExists : UpperTheory.Zero.LLC.RecTExists := by ...
       ```
       Proved directly from `artEx`, `cuspEx`, `exists_isLExt`, `extDim`, `extTw`, `extDual`, `extInj`, `extDepth`, `typeIff`. No section variables or axioms.
     - **`UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`** (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`):
       ```lean
       theorem galoisLocalGlobalStrong_recParameter : UpperTheory.GalStar.Row0b recT := galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK
       ```
       Discharged via `galoisRepresentations_of_thetaLift` (`.../GaloisRepresentationsOfThetaLift.lean:6` → `.../Development.lean:30`, `.../WeightOneGeometricRealization.lean:11`) and `UpperTheory.TP.K.tLiftK` (`.../ThetaKernels/TLiftK.lean:4–5` → `.../TPGHolds.lean:58`). No section variables or axioms.
     - **`UpperTheory.One.vwin_of_row`** (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4–5`):
       ```lean
       theorem UpperTheory.One.vwin_of_row (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) : UpperTheory.Top.VWin :=
         UpperTheory.One.Join.automorphic_window_of_inputs (UpperTheory.LiteratureTheorems.OpenImageCondition.mk h) UpperTheory.BaseChangeIdentities.baseChangeN h
       ```
       Constructs `OpenImageCondition` (`.../TemperedProductOfSquareIntegrable.lean:207–208`, a single-field `structure : Prop` wrapping `RowT`) from `h`, and supplies closed theorem `UpperTheory.BaseChangeIdentities.baseChangeN` (`.../BaseChangeIdentities/DefiniteNHolds.lean:5–6` → `FillPre.lean:7`, `FrameEx.lean:15`).
  5. **Discharge of `OpenLiteratureStatements`, `HypothesesUE`, and `Hypotheses₂`**:
     - `UpperTheory.LiteratureTheorems.OpenLiteratureStatements` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215–218`) has only 3 fields (`caraianiLocalGlobalDual`, `localLanglandsExists`, `galoisRepOfPolarizedPairLit`), all discharged at `MainConclusion.lean:8` by `⟨h, UpperTheory.Zero.LLC.recTExists, h⟩`.
     - Inside `EveryCharacterOfLiteratureOfVWin.lean:810–813`, `every_character_of_literature_of_vWin` populates `UnitaryGroupThirdPlaceHypotheses`, `ThetaLocalInputs`, and `PublishedHodgeBundleTheorems` from proved theorems and invokes `_root_.UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (`.../ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69–73`), which calls `nonempty_hyps_definite_side_of_closed_bound` (lines 44–68, also passing `geoCl anyGeometry` at lines 60, 63, 67) and `_root_.UpperTheory.Top.every_character_of_green_v_win` (`.../ThirdPlaceSeries/TopPlug.lean:16–18`).
     - `GlobalTheory.Fc.S0.HypothesesUE` (`src/Development/AbelianVarietyTheory/Definitions/Divisors/HypothesisBundleConversions.lean:56`) and `GlobalTheory.FunPr.Hypotheses₂` (`.../DiscreteSeriesHermitianUnique.lean:67`) appear in the parallel theorem `everyE₂` (`.../FockModels/EveryCharacterE.lean:67–71`), which is not directly called by `MainConclusion.lean` (the active path uses the renamed `UnitaryGroupThirdPlaceHypotheses` / `ThetaLocalInputs` twin in `SiegelEisensteinSecondTermHypotheses.lean`), while `GlobalTheory.NLink.Hypotheses₂` (`.../BoundAtTwoAndThreeForFamily.lean:18`) is discharged by `published_results_local` (`EveryCharacterOfLiteratureOfVWin.lean:658–665`). None is assumed unproved.
- **Logical distinction regarding the critic's `anyGeometry` claim**: While `geoCl anyGeometry` (`OverIx.lean:19`: `def anyGeometry : GeoP := fun _ _ _ => True`) is indeed passed on the active `Main.lean` chain (`SiegelEisensteinSecondTermHypotheses.lean:60,63,67`), a `True` predicate inside an *intermediate* lemma is **not** a soundness-hygiene exploit. If Lean's kernel typechecks `Main.lean` with no extra axioms, `riemannHypothesis` proves Mathlib's closed `RiemannHypothesis` regardless of whether intermediate constructions discard geometric hypotheses.

---

## VERDICT

**High confidence (static source audit, subject to the unverified-compilation / unverified-SHA caveats above): NO soundness-hygiene cheat or reward-hacking vulnerability was found anywhere in the 17.4M-line codebase.** Across all `175,187` submission modules in `Main`'s import closure, there are **0** `axiom`, `sorry`, `sorryAx`, `admit`, `native_decide`, `Lean.ofReduceBool`, `ofReduceNat`, `Lean.trustCompiler`, `implemented_by`, `extern`, `unsafe`, `unsafeCast`, `lcProof`, `opaque`, `csimp`, `addDeclWithoutChecking`, `setEnv`, `initialize`, `builtin_initialize`, or `debug.*` / `skipKernelTC` directives; `Statements.lean` and `Challenge.lean` import only `Mathlib` with byte-identical definitions, no Mathlib statement symbol is shadowed or homoglyphed, all five theorems in `Main.lean` are closed and hypothesis-free, and every literature/published `structure ... : Prop` bundle (including `OpenLiteratureStatements`, `OpenImageCondition`, and `Hypotheses₂`) is discharged by closed `theorem`s (`recTExists`, `galoisLocalGlobalStrong_recParameter`, `vwin_of_row`, `baseChangeN`). Our audit uncovered two benign metaprogramming mechanisms omitted from the repository's own `verification/static-scan.txt` — `32` inline `run_tac` blocks across `17` files and `1` `@[positivity]` extension (`EvalFrameOrd.lean`) — alongside the known `BuildAid` deny-list `run_cmd`s, kernel-checked `addDecl` copying (`CutCptCopy.lean`), and `kexactB`/`kcopy` elaborators, all of which remain kernel-checked; consequently, if the codebase compiles and passes independent kernel replay (`leanchecker-paranoid`, `nanoda`, `con-leche`, `con-ron`) against official `mathlib4` commit `0df444a360ea`, the final statements in `Main.lean` cannot be falsified by any source-level Lean soundness trick.
