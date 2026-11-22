# Riemann-hypothesis-Auditing

Independent audit of the claim that Levent Alpöge's Lean 4 proof of the Riemann Hypothesis
(released 2026-11-20, written with Claude) is invalid because its geometry predicate is defined as

```lean
def anyGeometry : GeoP := fun _ _ _ => True
```

The objection is due to Jenny Lorraine Nielsen, *Invalidity of the Alpoge Proposed Proof of the Riemann Hypothesis* (PhilArchive, 2026-11-21).
This repository does **not** try to prove or disprove the Riemann Hypothesis. It checks whether that objection is correct.

**Report (Chinese, PDF): [`report/audit_report.pdf`](report/audit_report.pdf)**

## Verdict

**The objection does not hold.** Its factual observations are largely correct; the inference from them to "the proof is invalid" is not.

| # | Claim | Fact check | Does invalidity follow? |
|---|---|---|---|
| C1 | The geometry predicate is defined to be `True` | True (`OverIx.lean:19`; 118 lines in 24 files) | No |
| C2 | It feeds the construction of the final hypothesis bundle, via `plugAll` | Partly: it **is** in the dependency cone of `riemannHypothesis` (kernel-level), but `plugAll` itself is not – its parallel twin `every_character_of_green_v_win` is | No |
| C3 | The geometric witness is built from a model the code itself calls degenerate | True (`geoDegenerate`, `mdlJunk`, … are in the cone) | No |
| C4 | The lattice witness holds its properties by definition | Partly (`nprimeDef := fun _ => rfl`) | No |
| C5 | The height equation holds by `rfl` | True (`h_eq := fun _ => rfl`) | No |
| C6 | Lemmas that would extract content from the geometric witnesses are never called | True, and stronger: `GeoCl.rec` is referenced by no declaration in the cone | No – this is what makes the slot a dead parameter |
| C7 | Hence the release contains no proof of RH | **Does not follow** | – |

Why the inference fails, in two sentences: `riemannHypothesis : RiemannHypothesis` is a closed theorem with no hypotheses whose type is Mathlib's
own constant, so there is nothing for a "vacuously satisfied" premise to attach to, and definitions cannot make new statements provable.
In this particular code the geometry slot `Γ` is write-only along the whole proof path – every lemma that receives it is proved for arbitrary `Γ`,
the final bundle `HypsAlt` does not mention it, and nothing ever eliminates a `GeoCl` proof – so instantiating it with `True` is equivalent to deleting it.

We also looked, independently of the objection, for real ways to cheat a Lean proof (extra axioms, `sorry`, a swapped statement, kernel bypass,
artefact mismatch) and found none.

## What was actually done

* **Provenance.** Downloaded the author's 14-part archive, matched its SHA-256 against the published value, and verified the audited mirror's `src/`
  is byte-identical to it (only the community-added `Challenge.lean` differs).
* **Source reading.** Located every use of `anyGeometry` and traced the chain from `Main.lean`; hygiene scan of all 175,187 files.
* **Kernel-level dependency analysis.** Wrote `conescan` (Rust, no dependencies) and ran it over the published 61.57 GB proof export
  (1,468,418 declarations): exactly 30 declarations depend on `anyGeometry`, including all five headline theorems; the export contains exactly the
  three standard axioms.
* **Independent kernel replay.** Built `con-leche` from source and ran `--verified --compare` on the full export on this machine.
* **Independent statement check.** Rebuilt the Mathlib-only challenge export from official Lean, official Mathlib cache and `lean4export`;
  the result is byte-identical to the published one.
* **Cross-check.** Four independent `agy` agents (Gemini 4 Neon, XHigh) each audited one sub-question.

## Limits

* Nielsen's full paper sits behind a bot check and could not be retrieved; the claims audited are those in its publicly quoted abstract,
  the author's public posts, and a third-party review that quotes it.
* The 175,187-module library was not rebuilt from source here; the link "export ⇐ source" relies on the published sandbox rebuild.
* The mathematics was not read. This is an audit of an argument about validity, not a referee report on the proof.

Details are in section 7 of the report.

## Layout

```
report/      audit_report.pdf and its LaTeX sources, generated excerpts and tables
evidence/    REPRODUCE.md, conescan (source + outputs), con-leche logs, hygiene scan, challenge rebuild,
             provenance log, toy Lean model, agy agent prompts and reports
```

Audit performed on 2026-11-23 by Claude (Anthropic) running in Claude Code, at the request of the repository owner.
