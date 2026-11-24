# The minimal example of 24 November 2026

On 24 November 2026 J. L. Nielsen posted a Lean file of about forty lines
(<https://x.com/QualiaQuanta/status/2125008805310222352>), described as a minimal example with no `sorry` and no
custom axioms, and presented it as showing how the release compiles. This directory holds the checks reported in
the addendum of the paper.

**Result.** The theorem of the example takes the Riemann Hypothesis as a hypothesis and hands it back:

```lean
theorem claimed_rh (hRH : RiemannHypothesis) : (∃ b : Bundle, …) ∧ RiemannHypothesis   -- the example
theorem riemannHypothesis : RiemannHypothesis := rhOfAll                               -- the release, Main.lean
```

The theorem of the release has no hypothesis, in the source and in the kernel export. The example is therefore
not a model of the release, and with the hypothesis removed it does not compile.

| File | What it is |
|---|---|
| `NielsenMinimal.lean`, `.out` | the example as posted, indentation restored (the post shows it flush left); compiler output |
| `NielsenMinimal_checked.lean`, `.out` | the example followed by four checks: its type; its proof term; the same text with an arbitrary proposition and with `False`; an attempt to use it without the hypothesis (fails, as it must) |
| `LastSteps.lean`, `.out` | the last two steps of the release that conclude `RiemannHypothesis` (`rh_of_right`, `rh_of_every`), copied verbatim; they need only Mathlib and compile on their own. Without a proof of `UpperTheory.EveryCharacter` they yield nothing (last line, fails as it must) |
| `export_records.txt` | the records of `riemannHypothesis` in the 61.57 GB proof export and in the challenge export: its type is the bare constant `RiemannHypothesis` |
| `rh_referrers.py`, `.out` | query on the kernel-level dependency graph: of 1,468,418 declarations, four refer to `RiemannHypothesis` in their type, all four as the conclusion |

To reproduce the compiler outputs, run `lake env lean FILE` inside a project that has Mathlib at tag `v4.33.1`
built (for instance the project of `../REPRODUCE.md`, section 5). An `.out` file ending in `exit code: 1`
records an error that the file is written to produce.

Independent verification by six Gemini 4 Neon agents: `../agy/round3/`.
