# Third-round cross-check agents (I–O): the minimal example of 24 November 2026

Six read-only agents were run with `agy --model gemini-4-neon-xhigh` (Google Gemini 4 Neon, highest reasoning
setting) on the Lean example that J. L. Nielsen posted on 24 November 2026 and on the claim that it shows how the
release compiles. Each started from an empty context and received one prompt (`prompts/`). None saw the main
analysis, and each was told not to read the earlier reports of this repository or the directories of the other agents.
(There is no agent N: the letter is used in the paper for the work under review.)

| File | Sub-question |
|---|---|
| `I_example_semantics.md` | what the posted example states and proves |
| `J_trace_main_theorem.md` | is the Riemann Hypothesis, or an equivalent, assumed anywhere on the route to the final theorem? |
| `K_faithful_model.md` | which features of the release the example models; attempts to remove its hypothesis; the converse experiment |
| `L_logic_and_tests.md` | under which conditions the inference from the example would be valid; mechanical tests; verdict |
| `M_kernel_export.md` | the statement of `riemannHypothesis` in the two kernel exports; axiom records |
| `O_last_steps.md` | what produces the conclusion in the release: the last steps and the route behind them |

Unlike the agents of the first two rounds, these could compile small Lean files: `leanc.sh` runs Lean 4.33.1
with the official Mathlib build on the search path and writes nothing (it is equivalent to `lake env lean FILE`
inside the project of `../../REPRODUCE.md`, section 5). They could not build the release.
Their test files are in `work/`; `work/RECHECK.txt` records the exit codes we obtained when we recompiled all of them.

All six reached the same assessment as the main analysis: the example compiles because its theorem takes
`RiemannHypothesis` as a hypothesis, the theorem of the release has no hypothesis, and so the example is not a
model of the release. Agent I also caught a vacuous check in our own draft (an equation between two proofs of a
proposition, which holds by proof irrelevance whatever the proofs are).

The reports are published as the agents wrote them, with two kinds of edit:

* two verbatim quotations from the paper under review, in the report of agent K, were replaced by
  `[quotation from the paper omitted]` (the line references `paper.txt:N` are kept);
* absolute paths on the audit machine were shortened to `~/…`.

`paper.txt` is the text of the paper extracted with `pdftotext -layout`; it is not redistributed here.
The prompts state the claim under review in neutral terms and quote two short phrases of the post.
