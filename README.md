# The Invalidity of "The Invalidity of Alpöge's Proof of the Riemann Hypothesis"

A kernel-level audit of the vacuous-witness objection to the Lean formalization.

**Zijian Zeng** — Institute of Computer Science and Digital Innovation, UCSI University, Kuala Lumpur, 56000, Malaysia
(<zijianzeng@foxmail.com>; <1002266693@ucsiuniversity.edu.my>)

**Paper (PDF): [`paper/invalidity_of_the_invalidity.pdf`](paper/invalidity_of_the_invalidity.pdf)** · audit date 23 November 2026 · addendum 24 November 2026

---

On 20 November 2026 Levent Alpöge released a Lean 4 development claimed to prove the Riemann Hypothesis.
J. L. Nielsen's paper *The Invalidity of Alpöge's Proof of the Riemann Hypothesis* argues that the release contains
no proof, because on the route to the final theorem a geometry predicate is the constant `True`, the geometric
witness is a degenerate model, lattice identifications hold by `rfl`, and a height is installed by assignment.

This repository audits **that argument**. It does not try to prove or disprove the Riemann Hypothesis, and it is not
a review of the mathematics of the release.

## Result

| Question | Answer |
|---|---|
| Are Nielsen's observations about the code true? | **Largely yes.** Confirmed in the source and at the level of the kernel export. A few citations are inaccurate, and two headline descriptions are false as statements about the code. |
| Does the conclusion "the release contains no proof of RH" follow? | **No.** |

Why the conclusion does not follow:

1. **What is certified is not a tautology.** The kernel certifies a closed term of type Mathlib's `RiemannHypothesis`
   using only `propext`, `Quot.sound`, `Classical.choice`. Its statement depends on 4,566 declarations, all in Mathlib
   and none in the release. It is not an equation `X = X`, and auxiliary definitions cannot change what it says.
2. **The squeeze is not proved by reflexivity.** The two inequalities are proved by `divClausesR_of` from 38
   hypotheses (operator-norm, valuation and covolume bounds). Its dependency cone holds 1,004 theorems of the release
   and none of the flagged objects. Section 7 of Nielsen's paper says the same; its Abstract and Section 8 contradict it.
3. **Deleting an input is not a test of soundness; replacing it is.** The consumers on the route are stated for
   arbitrary inputs (`∀ Γ : GeoP`, `∀ V NR : Prop`), and the bundle handed to the final step is a proposition whose
   type does not mention the geometry predicate.
4. **The numbers.** Of 1,468,418 declarations in the proof export, 30 depend on `anyGeometry` and 124 on any of the
   objects flagged as vacuous. The hypothesis bundle said to be hollow is established using 636,383 theorems of the
   release, and the final algebraic step (`every_character_of_green_v_win`) depends on none of the flagged objects.

What Nielsen's paper **does** establish: the formal proof does not use the geometric interpretation that its
identifiers and directory names advertise. That is a finding about exposition, and a useful one; it is not a finding
about validity.

Independently of the objection, we looked for the ways a kernel-checked theorem can still be wrong (extra axioms, a
substituted statement, an exploited kernel defect, a mismatch between source and checked artefact) and found none.

## Addendum (24 November 2026): the minimal example

On 24 November 2026 Nielsen posted a Lean file of about forty lines, described as a minimal example with no `sorry`
and no custom axioms, as showing how the release compiles. Section 11 of the paper examines it.

**The example does not model the release.** Its theorem assumes the Riemann Hypothesis and hands it back; the
theorem of the release has no hypothesis.

```lean
theorem claimed_rh (hRH : RiemannHypothesis) : (∃ b : Bundle, …) ∧ RiemannHypothesis   -- the example
theorem riemannHypothesis : RiemannHypothesis := rhOfAll                               -- the release
```

* The type of `claimed_rh` is `RiemannHypothesis → (…) ∧ RiemannHypothesis`. The same text compiles with `False`
  in place of `RiemannHypothesis`. With the hypothesis left out it does not compile, and six further attempts to
  do without it also fail.
* In the 61.57 GB proof export the type of `riemannHypothesis` is the bare constant `RiemannHypothesis`. A
  hypothesis would be recorded as a `forallE`, as it is for the lemma one step below.
* Of the 1,468,418 declarations in the export, four refer to `RiemannHypothesis` in their type, each as its
  conclusion. In the source, none of the 51 occurrences of the identifier is a hypothesis.
* The last two steps of the release that conclude `RiemannHypothesis` use only Mathlib and compile on their own.
  The hypothesis they need is supplied by a theorem that has none; in the example nobody supplies `hRH`.
* What the example does show: a vacuous certificate adds no evidence, and a clean `#print axioms` report does not
  tell you what a theorem states. One has to read the statement, which is what the statement comparison checks.

Files: `evidence/minimal-example/`. Six further Gemini agents verified this independently: `evidence/agy/round3/`.

## How it was checked

* **Provenance.** SHA-256 of the author's archive and of both published exports recomputed and matched; mirror
  `src/` identical to the archive.
* **Kernel-level dependency graph.** `depgraph` (Rust, written for this audit) extracts the complete
  declaration-level dependency graph of the 61.57 GB proof export: 1,468,418 declarations, 156 million edges, with
  statement dependencies and proof dependencies kept apart. `depquery.py` answers reachability questions on it.
* **Independent kernel replay.** `con-leche --verified --compare` on the complete export: exit code 0, all
  1,468,418 declarations accepted, all five theorems "justified by the solution".
* **Independent statement check.** The Mathlib-only statement export rebuilt from official Lean and the official
  Mathlib cache; byte-identical to the published one.
* **Two toy Lean files** reproducing the patterns at issue (`evidence/toy/`).

## Independent verification by Gemini 4 Neon

A second, independent line of verification was run with **Google Gemini 4 Neon (XHigh)** through the `agy` CLI:
eight read-only agents, each from an empty context, each on one sub-question, none shown the main analysis.
Several findings in the paper originated with these agents:

* the location of the degenerate and junk models, which a public review had searched for and not found (agent C);
* that the custom tactics `kexactB` / `kcopy` make an independent kernel replay necessary (agent D);
* that the "copied" lattices are substantive objects with proved lemmas (agent E);
* that the row-side condition `InGeo` is established by substantive proofs, and that the structure carrying the
  vacuous field `degHH_def` is never constructed (agent F);
* two mis-cited sites in Nielsen's paper, and that the pairing `Bk` is tied to the period pairing by a proved
  statement (agent G);
* an independent 13-step reconstruction and assessment of the argument, and the minimal counterexample to the
  "remove the package" test (agent H).

All eight reached the same overall assessment as the main analysis. Prompts and full reports: `evidence/agy/`.

For the addendum, six more agents (I–O) were run in the same way, this time able to compile small Lean files.
What originated with them:

* a correction to the main analysis, whose draft contained a vacuous check (an equation between two proofs of a
  proposition, true by proof irrelevance), and the observation that the three axioms reported for the example
  come from its statement, not from its proof (agent I);
* a classification of all 51 occurrences of `RiemannHypothesis` in the source, and the seven lemma hypotheses of
  that shape on the route with the theorem that discharges each (agent J);
* six failed attempts to remove the hypothesis of the example, and the converse experiment: the same vacuous
  bundle passed to a lemma stated for all bundles yields a valid theorem (agent K);
* the strongest point in favour of the example, recorded in the paper (agent L);
* the common prefix of the two kernel exports and a full pass over the 61.57 GB file for axiom records (agent M);
* an independent compilation of the last steps and a walk along the route (agent O).

All six reached the same assessment. We recompiled their 23 test files and obtained the outcomes they report.

## Limits

* The mathematics was not read. This is an audit of an argument about validity.
* The trust base remains: Lean's logic, at least one correct checker, `lean4export`, and the adequacy of Mathlib's
  definitions. Nielsen's paper does not question any of these.
* The build from the 175,187 source files to the export was not reproduced here; the export itself was checked directly.
* A dependency graph is syntactic, and counting theorems measures extent, not depth.

## Layout

```
paper/       the paper (PDF and LaTeX), generated excerpts and tables, make_excerpts.py, make_tables.py
evidence/    REPRODUCE.md
  conescan/      Rust sources: src/bin/depgraph.rs (graph extractor), src/main.rs (earlier single-pass analyser)
  depgraph/      depquery.py, watch list, query outputs, hashes of the graph files
  con-leche/     logs of the independent checker run
  challenge-rebuild/, provenance/, hygiene/, toy/
  minimal-example/   the example of 24 November 2026: compiled files, export records, graph query
  agy/           prompts and reports of the fourteen Gemini agents (round 1: A–D, round 2: E–H, round 3: I–O)
```

## Versions

* **v2.1** (24 November 2026): adds the addendum on the minimal example (Section 11 of the paper), the files in
  `evidence/minimal-example/` and the third round of agents.
* **v2** (the paper, English): based on the full text of Nielsen's paper; adds the dependency graph, the second
  round of agents and a correction of an undercount in v1 (Appendix B of the paper).
* **v1** (a report in Chinese, merged as PR #1): superseded; available in the git history.

## Contributions

The author posed the question, directed the work and is responsible for the conclusions. Claude Code (Anthropic)
carried out the main analysis and drafted the text under the author's direction. Gemini 4 Neon (Google), through
`agy`, performed the independent verification. Neither AI system is an author.

## 中文摘要

本仓库审计的是一个**论证**，而不是黎曼猜想本身：J. L. Nielsen 的论文认为 Alpöge 发布的 Lean 证明“不包含黎曼猜想的证明”，
理由是几何谓词被定义为 `True`、几何见证是退化模型、格等式由 `rfl` 成立、高度是赋值得到的公式。

结论：**这些代码观察基本属实，但推不出“证明无效”。**

1. 内核认证的是 Mathlib 的 `RiemannHypothesis` 的闭项，只用三条标准公理；其陈述依赖的 4,566 个声明全部来自 Mathlib，不是“同义反复”。
2. 核心的两条不等式不是由自反性成立，而是由 `divClausesR_of` 从 38 条假设证明的；其依赖锥含 1,004 个本库定理，不含任何被点名的对象。
3. “删掉输入后无路可走”不是可靠性检验；应当检验“换一个输入是否仍成立”，而路径上的消费者都是对任意输入陈述的。
4. 1,468,418 个声明中只有 30 个依赖 `anyGeometry`、124 个依赖任何被点名的对象；被称为“空洞”的假设包由 636,383 个定理支撑。

Nielsen 论文真正说明的是：形式化证明没有使用其标识符所宣称的几何解释。这是关于表述的发现，不是关于有效性的发现。

**补遗（2026 年 11 月 24 日）：** Nielsen 又发布了一段约四十行的 Lean“最小示例”，称发布版就是这样编译通过的。
核验结论：**该示例不是发布版的模型。** 示例的定理把黎曼猜想作为假设（`hRH : RiemannHypothesis`）再原样交回；
发布版的主定理没有任何假设，在 61.57 GB 的内核导出文件中其类型就是裸常量 `RiemannHypothesis`。
去掉假设后示例无法编译；导出的 1,468,418 个声明中只有 4 个在类型里提到 `RiemannHypothesis`，且全部是作为结论。详见论文第 11 节。

独立验证由 Google Gemini 4 Neon（XHigh，经 `agy`）的十四个只读代理完成（主体审计八个，补遗六个），论文中多处发现最先出自这些代理（见上文及论文第 7 节、第 11.7 节）。
论文正文为英文：[`paper/invalidity_of_the_invalidity.pdf`](paper/invalidity_of_the_invalidity.pdf)。
