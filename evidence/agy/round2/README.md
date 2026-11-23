# Second-round cross-check agents (E–H)

Four read-only agents were run with `agy --model gemini-4-neon-xhigh` (Google Gemini 4 Neon, highest reasoning
setting) on the full text of the paper under review. Each started from an empty context and received one prompt
(`prompts/`), the source tree, a declaration index and the extracted text of the paper. None saw the main analysis.

| File | Sub-question |
|---|---|
| `E_sections_2_3_4.md` | fact-check of Sections 2–4 of the paper |
| `F_sections_5_6.md` | fact-check of Sections 5–6, and what lies on the live route |
| `G_height_and_squeeze.md` | the height, `WordFacts`, `divClausesR_of`, `DivInputsR` (Sections 7–8) |
| `H_logic_review.md` | independent review of the paper's argument (Abstract, Sections 8–10, Appendix A) |

The reports are published as the agents wrote them, with three kinds of edit:

* verbatim quotations from the paper under review were replaced by `[quotation from the paper omitted]`
  (the line references `paper.txt:N` are kept, so each passage can be located in the paper itself);
* gendered pronouns referring to the paper's author were replaced by neutral wording;
* absolute paths on the audit machine were shortened to `~/…`.

`paper.txt` is the text of the paper extracted with `pdftotext -layout`; it is not redistributed here.
Agent H was given four facts as premises (closed theorem of Mathlib's statement, three standard axioms, independent
kernel replays, flagged objects in the dependency cone). The paper itself concedes the first two; the others are
established in the audit.
