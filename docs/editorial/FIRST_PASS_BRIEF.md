# First Jules editorial pass: bounded review, not a rewrite

## Deliverable

Read the published source listed in source_inventory.json and create only
`docs/editorial/first_review.md`. The goal is a coherent, modest, pedagogical book
rederiving the literature with clear finite-model assumptions and limitations.
Read STYLE_AND_SCOPE.md first. Use the repository source, not claims from a chat.
The publisher verified the previous manuscript at commit f6766b1, but that is not
mathematical/editorial approval. The new review packet adds only editorial setup.

One session should produce an actionable overall review. Do not start chapter
rewrites or create a PR, response JSON, PDFs, scripts, extra reports or environment
files. Do not install dependencies, compile Lean, run Lake, or spend time setting
up a TeX compiler: this task changes no LaTeX. No agent/provider calls from inside
the task. Read-only inspection and running the supplied report verifier are enough.
The result will pass local whitelist/provenance checks and be inspected by the
supervising agent; it is not an automatic mathematical PASS verdict.

## Initial observations to verify, not a predetermined verdict

Locate the current lines and check the context before accepting these concerns:

1. Main preface: "complete, self-contained" and "heuristics often obscure" can
   overstate completeness and unfairly characterize the source literature.
2. CH01: "exact finite dimensionality is strictly required" is too broad if it
   means Lean or Fourier theory generally; identify the actual modelling choice.
   The half-open Brillouin interval should not be called the unique possible
   convention without stating the extra convention that selects it.
3. CH01: assertions that other authors ignore Nyquist subtleties need specific
   evidence or neutral replacement. "With zero error" must identify the exact
   protected-subspace identity, not suggest an unrestricted continuum equivalence.
4. CH03: "eliminates divergences without needing arbitrary momentum cutoffs"
   needs a fixed-model interpretation and must not imply all continuum problems
   have disappeared.
5. CH08 introduction: inspect "circumvent all topological subtleties", Hilbert
   adjoint terminology for the polynomial pairing, and blanket termination claims
   for vertex/Weyl exponentials. Distinguish actual lowering-map nilpotency from
   stronger statements that require further hypotheses.
6. Global notation: compare cyclic/wrapped versus nonwrapping current definitions
   and the sign/order of CCR with the actual CH09/CH10 and CH19 assumptions. Do not
   propagate a likely frontmatter error into all chapters for consistency alone.
7. Spatial fermion names differ between the global notation page and later
   multi-species sections. Record contexts and propose a ledger rather than a
   blind replacement. Also check lattice length, physical length, mode cutoff,
   charge, energy budget, g, g_U and finite/abstract expectation notation.
8. The published master jumps from CH11 to CH19 after an outlook. Explain what
   readers lack without CH12–18; separate a temporary editorial bridge from the
   future integration of private drafts. Do not claim you reviewed unavailable text.
9. Miranda and Senechal are intended source authors, but may be absent from the
   current bibliography. Check what is actually cited; flag missing attribution
   without inventing bibliographic details, page numbers or literature claims.

## Report structure

Use exactly these level-two headings, in order:

- Executive assessment
- Prioritized findings
- Notation ledger
- Chapter connections
- Tone examples
- Revision queue
- Coverage and limits

Within Prioritized findings give 12–30 findings, each headed `### ED-01: ...`
with unique IDs. Each finding must contain at least one source line in this form:
`Source: notes/latex/main.tex:23-25`
Use an actual repository-relative path and valid line range at the packet baseline.
Include priority P1/P2/P3, category, the concrete problem, an explanatory or proposed
wording change, and whether it is editorially clear or needs a mathematical/source
check. Add at most one short quote where it helps. Do not present an uncertain
mathematical diagnosis as an established correction. Prefer high-impact findings
with a concrete remedy over an exhaustive list of repeated adjectives.

Notation ledger: a table with symbol, meaning/carrier, source locations, conflict,
proposed convention and unresolved decision. Separate neutral notation aliases
from changes that affect a theorem's mathematical content.

Chapter connections: cover published CH01–11 and CH19–21; give missing prerequisites,
where material repeats, and proposed opening/closing bridges. Identify the CH12–18
gap explicitly. Appendix ownership should avoid concurrent shared-file edits.

Tone examples: supply three short proposed replacements (preface, a chapter opening,
a limitations/transition paragraph). Follow the user's modest pedagogical tone;
do not rewrite a whole chapter here.

Revision queue: recommend the first CH01–03 pilot and CH07–08 pair; keep dense
chapters separate with relevant appendix context. Give concrete acceptance checks
and a cost-efficient order. One session per batch; corrections stay in that session;
use deterministic verification for routine compiler feedback; no Antigravity review.

Coverage and limits: include a table with rows `| CH01 | ... |` through CH11,
and CH19, CH20, CH21. State which published files/appendices you actually inspected,
which mathematical/literature claims require further checking, and what was not
reviewed. Do not assert full source coverage or proof verification. Keep the
entire report under 6,000 words and anchored in the actual source inventory.
