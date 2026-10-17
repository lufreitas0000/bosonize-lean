# Writing unwritten chapters with web agents

Start `make work` for the arrow-key interface. The shared full guide is
`/home/lucas/Projects/orchestrator/docs/LATEX_BROWSER_WORKFLOW.md`.
For the original typed menu use `make work PLAIN=1`.

Current manuscript (2026-10-17): the master includes CH01–21. CH19 is a complete replacement chapter; its four earlier numbered files are superseded and retained as provenance. CH20–21 use included numbered section sources (`20.1.tex`–`21.4.tex`). Independent review is tracked separately from compilation. CI verifies the active input graph; CI verifies that input graph and binds its publication receipt to the compiled PDF hash. Original downloads remain private; [import provenance](../../notes/latex/plan/imported_sections.json) records hashes and mappings.

The [Jules second-round plan](JULES_REVISION_PLAN.md) is a historical plan. It does not report the later rewrite wave or authorize a new dispatch; consult the editorial receipts and current roadmap.

Historical writing priority (superseded by the current master): CH19 had no LaTeX draft. CH01–11 are published drafts and will
be revised later through Jules. CH12–18 have private local drafts to preserve
for later review/integration. This sprint does not rewrite those chapters.

The [section inventory](../../notes/latex/plan/sections.json) maps 21 chapter
notes and their current writing/formal status. It is not a completed reference
coverage ledger. The [writing policy](../../notes/latex/plan/WRITING_POLICY.md)
contains scope, pedagogy, notation and context selection requirements.

## CH19 acceptance specifications (for future revisions)

1. `packets/book_ch19_scope.toml`
2. `packets/book_ch19_mode_correlators.toml`
3. `packets/book_ch19_spatial_correlators.toml`
4. `packets/book_ch19_finite_comparison.toml`

Each produces ONE section file. Prepare the next only after integrating previous
sections; their committed sources are mandatory context in the next packet.

```bash
make work-start SPEC=packets/book_ch19_scope.toml
make work
```

Select the task, copy/attach its packet, and ask the web agent to edit only the
body of its supplied standalone template. Discuss revisions directly in that
chat. Return one complete `.tex` download; no author JSON/ZIP. The web compiler,
when available, checks the standalone source. Cross-chapter references display
`book` in the preview; the actual whole-book build resolves real references.

After downloading, separately select **Detect/select download**, inspect its
full path and format, inspect the diff, then **Verify**. The body is extracted
without guessing boundaries; changed wrappers, stale identities and invalid
syntax are rejected. Accepted sections are conditionally included by the real
master; no placeholder CH19 chapter is published before its first section exists.
Logs/PDFs are retained privately in the candidate worktree's `.book-artifacts/`.

Failed verification generates `retry.md`; send it and the original standalone
template back to the author. A successful candidate gets an independent review
packet. Check the downloaded review, inspect the diff and explicitly approve
local integration. Generic document finish does not push. Push accepted work
when it should be published; CI updates the PDF linked in README and its
`book-build.json` source-revision receipt.

The interface displays saved tasks, history, attempt limits, candidate commits,
errors and stale baselines. It offers copy prompt/open folder, but no provider
calls. Optional Jules/API dispatch remains an explicit budgeted CLI operation.


## Direct manuscript import of October 15

The user explicitly requested organizing, compiling, committing and publishing
all eleven supplied downloads without first operating the per-section review
menu. This is recorded as a user-requested **manuscript draft import**. It does
not itself establish independent PASS review or Lean acceptance. Subsequent CH19/A08 and finite CH20 Phase C acceptance has separate receipts; CH21 remains unimplemented.
The older single-section candidate remains in history and is superseded by this
batch's numeric source mapping; its original branch is preserved.

Numbers 19.1–19.4, 20.1–20.3 and 21.1–21.4 identify files and TUI entries.
Descriptive section headings and stable semantic LaTeX labels remain in the book.
Only the body between the trusted standalone markers was imported. A missing
final newline in the 19.4 wrapper was normalized explicitly; no mathematical
text was changed during import. The build contains all eleven bodies and checks
undefined citations/references and duplicate labels. Compilation does not replace
the planned mathematical/editorial review.
