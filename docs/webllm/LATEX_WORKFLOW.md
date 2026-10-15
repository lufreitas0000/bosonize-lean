# Writing unwritten chapters with web agents

Start `make work` for the arrow-key interface. The shared full guide is
`/home/lucas/Projects/orchestrator/docs/LATEX_BROWSER_WORKFLOW.md`.
For the original typed menu use `make work PLAIN=1`.

Current priority: CH19 has no LaTeX draft. CH01–11 are published drafts and will
be revised later through Jules. CH12–18 have private local drafts to preserve
for later review/integration. This sprint does not rewrite those chapters.

The [section inventory](../../notes/latex/plan/sections.json) maps 21 chapter
notes and their current writing/formal status. It is not a completed reference
coverage ledger. The [writing policy](../../notes/latex/plan/WRITING_POLICY.md)
contains scope, pedagogy, notation and context selection requirements.

## CH19 queue

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
