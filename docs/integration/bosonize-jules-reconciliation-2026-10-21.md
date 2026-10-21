# Bosonize Jules reconciliation — 2026-10-21

The canonical branch is `main`. Source `1bdd21f49fbdc977c597a99c3cb3d7ab038129d6` was backed up by a normal fast-forward push from remote `083df9dbd7148a5c71ef09cce5a46558825a3907`. This publishes existing accepted and staged source as a backup; it does not promote S6, accept the old editorial wave, or claim the S6 h3 placeholder solved. No manuscript, Lean source, or lock was edited in this reconciliation.

## Completed source checks

Sandboxed `make lock-check` and full `make ci` passed at `1bdd21f`: 1317 statements, 1394 frozen commands, 43 complete Core source files, both Core/staging builds, guard and WebLLM tests. Staging permits explicitly recorded placeholders. Exact baseline hashes of 870 existing tracked and untracked files remained unchanged before publication; eight existing tracked edits and existing untracked governance/strategy material were preserved. Private logs, source chronology, provider receipts and recovery bundles are under `build/branch-reconciliation-2026-10-21/`.

The entire `notes/latex/` tree is byte-identical between remote baseline `083df9d` and `1bdd21f`. S3–S5 pedagogical additions are Markdown notes, not LaTeX. Consequently existing Jules reviewers can inspect exact current LaTeX on the available remote source. The push does not trigger the LaTeX-only workflow because it changes no LaTeX source; this document does not claim a new GitHub PDF release.

## Historical proof jobs

All 46 historical CH18/A08 Jules proof jobs have exact named declarations in complete frozen Core. The linked machine-readable disposition ledger supplies session IDs and current source anchors. These jobs are `superseded-by-promoted-Core`; their old staging patches must not be replayed. Provider completion or feedback state remains historical provenance, not a new acceptance gate. Three unoccupied theorem-fragment branches were retired after creating and verifying `superseded-theorem-fragments.bundle`; their original heads and recovery location are recorded in the retirement ledger. Occupied worktrees were preserved.

## Independent API audit

The archived API report is an independent report-only audit, not mathematical certification. Initial `api-pro` (`gpt-5.4-2026-03-05`) exhausted a bounded 12000 output tokens entirely in reasoning and returned incomplete, with no deliverable. A second admitted complimentary `api-fast` call returned the mechanically verified report candidate `b0f6e3572cbd373acc904b6d4799bc510947727a`. Its qualified verdict supports backup while rejecting promotion claims. It correctly warns that hash differences alone do not justify superseding every old editorial change. Its suggested CH20/CH21 prose concerns remain hypotheses for source-anchored Jules inspection, not automatically accepted fixes. No paid fallback or new author session was used.

## Editorial wave — current acceptance boundary

The old combined candidate `25f2955e4596a086137a9054b81a868444e3bbbf` was based on `4e2806009c9f7f72d670b1c1ad55afe8a564b53f`. Later main rewrites at `753d6d8` extensively changed CH01–11 and appended chapters/appendices. Current CH19 uses a unified chapter, superseding inclusion of old 19.1–19.4 sections. Other section bodies and frontmatter evolved. Whole-file restoration from the old candidate would regress later source and is rejected. Individual useful prose corrections still require current-source review.

The existing CH21 author returned corrected candidate `afa7cc3465d8be234a44a4bd5e08b7941e6d316e`, mechanically verified on its original base and not accepted into main. Revised old currents report `5d14b8a46c4aa929166a2f9443b2741feb07783f` was recovered. The foundations session was completed without a patch and retained as delivery-blocked until a same-session continuation was requested.

Three existing review sessions now perform bounded report-only supersession/salvage audits: foundations `17460451979780987732` (CH01–05), currents `462576978194251941` (CH06–11), interactions `17985480106567166240` (CH19–21/frontmatter). Contracts name exact old/current sources, report-only allowlists, integration ownership, verification and cleanup criteria. Final dispositions and any narrow source repair depend on actual fresh patch delivery and final-hash inspection. Old provider reports are not silently reused as reviews of current sources.
