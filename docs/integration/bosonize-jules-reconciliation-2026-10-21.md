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

A fresh currents supersession report was rejected during coordinator inspection: it asserted old candidate quotes were present in current `083df9d`, but actual `git show`/source searches contradicted those claims (CH10 still contains the original “central mathematical miracle” and “heuristic point-splitting” prose). This is a candidate/current-source confusion error. A bounded same-session revision requires explicit `git show` against the exact current SHA for every anchor. The rejected PASS is not evidence of supersession or acceptance; useful old prose corrections remain to be reconciled. The interactions session was provider-completed but still returned only its old report artifact at the first resumed collection, so no fresh current-source verdict has been accepted there.

## Current-source author batch

The user authorized additional Jules author work after useful old corrections were shown to remain. Three new disjoint tasks start from exact source `53ed5d4ea9a1c896cc693023a3f0c3e7f6cbe33a`, with prep-only contract/preservation commit `0c9c415a773fdc557c21bebbda06621e68ea1535` on temporary branch `codex/editorial-reconcile-20261021`:

| Group | Jules session | Scope |
| --- | --- | --- |
| Foundations | `12276826698917617142` | CH01–05 prose plus one findings report |
| Currents | `13434554062593087675` | CH06–11 prose plus one findings report |
| Interactions/frontmatter | `12204557691925919848` | Unified CH19, CH20/21 wrappers and active sections, main frontmatter prose plus one findings report |

This is narrow reconciliation of useful old corrections onto current sources, not restoration of old snapshots or unrelated chapter rewriting. Twenty-two source paths are disjoint. Current display/proof/theorem/definition blocks, 4072 inline math snippets, and label/citation/include command sequences are locked exactly and in order. Appendices, CH12–18, notation, bibliography, all Lean/Core/locks/CI and accepted newer pedagogy remain read-only. Each task allows one session and at most two focused same-session revisions. Independent final-candidate API review and fresh combined-book validation remain required.

The isolated prep checkout passed the current preservation check, exact inline lock, project source/include checker and sandboxed real-book compilation before dispatch. Disposable sandboxed mutations verified that changing an existing inline formula fails and changing ordinary prose passes; the source was restored. Prep-only wrappers and baseline files are not integration deliverables.

The shared document CLI has a pre-existing dotted-input graph issue: `Path('21.4').suffix` is `.4`, so it fails to append `.tex` before reading the active section. This reconciliation does not repair the hub. Instead, the isolated prep runner calls the same existing `verify_document.build_book` implementation directly, while the current project `scripts/check_book_sources.py` supplies the include-graph check for numeric sections. Both checks passed. This preserves the actual no-shell-escape compilation/log/reference gates without treating a CLI path-parsing failure as a manuscript defect.
