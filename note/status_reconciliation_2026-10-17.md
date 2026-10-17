# Version 1 status reconciliation — 2026-10-17

Scope: documentation, current machine-readable manuscript status, project
principles, theory-discussion prompts and accepted-history consolidation. No new
Lean theorem, definition, dependency or lock baseline is introduced. The user
explicitly paused implementation until the theoretical strategy is clear.

## Established baseline

- Input revision: `40dea8bfbdc849417c072e490480d4f72536116a`, two manuscript
  commits ahead of then-main `0d185dfbadd6b8efe1eba752d2520873b35cdc0a`.
- CH19/A08: Phase C complete, 62 original contracts. Finite CH20: Phase C
  complete, 64 original contracts. Their independent reviews and axiom receipts
  remain in the original acceptance reports; those reports are historical evidence.
- 34 frozen Core files, 1,079 theorem/lemma declarations and 1,093 frozen
  commands. CH21 has a current R&D proposal but no accepted Lean interface;
  its historical 47-contract count is not the current specification.
- The master includes CH01–21. CH19 uses its complete replacement; old 19.x
  sources are superseded provenance. CH20–21 use seven numbered section files.
  Appendix files A04–A10 are included, with A01–A03 topics in the narrative.

## Reconciliation coverage

Current status prose was searched across the README, roadmap, note/appendix
indexes, source-coverage plan, editorial scope and coordinator documents,
workflow guides, manuscript manifests, local rules/skills and workspace
README/cockpit/agent/operator guides. Current instructions were corrected.
Dated reviews and initial workflow examples retain their source-bound meaning;
supersession notices prevent them from being read as current phase status.
Acceptance receipts, source hashes and original import/download hashes were
not rewritten as new evidence.

The import manifest incorrectly kept seven already included CH20–21 sections
under `pending_master_sections`. They are now active `sections` entries, so the
existing publication checker actually checks their reachability and labels.
The CH19 superseded-source list and import hashes are preserved. No TeX body
was changed by this status reconciliation.

The shared authority files and their Bosonize copies now follow the current
user scope instead of the old infrastructure-only/CH19-unpromoted snapshot.
The workspace synchronizer propagated the updated allocation rules and
active-focus skill. Unrelated resource-routing and finiteQMB implementation
edits were excluded from this task's commits.

## Scientific and version decisions

Parameterized structural proofs, explicit hypotheses and regulator residuals
are stated in the README, strategy, project-specific principles and workspace
principles. Finite examples remain valuable witnesses and falsification tools.
Finite CAR, uncompressed polynomial CCR, formal series, state existence and
analytic limits remain distinct.

CH20b is the working name of the open Chapter 20 completion bridge; it is not
another numbered book chapter. The finite CH20 package is accepted, while the
broader research program needs reviewed constructions, obstructions and explicit
scope decisions. Six self-contained theoretical prompts and the source hash
manifest are in `docs/plans/ch20-theory/`. These are not executable proof packets.
The user's private finite-AQFT critique is retained as a research agenda and was
not copied into the public repository or modified.

Version 1 is standalone. Close the agreed CH20 scope, finite CH21 through its
reviewed A–B–C cycle, then the coverage/release audits. Version 2 is a future
complete refactor built on finiteQMB; it creates no dependency or migration
obligation in the current implementation.

## Validation

- Strict interface guard passed: 1,079 statements / 1,093 frozen commands.
- Core guard passed: 34 complete files. The change has no Lean or lock diff.
- Publication-source checker passed with CH19 replacement and all seven
  CH20–21 sections active in its checked manifest.
- Both existing publication-source regression tests passed.
- Documentation link, JSON, prompt-baseline and source-hash checks passed;
  `git diff --check` passed.
- No new mathematical acceptance or whole-project axiom audit is claimed.
  GitHub publication status must be checked against the final main commit;
  a prior branch build is not evidence for a later release.

Only accepted manuscript commits and these documentation/planning changes belong
in the canonical main line. Independent unfinished research branches and their
worktrees remain preserved; their existence does not mean their results have
been accepted into main.
