# Native LaTeX and terminal workflow sprint

Date: 2026-10-15. User refinement: write unwritten chapters first; reserve
rewrites of existing chapters for later Jules tasks. No Lean proof work and no
live model-generation call were started.

## Delivered scope

- One native standalone `.tex` per response; committed preamble/bibliography,
  source-bound wrapper, exact body markers, deterministic extraction and internal
  serialization. Full original download and verification responses are archived.
- Separate download detection, format reporting, selection/archive, diff preview
  and sandboxed verification. Malformed matching JSON is visible, rather than
  silently treated as absent. Preview does not spend a verification attempt.
- Arrow-key/Enter terminal interface with copy prompt, open folder, download
  selection, diff, local verification, independent review, errors and attempt/
  checkpoint history. Old typed menu and CLI remain available.
- CH19 writing queue: scope, mode contractions, spatial kernels, finite-Fock
  comparison. Later tasks require integrated predecessors as context. Shared
  notation/scope policy and a 21-chapter navigational inventory are supplied.
  Source-coverage and global notation reconciliation remain separate reviews.
- Existing CH01–18 text preserved; no private CH12–18 draft was published.
  Master conditionally includes new CH19 section files when accepted. Actual
  whole-book compilation checks inclusion/references/citations/duplicate labels.
- Historical CH17 B/C checkpoint histories merged with current main authoritative;
  no frozen Lean/lock changes. GitHub branch consolidation follows preservation.
- PDF workflow adds strict log checks, a source revision stamp, PDF/log artifacts
  and release provenance JSON. Refresh requires a successful fresh CI run.

## Validation checkpoint

134 orchestration tests passed (including native response preview/review/
integration, wrapper protection and malformed-download recovery). Shared pipeline
suite passed 168 tests; three additional terminal-navigation tests passed. Local
actual-book compilation passed with 110 pages before any new CH19 text exists.
Standalone and sandboxed candidate-book smoke evidence is retained privately;
remote CI result and final commits are reported in the sprint handoff.

No web-generated CH19 section or independent content review is claimed complete.
The task system's tests use synthetic provider results; no inference credits were
spent by dispatching a provider in this sprint.
