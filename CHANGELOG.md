# Changelog (Units of Work) — bosonize-lean

All notable changes and conceptual evolutions are recorded here per Unit of Work (`PG-10` + Rule 06).

## [Unreleased]

### [2026-11-20] [V1-S9-U3] [Actor: Antigravity] — V1 Release Readiness & Ch21 Pedagogical Coverage Audit (`v1_release_readiness_audit.md`)
#### Ideas & Contracts Evolved
- Completed line-referenced V1 release readiness and Ch21 pedagogical coverage audit (`docs/plans/v1-s9/v1_release_readiness_audit.md`), verifying 44 frozen Core files (`core_lock.py` = 0), 69 guard tests, `lake build Bosonize` / `BosonizeStubs`, and 94 passing `#print axioms` checks (`56` exported proofs + `34` exported data + `4` local instances) on `BosonizeStubs/Ch21SpinfulModels.lean` alongside the 19 `private lemma`s that trigger `audit_axioms.py` and `stub_lock.py --strict` ahead of human Phase C promotion.
- Cataloged remaining LaTeX-vs-Lean coverage gaps (`prop:ch21-continuum-charge-spin-decoupling`, `thm:ch21-umklapp-spin-cancel`, `thm:ch21-scaling-dimension-mott`, partial `prop:ch21-global-edge`, standalone $\mathbb{Z}^4$ cocycle, combined $W = V_{t,1}\oplus V_{t,2}$ singlet projection, `A10` analytic remainder, and stale `2026-10-17` disclaimers in `21.1.tex`–`21.3.tex`), passing W4 independent audit (`ACCEPT`).

#### Code & Artifacts Changed
- Added `docs/plans/v1-s9/v1_release_readiness_audit.md`; updated `LOG_DISCOVERY_AND_PIVOTS.md` and `CHANGELOG.md`.

### [2026-11-19] [V1-S9-U2] [Actor: Antigravity] — Wave-2 `BL-1` residual & `Ch21` Phase B reconciliation ledger (`bl1_and_s9_reconciliation.md`)
#### Ideas & Contracts Evolved
- Audited exact Core (`Ch10`, `Ch13`, `V1S6`) and Phase B staging (`Ch21SpinfulModels.lean`) residual bounds and recorded their exact mathematical transfer contracts (`ch01_m02`, `ch01_m03`, `ch02_m04`, `HC-QMB-09`).
- Documented why `stub_lock.py --check --strict` intentionally reports `Ch21SpinfulModels.lean` as unlocked pending human Phase C review (`core_lock.py` 44 Core files untouched).

#### Code & Artifacts Changed
- Added `docs/plans/v1-s9/bl1_and_s9_reconciliation.md`; updated `LOG_DISCOVERY_AND_PIVOTS.md` and `CHANGELOG.md`.

### [2026-11-18] [V1-S9-U1] [Actor: Antigravity] — Consolidate 105+ historical branches into single main, preserve V1 planning/review records, and adopt Four-Record + HORIZON + UoW CHANGELOG
#### Ideas & Contracts Evolved
- Archived 105+ local/remote branches, stash@{0}, and .codex scratch before pruning to single main.
- Restored missing 2026-10-17 CH20 row in LOG_DISCOVERY_AND_PIVOTS.md and ignored .scratch/.
- Added hub cross-project horizon pointers to proposal notes.

#### Code & Artifacts Changed
- Added PROJECT_STATE.yaml, HORIZON.md, CHANGELOG.md; updated README.md, CURRENT_SPRINT.md, .gitignore, LOG_DISCOVERY_AND_PIVOTS.md; preserved untracked docs/plans/* & notes/review/*; synced .agents/.
