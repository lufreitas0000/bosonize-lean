# Changelog (Units of Work) — bosonize-lean

All notable changes and conceptual evolutions are recorded here per Unit of Work (`PG-10` + Rule 06).

## [Unreleased]

### [2026-11-20] [V1-S9-U4] [Actor: Antigravity] — Close Ch21 Finite-CAR Phase B Gaps & Fix `audit_axioms.py` Private-Declaration Filtering
#### Ideas & Contracts Evolved
- Fixed `scripts/webllm/audit_axioms.py` (`is_private_decl` / `exported_declarations`) to filter `private` declarations before generating importing `#print axioms` checks, with regression tests in `scripts/webllm/test_audit_axioms.py` (`20/20` webllm unit tests pass; `audit_axioms.py BosonizeStubs/Ch21SpinfulModels.lean` now exits `0` across all `148` exported declarations, cleanly skipping `35` `private lemma`s).
- Closed the concrete finite-CAR Phase B gaps in `BosonizeStubs/Ch21SpinfulModels.lean` (`0` `sorry`, `0` warnings, standard axioms only):
  - `prop:ch21-global-edge`: ambient edge operator `edgeOp`, `[R^c, R^s] = E_↑ - E_↓`, `[R^c, R^c] = [R^s, R^s] = E_↑ + E_↓` for both chiralities, and mixed cross-chirality `[R^c_R, R^s_L] = 0` / `[R^s_R, R^c_L] = 0`.
  - `thm:ch21-pair-projected` (`[W2]`): combined orthogonal-sum codomain `W = V_{t,B} ⊕ V_{t,A}` (`singletTargetSum`, `singletTargetProjection`, `singletProjectedMap`, `singletOrderSC_projected_sum`) with independent cutoffs and explicit channel residuals.
  - Concrete `h = 2` witnesses: `ex:ch21-pair-sign` (`±1/4` opposite singlet amplitudes), `ex:ch21-pair-residual` (`⟨Ξ, (B_{a,1} ∘ B_{b,1}) Ω₀⟩ = 0`, `⟨Ξ, R₁ Ω₀⟩ = -i/4 ≠ 0`), and `ex:ch21-u-inward-only` (per-species charge box `speciesChargeBox`, Pauli-blocked `O_U(x)|S⟩ = 0`, inward matrix element `g_U/16`, and zero leakage `(I - P_{16,B}) H_U |S⟩ = 0`).
- Preserved `Bosonize/Core/`, `core_locks.json`, `docs/spec/stub_locks.v2.json`, and `notes/latex/` untouched; Phase B `BosonizeStubs/Ch21SpinfulModels.lean` continues to await human Phase C review/lock promotion (`stub_lock.py --strict` reports `121 unlocked lemma(s), 66 unfrozen command(s)`).

#### Code & Artifacts Changed
- Updated `scripts/webllm/audit_axioms.py`, `scripts/webllm/test_audit_axioms.py`, `BosonizeStubs/Ch21SpinfulModels.lean`, `docs/companion/BosonizeStubs/Ch21SpinfulModels.md`, `docs/plans/v1-s9/v1_release_readiness_audit.md`, `LOG_DISCOVERY_AND_PIVOTS.md`, and `CHANGELOG.md`.

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
