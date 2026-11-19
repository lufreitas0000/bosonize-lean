---
title: "V1-S9 & BL-1 Finite-Regulator Residual Reconciliation"
phase: Phase B -> Phase C Gate
milestone: V1-S9
status: active
owner: lufreitas0000
last_updated: "2026-11-19"
tags: [bosonize-lean, v1-s9, bl-1, hc-qmb-09a, reconciliation]
depends_on:
  - CURRENT_SPRINT.md
  - BACKLOG.md
  - Bosonize/Core/V1S6PhysicalFields.lean
  - BosonizeStubs/Ch21SpinfulModels.lean
  - docs/companion/BosonizeStubs/Ch21SpinfulModels.md
  - docs/plans/v1-s9/ch21_phase_b_referee.md
---

# V1-S9 & BL-1 Finite-Regulator Residual Reconciliation

This note reconciles the live `main` baseline (`1997ac5`) in `bosonize-lean` against [`CURRENT_SPRINT.md`](../../../CURRENT_SPRINT.md), [`BACKLOG.md`](../../../BACKLOG.md) (`IDEA-001`), and the cross-repo `BL-1` / `HC-QMB-09a` finite-regulator residual ledger. No `.lean` source, `core_locks.json`, or [`docs/spec/stub_locks.v2.json`](../../spec/stub_locks.v2.json) is modified by this reconciliation.

---

## 1. Verified Baseline on `main` (`1997ac5`)

All checks below were executed directly on `main` (`1997ac5`):

| Check / Gate | Command | Observed Result | Notes |
| :--- | :--- | :--- | :--- |
| Core lock integrity | `python3 scripts/guards/core_lock.py` | **PASS** (exit `0`) | Verified `44` complete Core source files untouched. |
| Guard unit suite | `python3 -m unittest discover -s scripts/guards -p 'test_*.py'` | **PASS** (exit `0`) | `69` tests passed in `0.994s`. |
| Lean builds (Core + Stubs) | `lake build Bosonize && lake build BosonizeStubs` | **PASS** (exit `0`) | `Build completed successfully (3451 jobs)`; `0` `sorry`/warnings on [`BosonizeStubs/Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean) (`56/56` exported declarations on standard axioms `{propext, Classical.choice, Quot.sound}`, per [`ch21_phase_b_referee.md`](./ch21_phase_b_referee.md)). |
| WebLLM verification suite | `python3 -m unittest discover -s scripts/webllm -p 'test_*.py'` | **PASS** (exit `0`) | `18` tests passed in `20.381s` (with `elan` / `lake` on `PATH`). |
| Strict stub-lock Phase C gate | `python3 scripts/guards/stub_lock.py --check --strict` | **FLAGGED (expected)** (exit `1`) | Flags [`BosonizeStubs/Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean) as a new unbaselined staging file (`75 unlocked lemma(s), 42 unfrozen command(s)`). |

### Remaining Phase C Gate

- [`BosonizeStubs/Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean) (and its mirrored companion [`docs/companion/BosonizeStubs/Ch21SpinfulModels.md`](../../companion/BosonizeStubs/Ch21SpinfulModels.md)) remains in Phase B staging awaiting human Phase C review, promotion to `Bosonize/Core/`, and human-reviewed update of [`docs/spec/stub_locks.v2.json`](../../spec/stub_locks.v2.json) (never auto-updated by agents).

---

## 2. `BL-1` Finite-Regulator Residual Ledger (`HC-QMB-09a` / `IDEA-001`)

This ledger maps proved finite-carrier residual and counterexample theorems in `bosonize-lean` to downstream numerical falsification/verification in `xxz-benchmark` ([`HC-QMB-09.yaml`](../../../../xxz-benchmark/doc/hypotheses/HC-QMB-09.yaml)) and pedagogical derivations in `qed3-duality/workplace` ([`ch01_m02_current_algebra_klein.tex`](../../../../qed3-duality/workplace/src/ch01/ch01_m02_current_algebra_klein.tex), [`ch01_m03_mattis_mandelstam.tex`](../../../../qed3-duality/workplace/src/ch01/ch01_m03_mattis_mandelstam.tex)).

| Lean Module & Symbol | Proved Finite-Carrier Content (Core vs. Phase B Staging) | `xxz-benchmark` (`HC-QMB-09a`) Target | `qed3-duality/workplace` Target |
| :--- | :--- | :--- | :--- |
| [`V1S6PhysicalFields.lean`](../../../Bosonize/Core/V1S6PhysicalFields.lean#L108-L120) `quantitative_product_comparison` (Core) | Operator-norm bound decomposing projected product error into `intermediateResidual`, `omittedRangeResidual`, and `finiteDictionaryError` terms on fixed finite carriers. | Deterministic diagnostic baseline (`hc_qmb_09_bl1_wires.dat`): tracks cutoff/projection remainder norms ahead of owner `HC-QMB-09` threshold lock. | [`ch01_m03_mattis_mandelstam.tex`](../../../../qed3-duality/workplace/src/ch01/ch01_m03_mattis_mandelstam.tex) (§4.2): explicit separation of truncated Fock-budget remainder from formal continuum identities. |
| [`V1S6PhysicalFields.lean`](../../../Bosonize/Core/V1S6PhysicalFields.lean#L47-L59) `intermediateResidual`, `omittedRangeResidual` (Core) | Exact ambient discarded-channel (`(I - P) B`) and omitted embedded-range (`(P - U U†) B`) operators. | Tracks discarded intermediate-budget weight in `bosonize_v1s6_cdw_residual_bound`. | [`ch01_m03_mattis_mandelstam.tex`](../../../../qed3-duality/workplace/src/ch01/ch01_m03_mattis_mandelstam.tex) (§4.3): formalizes why finite-cutoff bilinear compositions carry explicit intermediate-projection residuals. |
| [`V1S6PhysicalFields.lean`](../../../Bosonize/Core/V1S6PhysicalFields.lean#L354-L360) `cdw_discarded_channel_norm_lower_bound` (Core) | Proves `‖projectedMap 2 ... cdwResidualOp ... (groundVector 2 ...)‖ ≥ 1 / 4` at `h = 2` (`L = 4, x = 1`), establishing non-vanishing CDW discarded-channel residual. | `bosonize_v1s6_cdw_residual_bound(h=2, x=1) == 0.25`: verifies nonzero discarded-channel norm (`≥ 1/4`) at `L = 4`. | [`ch01_m03_mattis_mandelstam.tex`](../../../../qed3-duality/workplace/src/ch01/ch01_m03_mattis_mandelstam.tex) (§4.3): illustrates finite-lattice Mattis-Mandelstam CDW projection leakage. |
| [`Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean) `umklapp_zero_charge_witness_coeff`, `umklapp_witness_h2_coeff` (Phase B staging; `stub_lock` pending) | Exact CAR matrix element `⟨Ψ_target \| H_U(g_U) \| Ω₀⟩ = -g_U / (2h)²`, specialized to `-g_U / 16` at `h = 2` (`L = 4`) via band-bottom hole `1 - h`. | `bosonize_ch21_umklapp_witness_amplitude`: independent sparse-Fock diagnostic (`-g_U / (2h)²`, `-g_U / 16` at `L = 4`) beyond `K ≤ 1` cutoffs. | [`ch01_m03_mattis_mandelstam.tex`](../../../../qed3-duality/workplace/src/ch01/ch01_m03_mattis_mandelstam.tex) (§4.4): finite-regulator band-bottom excitation cost `2(h - 1)` in bosonized Umklapp terms. |
| [`Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean) `umklapp_zero_budget_not_invariant` (Phase B staging; `stub_lock` pending) | Proves `periodicUmklappOp h g_U (groundKet h 0) ∉ jointBudget h 0 K` for all `0 < h, K : ℕ` and `g_U ≠ 0`. | Diagnostic anchor falsifying fixed-budget invariance under Umklapp perturbation (`hc_qmb_09_bl1_wires.dat`). | [`ch01_m03_mattis_mandelstam.tex`](../../../../qed3-duality/workplace/src/ch01/ch01_m03_mattis_mandelstam.tex) (§4.4): documents why fixed-energy Fock budgets are not invariant under real-space Umklapp. |
| [`Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean) `singlet_channel_targets_orthogonal` (Phase B staging; `stub_lock` pending) | Proves the two spin-singlet pairing channels `A = (R↓, L↑)` and `B = (R↑, L↓)` map into orthogonal `SpinBranch → ℤ` charge sectors. | Guides future sector-resolved singlet pairing correlator decomposition in spinful XXZ/Hubbard benchmarks. | Deferred to spinful [`ch02_m04_spinful_luttinger_sine_gordon.tex`](../../../../qed3-duality/workplace/src/ch02/ch02_m04_spinful_luttinger_sine_gordon.tex) (`ch01_m02..03` remain spinless/single-species). |
