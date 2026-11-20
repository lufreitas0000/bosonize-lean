---
title: "V1 Release Readiness & Chapter 21 Pedagogical Coverage Audit"
phase: Phase B -> Phase C Gate
milestone: V1-S9
status: active
owner: lufreitas0000
last_updated: "2026-11-20"
tags: [bosonize-lean, v1-s9, ch21, release-readiness, audit]
depends_on:
  - CURRENT_SPRINT.md
  - docs/plans/v1-s9/bl1_and_s9_reconciliation.md
  - docs/plans/v1-s9/ch21_phase_b_referee.md
  - BosonizeStubs/Ch21SpinfulModels.lean
  - docs/companion/BosonizeStubs/Ch21SpinfulModels.md
  - notes/latex/chapters/ch21_spinful_umklapp.tex
---

# V1 Release Readiness & Chapter 21 Pedagogical Coverage Audit

**Date:** 2026-11-20  
**Repository Baseline:** `main` at `92607c5` (`bosonize-lean`)  
**Scope:** Read-only verification of frozen Core (`Bosonize/Core/`), Phase B staging (`BosonizeStubs/Ch21SpinfulModels.lean`), guard/WebLLM/book-check scripts, and claim-by-claim reconciliation against [`notes/latex/chapters/ch21_spinful_umklapp.tex`](../../../notes/latex/chapters/ch21_spinful_umklapp.tex) (`sections/21.1.tex`–`21.4.tex`). No `.lean`, `core_locks.json`, `docs/spec/stub_locks.v2.json`, or `notes/latex/` files were modified.

---

## 1. Executive Verdict

- **Frozen Core (`Bosonize`, 44 files):** **PASS / V1-READY.** `core_lock.py` verifies all `44` Core files untouched, `lake build Bosonize` succeeds, and all `69` guard unit tests pass.
- **Chapter 21 (`BosonizeStubs/Ch21SpinfulModels.lean`):** **PHASE B COMPLETE — BLOCKED ON HUMAN PHASE C GATE.** All `1,283` lines (`56` exported proof declarations: `51` `lemma`s + `5` `theorem`s, `34` exported data declarations [`32` `def` + `1` `abbrev` + `1` `structure`] + `4` `local instance`s = `38` data/instance commands, and `19` `private lemma`s = `113` total `phase_b.declarations`) compile with zero warnings and zero `sorry`s, and all `94` passing `#print axioms` checks (`56` exported proofs + `38` exported data/instance commands) depend solely on standard Lean axioms (`{propext, Classical.choice, Quot.sound}`, `[propext]`, or none). Two automated gates intentionally/expectedly return exit `1` in Phase B:
  1. `verify_phase_b.py` (via `stub_lock.py --check --strict`) rejects `BosonizeStubs/Ch21SpinfulModels.lean` as a `NEW file not in the baseline (75 unlocked lemma(s), 42 unfrozen command(s))` awaiting human Phase C review and `docs/spec/stub_locks.v2.json` update.
  2. `audit_axioms.py` exits `1` because it emits `#print axioms` for all `19` `private lemma`s in `Bosonize.Ch21` (`Unknown constant` errors), even though all `94` exported declarations/instances are axiom-clean.
- **Pedagogical Coverage (`ch21_spinful_umklapp.tex`):** **PARTIAL (Finite CAR Proved; Continuum/RG & Some Finite Bridges Unformalized).** Finite-carrier spin-charge current algebra, parity sublattice, two-channel singlet orthogonality/residuals, Umklapp charge-sector selection rules, self-adjointness, and the `B4` witness (`-g_U/(2h)^2`) are constructively proved in `Ch21SpinfulModels.lean`, and discrete Schrieffer–Wolff algebra is proved in Core `A10DiscreteSchriefferWolff.lean`. Continuum/RG theorems (`prop:ch21-continuum-charge-spin-decoupling`, `thm:ch21-umklapp-spin-cancel`, `thm:ch21-scaling-dimension-mott`), the standalone $\mathbb{Z}^4$ Klein 2-cocycle (`thm:ch21-cocycle-identity`), the combined `W = V_{t,1} ⊕ V_{t,2}` singlet codomain (`thm:ch21-pair-projected`), and the analytic SW Taylor remainder bound (`prop:ch21-sw-analytic-remainder`) remain unformalized in Lean.

---

## 2. Executed Verification Commands & Observed Results

All commands were executed directly in `/home/lu/Projects/research/qmb/bosonize-lean` on `main` (`92607c5`):

| # | Command | Exit | Observed Output / Notes |
| :--- | :--- | :--- | :--- |
| 1 | `python3 scripts/guards/core_lock.py` | `0` | `[core_lock] Verified 44 complete Core source file(s).` |
| 2 | `python3 -m unittest discover -s scripts/guards -p 'test_*.py'` | `0` | `Ran 69 tests in 1.004s` — `OK`. |
| 3 | `PATH="$HOME/.elan/bin:$PATH" lake build Bosonize` | `0` | Core builds cleanly. |
| 4 | `PATH="$HOME/.elan/bin:$PATH" lake build BosonizeStubs` | `0` | `Build completed successfully (3449 jobs)`; zero warnings/errors on `BosonizeStubs/Ch21SpinfulModels.lean`. |
| 5 | `PATH="$HOME/.elan/bin:$PATH" python3 scripts/webllm/verify_phase_b.py BosonizeStubs/Ch21SpinfulModels.lean` | `1` | Rejected by `stub_lock.py --check --strict --baseline-ref 92607c5...`: `(strict) BosonizeStubs/Ch21SpinfulModels.lean: NEW file not in the baseline (75 unlocked lemma(s), 42 unfrozen command(s))`. Expected until human Phase C baseline update. |
| 6 | `PATH="$HOME/.elan/bin:$PATH" python3 scripts/webllm/audit_axioms.py BosonizeStubs/Ch21SpinfulModels.lean` | `1` | `ValueError: Imported axiom audit failed`. All `94` passing `#print axioms` lines (`56` exported proofs + `34` exported data declarations + `4` `local instance`s) print `[propext, Classical.choice, Quot.sound]`, `[propext]`, or no axioms; failure is caused by `audit_axioms.py` querying all `19` `private lemma`s (`Unknown constant`, `94 + 19 = 113` total `phase_b.declarations`). |
| 7a | `python3 -m unittest discover -s scripts/webllm -p 'test_*.py'` (default `PATH`) | `1` | `Ran 18 tests in 1.010s` — `FAILED (errors=2)`: `test_verify_phase_a` and `test_verify_phase_b` fail with `FileNotFoundError: 'lake'` when `~/.elan/bin` is not on `PATH`. |
| 7b | `PATH="$HOME/.elan/bin:$PATH" python3 -m unittest discover -s scripts/webllm -p 'test_*.py'` | `0` | `Ran 18 tests in 18.858s` — `OK`. |
| 8a | `python3 scripts/check_book_sources.py` | `0` | `PASS: master includes chapters 19; sections 20.1, 20.2, 20.3, 21.1, 21.2, 21.3, 21.4`. |
| 8b | `python3 scripts/check_book_log.py` (no args) | `1` | `IndexError: list index out of range` (requires `<logfile>` argument). |
| 8c | `python3 scripts/check_book_log.py notes/latex/main.log` | `0` | `PASS: references, citations and labels` (note: `notes/latex/main.log` dates from commit `40dea8b`, `2026-10-17`, matching the last commit of `ch21_spinful_umklapp.tex` and `21.1.tex`–`21.4.tex`). |

---

## 3. Epistemic Separation: Frozen Core vs. Phase B Staging

| Tier | Modules | Status | Lock / Audit State |
| :--- | :--- | :--- | :--- |
| **Frozen Core (`Bosonize/Core/`)** | `44` modules (`A01`–`A10`, `Ch01`–`Ch20`, `V1S1`–`V1S6`) | **Verified & Frozen** | `core_lock.py` exit `0`; `lake build Bosonize` exit `0`. |
| **Phase B Staging (`BosonizeStubs/`)** | [`BosonizeStubs/Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean) | **Phase B Complete; Awaiting Phase C** | `lake build BosonizeStubs` exit `0`, `0` `sorry`, `56/56` exported proofs on standard axioms; `stub_lock.py --strict` exit `1` (unbaselined). |

---

## 4. Claim-by-Claim Crosswalk: `ch21_spinful_umklapp.tex` (`21.1`–`21.4`) vs. Lean

### 4.1 Section 21.1 — Spinful Species, Raw Currents, and the Parity Sublattice ([`21.1.tex`](../../../notes/latex/chapters/sections/21.1.tex))

| LaTeX Claim / Equation | Lean Realization & Tier | Coverage & Gap Notes |
| :--- | :--- | :--- |
| `def:ch21-species` (`L↑ < L↓ < R↑ < R↓`, 4-species CAR) | **Core** (`A05.Mode`, `A05.speciesOrder`, `A05.annihilation_car`, `A05.creation_car`, `A05.mixed_car`) + **Phase B** (`SpinBranch`, `brLUp`–`brRDown`) | **Proved.** |
| `def:ch21-raw-currents` (`R^{c,s}_{\eta,m}`, adjointness) | **Phase B** (`rhoChargeL`, `rhoSpinL`, `rhoChargeR`, `rhoSpinR`, `*_adjoint`) | **Proved.** |
| `prop:ch21-global-edge` & `thm:ch21-budget-ccr` (ambient edge identities, cross-chirality commutation, `2κ(m,n) = -2m` / `0` on common margin) | **Phase B** (`rhoChargeR_rhoChargeL_commute`, `rhoSpinR_rhoSpinL_commute`, `rhoChargeL_commutator`, `rhoSpinL_commutator`, `rhoChargeL_rhoSpinL_commutator`, `rhoChargeR_commutator`, `rhoSpinR_commutator`, `rhoChargeR_rhoSpinR_commutator`) | **Partial (`thm:ch21-budget-ccr` Proved; `prop:ch21-global-edge` Partial):** Common-margin budget evaluations and same-type cross-chirality (`[R^c_R, R^c_L] = 0`, `[R^s_R, R^s_L] = 0`) are proved (via Core `A06.joint_signed_current_commutator`, `A05.rho_cross_commute`), whereas `prop:ch21-global-edge`'s ambient (unbudgeted) edge-difference equations `[R^c, R^s] = E_↑ - E_↓`, `[R^c, R^c] = [R^s, R^s] = E_↑ + E_↓` and mixed cross-chirality `[R^c_R, R^s_L] = 0` / `[R^s_R, R^c_L] = 0` are omitted. |
| `prop:ch21-continuum-charge-spin-decoupling` (`[J_{r,c}(x), J_{r',s}(y)] = 0`, $SU(2)$ pinning $K_s = 1$) | **Not in Lean** | **Gap (Continuum/RG):** Distributional $\delta'(x-y)$ algebra and $SU(2)$ Luttinger-parameter pinning $K_s = 1$ are continuum physics statements, not formalized in Lean. |
| `ex:ch21-first-mode`, `eq:ch21-off-margin-example` (`[R^c, R^s]v = -v`), `eq:ch21-compression-residual` | **Not in `Ch21SpinfulModels.lean`** | **Gap (Concrete Witnesses):** The off-margin counterexample and compressed-commutator residual identity are not instantiated in `Ch21SpinfulModels.lean` (cf. Core `V1S6PhysicalFields` for general projected product residuals). |
| `prop:ch21-parity-lattice` (integer zero modes & parity sublattice $\Lambda_{c,s}$) | **Phase B** (`totalChargeObservable`, `totalSpinObservable`, `SpinChargeTuple`, `branchesToSpinCharge`, `SpinChargeSublattice`, `spinChargeToBranches`, `branchesToSpinCharge_mem_sublattice`, `spinCharge_left_inv`, `spinCharge_right_inv`, `ChiralSpinChargeParity`, `chiral_spinCharge_recover`) | **Proved** (both full 4-branch mod-4 sublattice and per-chirality mod-2 parity). |
| `thm:ch21-cocycle-identity`, `def:ch21-four-klein`, `prop:ch21-klein-anticommute` ($\mathbb{Z}^4$ Klein 2-cocycle) | **Partial in Core** (`Ch13.kleinKernel`, `Ch13.kernel_cross_anticommute`) / **Not in `Ch21SpinfulModels.lean`** | **Gap:** The standalone $\mathbb{Z}^4$ cocycle identity $\varepsilon(p,q)\varepsilon(p+q,t) = \varepsilon(q,t)\varepsilon(p,q+t)$ and $F_i = P_{<i} T_i$ on $\mathbb{C}^{(\mathbb{Z}^4)}$ are not formalized in `Ch21SpinfulModels.lean`. |
| `eq:ch21-budget-energy-sum`, `eq:ch21-not-product-cutoff` | **Not in `Ch21SpinfulModels.lean`** | **Gap:** Graded direct-sum decomposition of `jointBudget` and non-product counterexample at $K=1$ are not formalized. |
| `prop:ch21-quadratic-block`, `eq:ch21-block-speed`, `eq:ch21-hyperbolic-parameters`, `ex:ch21-equal-speeds` | **Partial in Core** (`A07.HyperbolicParams`, `A07.hyperbolic_params_exist`) / **Not in `Ch21SpinfulModels.lean`** | **Gap:** Ordered quadratic block diagonalization `a(X_↑ Y_↑ + X_↓ Y_↓) + b(...)` and spinful $(u_c, u_s)$ speed non-degeneracy are not formalized in `Ch21SpinfulModels.lean`. |

### 4.2 Section 21.2 — The Spin-Singlet Cooper Pair and Its Two Charge Channels ([`21.2.tex`](../../../notes/latex/chapters/sections/21.2.tex))

| LaTeX Claim / Equation | Lean Realization & Tier | Coverage & Gap Notes |
| :--- | :--- | :--- |
| `def:ch21-singlet` (`O_{SSC}(x) = A_1(x) - A_2(x)` = `c_{R↑}c_{L↓} - c_{R↓}c_{L↑}`) | **Phase B** (`singletBranchesA`, `singletBranchesB`, `singletOrderSC := Ch20.orderSC ... singletBranchesB - Ch20.orderSC ... singletBranchesA`) | **Proved / Aligned** (sign convention matches `O_{SSC}(x)` verbatim). |
| `lem:ch21-singlet-shifts` (distinct targets $\mathbf{T}_1 \ne \mathbf{T}_2$, orthogonality, $\Delta Q_c = -2, \Delta Q_s = 0$) | **Phase B** (`singlet_targets_distinct`, `singlet_channel_targets_orthogonal`, `singlet_preserves_spin_and_shifts_charge`) | **Proved.** |
| `prop:ch21-two-klein-products`, `lem:ch21-pair-ground-action`, `ex:ch21-pair-sign` (`±1/4` at `h=2`), `eq:ch21-pair-general-sign` | **Not in `Ch21SpinfulModels.lean`** | **Gap:** Ground-state Klein phase products and the `h = 2` `±1/4` singlet matrix element witness are not yet formalized in `Ch21SpinfulModels.lean` (cf. Core `Ch13.ground_field_coefficient` for single-field ground coefficients). |
| `thm:ch21-pair-projected` (`p_W O_{SSC}(x) i_s` on $W = V_{t,1} \oplus V_{t,2}$) | **Phase B (channel-wise)** (`singletA_projected_residual`, `singletB_projected_residual` via **Core** `Ch20.projected_sc_residual`) | **Partial Gap:** Channel-wise projected residuals are proved, but the combined orthogonal-sum codomain $W = V_{t,1} \oplus V_{t,2}$ projection theorem (`eq:ch21-pair-typed-identity`) is not yet assembled (noted as `[W2]` in `ch21_phase_b_referee.md`). |
| `ex:ch21-pair-residual` (`-i/4` intermediate residual witness at `h=2`), `rem:ch21-pair-enlarged-target` | **Not in `Ch21SpinfulModels.lean`** | **Gap:** Concrete singlet intermediate-projection residual witness is not formalized in `Ch21SpinfulModels.lean`. |

### 4.3 Section 21.3 — Umklapp Scattering, Charge-Sector Leakage, and Finite Projection ([`21.3.tex`](../../../notes/latex/chapters/sections/21.3.tex))

| LaTeX Claim / Equation | Lean Realization & Tier | Coverage & Gap Notes |
| :--- | :--- | :--- |
| `def:ch21-u-word`, `prop:ch21-u-selfadjoint` ($H_U^\dagger = H_U$) | **Phase B** (`umklappForwardSite`, `umklappBackwardSite`, `umklappOp`, `periodicUmklappOp`, `umklappOp_self_adjoint`) | **Proved.** |
| `lem:ch21-u-fundamental-commutators`, `thm:ch21-u-charge-shift` (charge shift `(+1,+1,-1,-1)`, `Q_c, Q_s, J_s` conservation, `J_c ∓ 4`), `cor:ch21-u-sector-compression` | **Phase B** (`umklappForwardSite_charge_commutator`, `umklappBackwardSite_charge_commutator`, `umklapp_quantum_number_shifts`, `umklappForwardSite_maps_sector`, `umklappBackwardSite_maps_sector`, `umklappOp_charge_diagonal_zero`) | **Proved.** |
| `def:ch21-u-charge-box`, `thm:ch21-u-leakage` (general per-species charge box $\mathcal{B}_{K,\mathbf{B}}$ leakage) | **Partial in Phase B** (`umklapp_zero_budget_not_invariant` for `jointBudget h 0 K`) | **Partial Gap:** Proved for zero-charge budgets `jointBudget h (fun _ => 0) K`; general per-species box `B_{K, \mathbf{B}}` and `[P_{K,\mathbf{B}}, H_U] \ne 0` are not separately formalized. |
| `thm:ch21-u-zero-box-witness` (`-g_U / L^2` = `-g_U / (2h)^2`), `ex:ch21-u-four-site` (`-1/16` at `h=2`) | **Phase B** (`umklappZeroChargeWitness`, `umklapp_zero_charge_witness_coeff`, `umklapp_witness_h2_coeff`, `umklapp_witness_h1_coeff`, `umklapp_zero_budget_not_invariant`) | **Proved.** |
| `ex:ch21-u-inward-only` (Pauli-blocked `h=2` inward-only state `|S⟩`, `g_U/16`) | **Not in `Ch21SpinfulModels.lean`** | **Gap:** Not formalized in `Ch21SpinfulModels.lean`. |
| `thm:ch21-umklapp-spin-cancel` ($\mathcal{O}_U \propto \cos(\sqrt{8\pi}\phi_c) \otimes I_{\text{spin}}$), `thm:ch21-scaling-dimension-mott` ($x_{\text{umklapp}} = 2K_c$, BKT flow, Mott gap $\Delta_c > 0$) | **Not in Lean** | **Gap (Continuum/RG):** Bosonized vertex cancellation, scaling dimension $2K_c$, BKT RG flow, and Mott gap are continuum/RG theory statements, not formalized in Lean. (Also note `21.3.tex` L606 cites `Theorem~\ref{thm:ch19-exponent-dictionary}`, whereas Core `Ch19Correlations.lean` proves finite-carrier density-kernel and Bogoliubov expectation identities rather than continuum vertex scaling dimensions.) |

### 4.4 Section 21.4 — Finite Energy-Shell Projection and Effective Hamiltonians ([`21.4.tex`](../../../notes/latex/chapters/sections/21.4.tex))

| LaTeX Claim / Equation | Lean Realization & Tier | Coverage & Gap Notes |
| :--- | :--- | :--- |
| `prop:ch21-shell-partition` ($P^2=P=P^\dagger$, $Q^2=Q=Q^\dagger$, $PQ=0$, $P+Q=\Pi_{\mathbf{N},K}$) | **Core** (`A10.shell_proj_partition`, `A10.shell_proj_orthogonal`, `A10.shell_proj_self_adjoint`) | **Proved.** |
| `ex:ch21-shell-versus-mode` (repeated mode-1 witness discarded by $P$) | **Core** (`A10.energy_shell_discards_double_mode_one`) | **Proved.** |
| `thm:ch21-sw-generator` (`[S_1, H_0] = -V_o`, $S_1^\dagger = -S_1$) | **Core** (`A10.sw_generator_commutator_eq`, `A10.sw_generator_skew_hermitian`) | **Proved.** |
| `thm:ch21-sw-compressed` (exact compressed degree-two BCH polynomial) | **Core** (`A10.sw_compressed_bch_second_order`) | **Proved.** |
| `prop:ch21-sw-intermediate` (sum-over-states formula for $W^{(2)}$) | **Not in Core `A10`** | **Gap:** Explicitly expanded matrix-entry sum over $\mu \in I_Q$ is not separately stated in `A10DiscreteSchriefferWolff.lean`. |
| `prop:ch21-sw-analytic-remainder` (integral Taylor remainder & operator-norm bound $\|PR_3(t)P\|$) | **Not in Core `A10`** | **Gap (explicitly acknowledged in `21.4.tex` L487–488):** `A10` proves the algebraic degree-two polynomial identity, not the analytic exponential Taylor remainder bound. |
| `ex:ch21-sw-two-level` & `ex:ch21-sw-three-level` (`2×2` and `3×3` witnesses, plus `V_o = 0` exactness) | **Core** (`A10.sw_2x2_truncation_witness`, `A10.sw_2x2_exact_eigenpair`, `A10.sw_3x3_no_iff_witness`, `A10.sw_off_zero_implies_effective_exact`) | **Proved.** |
| Instantiation of `A10` onto spinful `Ch21` Hamiltonians | **Not in Lean** | **Gap:** Bridge transferring `Ch21` spinful Hamiltonians into `A10` hypotheses (`[P, H_0] = 0`, non-resonance) is not formalized (acknowledged in `21.4.tex` L596–603). |

---

## 5. Pedagogical Sync & V1 Release Recommendations

1. **Human Phase C Promotion (Blocking V1 Closure of Ch21):**
   - Conduct human Phase C review of [`BosonizeStubs/Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean), promote to `Bosonize/Core/`, and update [`docs/spec/stub_locks.v2.json`](../../spec/stub_locks.v2.json) + `core_locks.json` so `verify_phase_b.py` and `stub_lock.py --check --strict` pass.
2. **Tooling Hygiene (Non-blocking for math, blocking for automated axiom CI):**
   - Update `scripts/webllm/audit_axioms.py` to filter out `private` declarations when emitting `#print axioms` checks.
3. **Pedagogical Sync (`21.1.tex`–`21.3.tex`, `notes/md/ch21_spinful_models.md`):**
   - Once Phase C promotion occurs, update the stale `2026-10-17` disclaimers in `21.1.tex` (L799–802), `21.2.tex` (L626–628), and `21.3.tex` (L655–658) so they accurately distinguish:
     - **Verified finite-CAR Ch21 results** (spin-charge currents, parity sublattice, singlet channel orthogonality/residuals, Umklapp selection rules & `B4` witness, Core `A10` discrete SW), from
     - **Unformalized continuum/RG & future finite-bridge items** (`prop:ch21-continuum-charge-spin-decoupling`, `thm:ch21-cocycle-identity`, combined `W = V_{t,1} \oplus V_{t,2}` `thm:ch21-pair-projected`, `thm:ch21-umklapp-spin-cancel`, `thm:ch21-scaling-dimension-mott`, `prop:ch21-sw-analytic-remainder`).
