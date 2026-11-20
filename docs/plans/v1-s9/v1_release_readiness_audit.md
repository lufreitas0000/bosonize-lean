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

**Date:** 2026-11-20 (updated under `[V1-S9-U4]`)  
**Repository Baseline:** `main` at `92607c5` + uncommitted `[V1-S9-U4]` Phase B & tooling updates (`bosonize-lean`)  
**Scope:** Verification of frozen Core (`Bosonize/Core/`), updated Phase B staging (`BosonizeStubs/Ch21SpinfulModels.lean`), fixed `scripts/webllm/audit_axioms.py` (with new unit tests), guard/WebLLM/book-check scripts, and claim-by-claim reconciliation against [`notes/latex/chapters/ch21_spinful_umklapp.tex`](../../../notes/latex/chapters/ch21_spinful_umklapp.tex) (`sections/21.1.tex`–`21.4.tex`). `Bosonize/Core/`, `core_locks.json`, `docs/spec/stub_locks.v2.json`, and `notes/latex/` remain untouched.

---

## 1. Executive Verdict

- **Frozen Core (`Bosonize`, 44 files):** **PASS / V1-READY.** `core_lock.py` verifies all `44` Core files untouched, `lake build Bosonize` succeeds, and all `69` guard unit tests pass.
- **Chapter 21 (`BosonizeStubs/Ch21SpinfulModels.lean`):** **PHASE B COMPLETE (FINITE-CAR GAPS CLOSED) — BLOCKED ON HUMAN PHASE C GATE.** All `2,624` lines (`86` exported proof declarations: `71` `lemma`s + `15` `theorem`s; `62` exported data/instance commands [`56` `def` + `1` `abbrev` + `1` `structure` + `4` `local instance`s]; and `35` `private lemma`s = `183` total `phase_b.declarations`) compile with zero warnings and zero `sorry`s. With `scripts/webllm/audit_axioms.py` fixed to filter `private` declarations, `audit_axioms.py BosonizeStubs/Ch21SpinfulModels.lean` now exits **`0`** (`PASS: 148 freshly built data/theorem declarations`) verifying standard Lean axioms only (`{propext, Classical.choice, Quot.sound}`, `[propext]`, or none). Only one automated gate intentionally returns exit `1` in Phase B:
  1. `verify_phase_b.py` (via `stub_lock.py --check --strict`) rejects `BosonizeStubs/Ch21SpinfulModels.lean` as a `NEW file not in the baseline (121 unlocked lemma(s), 66 unfrozen command(s))` awaiting human Phase C review and `docs/spec/stub_locks.v2.json` update.
- **Pedagogical Coverage (`ch21_spinful_umklapp.tex`):** **FINITE-CAR CORE & CONCRETE WITNESSES PROVED; CONTINUUM/RG & HIGHER BRIDGES UNFORMALIZED.** Under `[V1-S9-U4]`, the previously open finite-CAR Phase B gaps in `Ch21SpinfulModels.lean` are now constructively proved:
  - `prop:ch21-global-edge`: ambient (unbudgeted) edge-difference identities `[R^c, R^s] = E_↑ - E_↓`, `[R^c, R^c] = [R^s, R^s] = E_↑ + E_↓`, and mixed cross-chirality `[R^c_R, R^s_L] = 0` / `[R^s_R, R^c_L] = 0`;
  - `thm:ch21-pair-projected` (`[W2]`): combined orthogonal-sum codomain `W = V_{t,B} ⊕ V_{t,A}` (`singletOrderSC_projected_sum`, Eq. (21.7)) with independent cutoffs and explicit channel residuals;
  - Concrete `h = 2` finite-CAR witnesses: `ex:ch21-pair-sign` (`±1/4`), `ex:ch21-pair-residual` (`-i/4` intermediate residual witness & zero projected composition), and `ex:ch21-u-inward-only` (Pauli-blocked inward-only `g_U/16` witness with zero box leakage `(I - P_{16,B}) H_U |S⟩ = 0`).
  Continuum/RG theorems (`prop:ch21-continuum-charge-spin-decoupling`, `thm:ch21-umklapp-spin-cancel`, `thm:ch21-scaling-dimension-mott`), the standalone $\mathbb{Z}^4$ Klein 2-cocycle (`thm:ch21-cocycle-identity`), and the analytic SW Taylor remainder bound (`prop:ch21-sw-analytic-remainder`) remain unformalized in Lean.

---

## 2. Executed Verification Commands & Observed Results

All commands were executed directly in `/home/lu/Projects/research/qmb/bosonize-lean` after the `[V1-S9-U4]` updates (with `PATH="$HOME/.elan/bin:$PATH"`):

| # | Command | Exit | Observed Output / Notes |
| :--- | :--- | :--- | :--- |
| 1 | `python3 scripts/guards/core_lock.py` | `0` | `[core_lock] Verified 44 complete Core source file(s).` |
| 2 | `python3 -m unittest discover -s scripts/guards -p 'test_*.py'` | `0` | `Ran 69 tests in 1.004s` — `OK`. |
| 3 | `PATH="$HOME/.elan/bin:$PATH" python3 -m unittest discover -s scripts/webllm -p 'test_*.py'` | `0` | `Ran 20 tests in 9.582s` — `OK` (includes 2 new `test_audit_axioms.py` tests for `private` declaration filtering). |
| 4 | `PATH="$HOME/.elan/bin:$PATH" lake build Bosonize` | `0` | Core builds cleanly (`Build completed successfully`). |
| 5 | `PATH="$HOME/.elan/bin:$PATH" lake build BosonizeStubs` | `0` | `Build completed successfully`; zero warnings/errors on `BosonizeStubs/Ch21SpinfulModels.lean`. |
| 6 | `PATH="$HOME/.elan/bin:$PATH" python3 scripts/webllm/audit_axioms.py BosonizeStubs/Ch21SpinfulModels.lean` | `0` | `PASS: 148 freshly built data/theorem declarations` (`86` exported proofs + `62` exported data/instance commands; `35` `private lemma`s cleanly filtered). |
| 7 | `python3 scripts/guards/stub_lock.py --check --strict` | `1` | `(strict) BosonizeStubs/Ch21SpinfulModels.lean: NEW file not in the baseline (121 unlocked lemma(s), 66 unfrozen command(s))`. Expected until human Phase C baseline update. |
| 8 | `python3 scripts/check_book_sources.py` | `0` | `PASS: master includes chapters 19; sections 20.1, 20.2, 20.3, 21.1, 21.2, 21.3, 21.4`. |
| 9 | `python3 -B /home/lu/Projects/scripts/uow.py check --repo /home/lu/Projects/research/qmb/bosonize-lean` | `0` | `[PASS] bosonize-lean` / `Summary: 1/1 passed.` |

---

## 3. Epistemic Separation: Frozen Core vs. Phase B Staging

| Tier | Modules | Status | Lock / Audit State |
| :--- | :--- | :--- | :--- |
| **Frozen Core (`Bosonize/Core/`)** | `44` modules (`A01`–`A10`, `Ch01`–`Ch20`, `V1S1`–`V1S6`) | **Verified & Frozen** | `core_lock.py` exit `0`; `lake build Bosonize` exit `0`. |
| **Phase B Staging (`BosonizeStubs/`)** | [`BosonizeStubs/Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean) | **Phase B Complete; Awaiting Phase C** | `lake build BosonizeStubs` exit `0`, `0` `sorry`, `audit_axioms.py` exit `0` (`148/148` exported declarations on standard axioms); `stub_lock.py --strict` exit `1` (unbaselined). |

---

## 4. Claim-by-Claim Crosswalk: `ch21_spinful_umklapp.tex` (`21.1`–`21.4`) vs. Lean

### 4.1 Section 21.1 — Spinful Species, Raw Currents, and the Parity Sublattice ([`21.1.tex`](../../../notes/latex/chapters/sections/21.1.tex))

| LaTeX Claim / Equation | Lean Realization & Tier | Coverage & Gap Notes |
| :--- | :--- | :--- |
| `def:ch21-species` (`L↑ < L↓ < R↑ < R↓`, 4-species CAR) | **Core** (`A05.Mode`, `A05.speciesOrder`, `A05.annihilation_car`, `A05.creation_car`, `A05.mixed_car`) + **Phase B** (`SpinBranch`, `brLUp`–`brRDown`) | **Proved.** |
| `def:ch21-raw-currents` (`R^{c,s}_{\eta,m}`, adjointness) | **Phase B** (`rhoChargeL`, `rhoSpinL`, `rhoChargeR`, `rhoSpinR`, `*_adjoint`) | **Proved.** |
| `prop:ch21-global-edge` & `thm:ch21-budget-ccr` (ambient edge identities, cross-chirality commutation, `2κ(m,n) = -2m` / `0` on common margin) | **Phase B** (`edgeOp`, `rhoChargeL_rhoSpinL_global_edge`, `rhoChargeL_global_edge`, `rhoSpinL_global_edge`, `rhoChargeL_eq_rhoSpinL_global_edge`, `rhoChargeR_rhoSpinR_global_edge`, `rhoChargeR_global_edge`, `rhoSpinR_global_edge`, `rhoChargeR_eq_rhoSpinR_global_edge`, `rhoChargeR_rhoChargeL_commute`, `rhoSpinR_rhoSpinL_commute`, `rhoChargeR_rhoSpinL_commute`, `rhoSpinR_rhoChargeL_commute`, `rhoChargeL_commutator`, `rhoSpinL_commutator`, `rhoChargeL_rhoSpinL_commutator`, `rhoChargeR_commutator`, `rhoSpinR_commutator`, `rhoChargeR_rhoSpinR_commutator`) | **Proved** (both `prop:ch21-global-edge` ambient edge-difference identities + all four cross-chirality commutators and `thm:ch21-budget-ccr` common-margin evaluations are constructively proved). |
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
| `prop:ch21-two-klein-products`, `lem:ch21-pair-ground-action`, `ex:ch21-pair-sign` (`±1/4` at `h=2`), `eq:ch21-pair-general-sign` | **Phase B (`ex:ch21-pair-sign` Proved)** (`singlet_pair_sign_channel1_h2`, `singlet_pair_sign_channel2_h2`, `singlet_pair_sign_h2`) / general `h` formula not yet in `Ch21SpinfulModels.lean` | **Partial (`ex:ch21-pair-sign` Proved):** The `h = 2, L = 4, x = 1` concrete singlet witness (`-1/4` on channel 1, `+1/4` on channel 2) is constructively proved; general-`h` Klein product (`eq:ch21-pair-general-sign`) remains optional future work. |
| `thm:ch21-pair-projected` (`p_W O_{SSC}(x) i_s` on $W = V_{t,1} \oplus V_{t,2}$) | **Phase B** (`singletTargetUnionSet`, `singletTargetSum`, `singletTargetSum_disjoint`, `singletTargetInclB`, `singletTargetInclA`, `singletTargetProjection` + `_eq_coord`/`_idempotent`/`_adjoint`/`_range`, `singletProjectedMap`, `singletA_projected_residual`, `singletB_projected_residual`, `singletOrderSC_projected_sum`) | **Proved** (closes `[W2]` from `ch21_phase_b_referee.md`: combined orthogonal-sum codomain `W = V_{t,B} ⊕ V_{t,A}` with independent cutoffs `Ks, KmB, KmA, KtB, KtA` and both explicit channel residuals). |
| `ex:ch21-pair-residual` (`-i/4` intermediate residual witness at `h=2`), `rem:ch21-pair-enlarged-target` | **Phase B (`ex:ch21-pair-residual` Proved)** (`singletResidualWitnessConfig`, `singletResidualWitnessKet`, `singletResidualWitnessKet_mem_target`, `singletResidualWitnessVec`, `singlet_pair_residual_comp_zero_h2`, `singlet_pair_residual_witness_h2`, `singlet_pair_residual_ne_zero_h2`) | **Proved (`ex:ch21-pair-residual`):** Constructively proves `⟨Ξ, (B_{a,1} ∘ B_{b,1}) Ω₀⟩ = 0` and `⟨Ξ, R₁ Ω₀⟩ = -i/4 ≠ 0` at `h = 2, J_s = 0, J_{m,1} = 0, J_{t,1} = 1`. |

### 4.3 Section 21.3 — Umklapp Scattering, Charge-Sector Leakage, and Finite Projection ([`21.3.tex`](../../../notes/latex/chapters/sections/21.3.tex))

| LaTeX Claim / Equation | Lean Realization & Tier | Coverage & Gap Notes |
| :--- | :--- | :--- |
| `def:ch21-u-word`, `prop:ch21-u-selfadjoint` ($H_U^\dagger = H_U$) | **Phase B** (`umklappForwardSite`, `umklappBackwardSite`, `umklappOp`, `periodicUmklappOp`, `umklappOp_self_adjoint`) | **Proved.** |
| `lem:ch21-u-fundamental-commutators`, `thm:ch21-u-charge-shift` (charge shift `(+1,+1,-1,-1)`, `Q_c, Q_s, J_s` conservation, `J_c ∓ 4`), `cor:ch21-u-sector-compression` | **Phase B** (`umklappForwardSite_charge_commutator`, `umklappBackwardSite_charge_commutator`, `umklapp_quantum_number_shifts`, `umklappForwardSite_maps_sector`, `umklappBackwardSite_maps_sector`, `umklappOp_charge_diagonal_zero`) | **Proved.** |
| `def:ch21-u-charge-box`, `thm:ch21-u-leakage` (general per-species charge box $\mathcal{B}_{K,\mathbf{B}}$ leakage) | **Partial in Phase B** (`speciesChargeBoxSet`, `speciesChargeBox`, `speciesChargeBoxProjection`, `umklapp_zero_budget_not_invariant` for `jointBudget h 0 K`) | **Partial Gap:** Per-species charge box $\mathcal{B}_{K,\mathbf{B}}$ and projector $P_{K,\mathbf{B}}$ are now defined (and instantiated in `ex:ch21-u-inward-only`), and zero-charge budget leakage is proved; general conditional outward leakage `[P_{K,\mathbf{B}}, H_U] ≠ 0` remains optional future work. |
| `thm:ch21-u-zero-box-witness` (`-g_U / L^2` = `-g_U / (2h)^2`), `ex:ch21-u-four-site` (`-1/16` at `h=2`) | **Phase B** (`umklappZeroChargeWitness`, `umklapp_zero_charge_witness_coeff`, `umklapp_witness_h2_coeff`, `umklapp_witness_h1_coeff`, `umklapp_zero_budget_not_invariant`) | **Proved.** |
| `ex:ch21-u-inward-only` (Pauli-blocked `h=2` inward-only state `|S⟩`, `g_U/16`) | **Phase B** (`umklappInwardBoxBounds`, `umklappInwardSourceCharge`, `umklappInwardSourceConfig`, `umklappInwardSourceKet`, `umklappInwardSourceKet_mem_box`, `umklappInwardTargetSpeciesConfig`, `umklappInwardTargetConfig`, `umklappInwardTargetKet`, `umklappInward_outward_pauli_blocked`, `umklappInward_coeff_h2`, `umklappInward_mem_box_h2`, `umklappInward_no_leakage_h2`) | **Proved:** Pauli blocking `O_U(x) |S⟩ = 0`, exact inward matrix element `⟨T', H_U(g_U) S⟩ = g_U/16`, and for `g_U ≠ 0`, `H_U |S⟩ ≠ 0` with zero leakage `(I - P_{16,B}) H_U |S⟩ = 0`. |
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
2. **Tooling Hygiene (RESOLVED in `[V1-S9-U4]`):**
   - `scripts/webllm/audit_axioms.py` now filters `private` declarations (`is_private_decl` / `exported_declarations`) and is covered by unit tests in `scripts/webllm/test_audit_axioms.py`; `audit_axioms.py BosonizeStubs/Ch21SpinfulModels.lean` exits `0` (`148/148` exported declarations on standard axioms).
3. **Pedagogical Sync (`21.1.tex`–`21.3.tex`, `notes/md/ch21_spinful_models.md`):**
   - Once Phase C promotion occurs, update the stale `2026-10-17` disclaimers in `21.1.tex` (L799–802), `21.2.tex` (L626–628), and `21.3.tex` (L655–658) so they accurately distinguish:
     - **Verified finite-CAR Ch21 results** (spin-charge currents + `prop:ch21-global-edge`, parity sublattice, combined `W = V_{t,B} ⊕ V_{t,A}` singlet projection `thm:ch21-pair-projected`, Umklapp selection rules & `B4` witness, concrete `h = 2` witnesses `ex:ch21-pair-sign`, `ex:ch21-pair-residual`, `ex:ch21-u-inward-only`, and Core `A10` discrete SW), from
     - **Unformalized continuum/RG & future finite-bridge items** (`prop:ch21-continuum-charge-spin-decoupling`, `thm:ch21-cocycle-identity`, `thm:ch21-umklapp-spin-cancel`, `thm:ch21-scaling-dimension-mott`, `prop:ch21-sw-analytic-remainder`).
