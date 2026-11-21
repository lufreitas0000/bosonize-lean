# Changelog (Units of Work) — bosonize-lean

All notable changes and conceptual evolutions are recorded here per Unit of Work (`PG-10` + Rule 06).

## [Unreleased]

### [2026-11-21] [V1-S9-U7] [Actor: Antigravity] — Formalize Ch21 Finite Analytic Schrieffer–Wolff Remainder, `2×2` Witness & Umklapp Block Norm Bound (`Ch21AnalyticSWCore.lean`, `Ch21AnalyticRemainder.lean`)
#### Ideas & Contracts Evolved
- Added leaf `module` `BosonizeStubs/Ch21AnalyticSWCore.lean` (`558` lines, `25` exported declarations [`18` proofs + `7` data]) and non-`module` `BosonizeStubs/Ch21AnalyticRemainder.lean` (`795` lines, `33` exported declarations [`24` proofs + `9` data/instance commands]), closing `prop:ch21-sw-analytic-remainder` and `ex:ch21-sw-two-level` (`21.4.tex`) with `0` `sorry`, `0` warnings under `lake --wfail build BosonizeStubs`, standard axioms only (`58/58` exported declarations via `audit_axioms.py`), and independent W4 `Carbon` Pass-2 `ACCEPT`:
  - **Banach / unital `CStarRing` Taylor remainder (`Ch21AnalyticSWCore.lean`):** Proved FTC integral remainder `swRemainder3_integral` (`eq:ch21-sw-integral-remainder`), unitary invariance `norm_exp_smul_skew_eq_one` / `swAdjointFlow_norm_eq` for skew-Hermitian `S₁`, orthogonal projection contraction `norm_ortho_proj_le_one`, and norm bound `‖P R₃(t) P‖ ≤ ‖R₃(t)‖ ≤ |t|³ (‖ad_{S₁}³ H₀‖/6 + ‖ad_{S₁}² V‖/2)` (`swRemainder3_norm_bound`, `swCompressed_exact_plus_remainder_and_bound`).
  - **Explicit `2×2` witness (`ex:ch21-sw-two-level`, `Ch21AnalyticRemainder.lean`):** Proved `S₁² = -I`, closed trigonometric `exp(t S₁)`, rotated entry `sin² t - t sin(2t)` (`eq:ch21-sw-2x2-rotated`), off-diagonal `t cos(2t) - (1/2) sin(2t)`, exact eigenvalues `(1 ± √(1+4t²))/2`, finite-coupling discrepancy `-1/3 ≠ -4/9` at `t = 2/3`, and explicit `(8/3)|t|³` `L2Operator` bound.
  - **`Ch21 → A10` Umklapp block analytic bound:** Bridged `umklappBlock_a10_bch_bridge` to `A05.FockSpace` bounded operators (`toFockCLM`), proving `‖V‖ = |g_U|/(4h²)` and `‖P R₃(t) P‖ ≤ |t|³ |g_U|³ / (96 h⁸)` (`|t|³ |g_U|³ / 24576` at `h = 2`).
- Updated `docs/companion/BosonizeStubs/Ch21AnalyticRemainder.md` and `docs/plans/v1-s9/v1_release_readiness_audit.md` (`383` total Ch21 exported declarations across `5` Phase B files awaiting human Phase C review); preserved `Bosonize/Core/*` (`44` files), `core_locks.json`, `stub_locks.v2.json`, and `notes/latex/` untouched.

#### Code & Artifacts Changed
- Added `BosonizeStubs/Ch21AnalyticSWCore.lean`, `BosonizeStubs/Ch21AnalyticRemainder.lean`, and `docs/companion/BosonizeStubs/Ch21AnalyticRemainder.md`; updated `docs/plans/v1-s9/v1_release_readiness_audit.md`, `LOG_DISCOVERY_AND_PIVOTS.md`, `PROJECT_STATE.yaml`, and `CHANGELOG.md`.

### [2026-11-20] [V1-S9-U6] [Actor: Antigravity] — Formalize Ch21 Graded Budget vs. Product Cutoff, General-$h$ Singlet Klein Sign, Intermediate-State SW Formula & `Ch21 → A10` Bridge (`Ch21BudgetAndSWBridge.lean`)
#### Ideas & Contracts Evolved
- Added new Phase B staging module `BosonizeStubs/Ch21BudgetAndSWBridge.lean` (`import BosonizeStubs.Ch21CocycleAndLeakage`, `1,664` lines, `63` exported audited declarations [`36` proofs: `19` `theorem` + `17` `lemma`; `27` data/instance commands: `23` `def` + `4` `local instance`], `0` `sorry`, `0` warnings under `-DwarningAsError=true`, standard axioms only via `audit_axioms.py`, independent W4 `Carbon` `ACCEPT`):
  - **Graded direct-sum decomposition vs. product cutoff (`eq:ch21-budget-energy-sum`, `eq:ch21-not-product-cutoff`):** Formalized `gradedSectorSpace` and `productCutoffSpace`, proved orthogonal internal direct-sum equivalence `jointBudget_eq_graded_sum` (`gradedSectorSpace_orthogonal`, `gradedSectorSpace_iSupIndep`) for all `0 < h`, and constructively proved `k1_product_cutoff_strict_superset` (`A05.jointBudget h 0 1 < productCutoffSpace h 0 1` via `k1DoubleExciteKet` having species cost `1` each and total cost `2`).
  - **General-$h$ singlet Klein-product sign (`eq:ch21-pair-general-sign`):** Proved `singlet_klein_product_sign_eq` and `singlet_pair_general_sign` for ALL `0 < h` and `x : Fin (2 * h)`, establishing exact ground-to-ground amplitudes `+(-1)^{h+1}/(2h)` on $\Omega_{T_B}$ and `-(-1)^{h+1}/(2h)` on orthogonal $\Omega_{T_A}$ (specializing to `∓1/4` at `h = 2` in `singlet_pair_general_sign_h2`).
  - **Intermediate-state SW formula & `Ch21 → A10` block bridge (`prop:ch21-sw-intermediate`):** Proved explicit `I_Q`-filtered sum-over-states formulas `sw_second_order_intermediate_sum`, `sw_second_order_diagonal_shift`, and `sw_second_order_diagonal_nonpos_of_ordered`, plus both matrix-level (`umklappBlock_sw_generator_and_shift`, `umklappBlock_sw_h2`) and operator-level (`umklappBlock_a10_bch_bridge`, `umklappBlock_a10_bch_bridge_h2`) bridges instantiating `A10.sw_compressed_bch_second_order` on `A05.Operators SpinBranch h` with `W^{(2)}_{00} = -g_U²/(32h⁵)` (`-g_U²/1024` at `h = 2`).
- Preserved `Bosonize/Core/` (`44` Core files intact), `Ch21SpinfulModels.lean`, `Ch21CocycleAndLeakage.lean`, `BosonizeStubs.lean`, `core_locks.json`, `docs/spec/stub_locks.v2.json`, and `notes/latex/` untouched.

#### Code & Artifacts Changed
- Added `BosonizeStubs/Ch21BudgetAndSWBridge.lean` and `docs/companion/BosonizeStubs/Ch21BudgetAndSWBridge.md`; updated `LOG_DISCOVERY_AND_PIVOTS.md`, `CHANGELOG.md`, and `PROJECT_STATE.yaml`.

### [2026-11-20] [V1-S9-U5] [Actor: Antigravity] — Formalize Ch21 $\mathbb{Z}^4$ Klein 2-Cocycle, Off-Margin Counterexample, Spinful Hyperbolic Diagonalization, and General Charge-Box Leakage (`Ch21CocycleAndLeakage.lean`)
#### Ideas & Contracts Evolved
- Added new Phase B staging module `BosonizeStubs/Ch21CocycleAndLeakage.lean` (`import BosonizeStubs.Ch21SpinfulModels`, `1,226` lines, `77` exported proofs [`46` lemmas + `31` theorems] + `37` data/instance commands = `114` audited declarations, `0` `sorry`, `0` warnings under `-DwarningAsError=true`, standard axioms only via `audit_axioms.py`):
  - **Standalone $\mathbb{Z}^4$ Klein 2-cocycle & four-species Klein operators (`thm:ch21-cocycle-identity`, `def:ch21-four-klein`, `prop:ch21-klein-anticommute`):** exact `epsZ4` 2-cocycle law in $\mathbb{Z}$ and $\mathbb{C}$, projective shift representation `cocycleShift_mul`, unitary $F_i = P_{<i} T_i$ on $\mathbb{C}^{(\mathbb{Z}^4)}$ with `fourKleinOp_unitary_left/right`, `{F_i, F_j} = 0`, `{F_i, F_j†} = 0`, `[N_i, F_j] = -δ_{ij} F_j`, plus finite $\mathbb{Z}_2^4$ Clifford involution operators `fourKleinMod2Op` (`K_i² = I`, `K_i K_j = -K_j K_i`, intertwined by `chargeParityQuotient_intertwines`).
  - **First-mode & off-margin commutator counterexample (`ex:ch21-first-mode`, `eq:ch21-off-margin-example`, `eq:ch21-compression-residual`):** first-mode commutators for `h ≥ 2` (`h = 2`), explicit off-margin ket `offMarginKetL` proving `[R^c_{L,-1}, R^s_{L,1}] v = -v ≠ 0` and global non-commutativity `[R^c_{L,-1}, R^s_{L,1}] ≠ 0` for all `h ≥ 2`, plus the exact compressed-commutator residual identity `[PAP, PBP] = P[A,B]P - PAQBP + PBQAP`.
  - **Spinful charge/spin hyperbolic quadratic block diagonalization (`prop:ch21-quadratic-block`, `eq:ch21-asymmetry-mixes`, `eq:ch21-bogoliubov-dynamic`, `eq:ch21-hyperbolic-parameters`, `ex:ch21-equal-speeds`):** ordered noncommutative block diagonalization, spin-asymmetry mixing identity, independent charge `(u_c, K_c)` and spin `(u_s, K_s)` hyperbolic diagonalization reusing `A07Interactions.HyperbolicParams` & `Ch17.v1Velocity`/`v2Velocity` under `|g_{2,ν}| < 2π v_F + g_{4,ν}`, `2×2` Bogoliubov dynamical-matrix diagonalization `B M B⁻¹ = diag(u, -u)`, speed non-degeneracy equivalence, equal-speed witness (`u_c = u_s = v`), and contrast witness (`u_c = 8 ≠ 5 = u_s`).
  - **General per-species charge-box Umklapp leakage (`thm:ch21-u-leakage`):** proved outward and inward conditional leakage (`umklapp_charge_box_outward_leakage`, `umklapp_charge_box_inward_leakage`, `umklapp_charge_box_basis_leakage`, `umklapp_zero_box_commutator_ne_zero`) yielding `H_U ψ ∉ ℬ_{K,B}` and `[P_{K,B}, H_U] ≠ 0` whenever a definite-charge box state or basis ket has a nonzero Umklapp step exiting any species charge bound `±B_ν`.
- Preserved `Bosonize/Core/`, `BosonizeStubs/Ch21SpinfulModels.lean`, `BosonizeStubs.lean`, `core_locks.json`, `docs/spec/stub_locks.v2.json`, and `notes/latex/` untouched; recorded expected `stub_lock.py --strict` exit `1` for unbaselined Phase B staging files pending human Phase C promotion.

#### Code & Artifacts Changed
- Added `BosonizeStubs/Ch21CocycleAndLeakage.lean`; updated `docs/plans/v1-s9/v1_release_readiness_audit.md`, `CHANGELOG.md`, `LOG_DISCOVERY_AND_PIVOTS.md`, and `PROJECT_STATE.yaml`.

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
