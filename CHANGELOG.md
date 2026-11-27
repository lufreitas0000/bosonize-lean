# Changelog (Units of Work) — bosonize-lean

All notable changes and conceptual evolutions are recorded here per Unit of Work (`PG-10` + Rule 06).

## [Unreleased]

### [2026-11-27] [QMB-P1C-02] [Actor: Blue Orchestrator (`gemini-pro-orchestrator-neon`)] — Freeze All `15` Unbaselined CoupledWire & Ch21 Modules in `docs/spec/stub_locks.v2.json` (`make lock-check` & `./scripts/ci.sh` Strict Closure)
#### Ideas & Contracts Evolved
- Executed Phase 1C Priority 7 (`QMB-P1C-02`, branch `chore/qmb-p1c-02-ch21-stub-locks` stacked linearly off `refactor/qmb-p1b-04b-coupled-wire-port @ b813c5aa0d2f` per `R38-01`), auditing and freezing all `15` previously unbaselined modules in `docs/spec/stub_locks.v2.json` via `env -u CI python3 -B scripts/guards/stub_lock.py --update` **without** `--accept-changes`:
  - **Zero mutation to frozen V1 baseline:** All `44` prior V1 Core entries (`1,317` headers, `1,394` frozen commands), `docs/spec/core_locks.json` (`54/54` complete Core SHA-256 hashes), and every `.lean` source file across `Bosonize/`, `BosonizeStubs/`, and `BosonizeLab/` remain `100%` byte-for-byte untouched.
  - **15 newly locked modules (`+528` headers, `+443` frozen commands -> `59` files, `1,845` locked declaration headers, `1,837` frozen commands total):**
    - `10` `Bosonize/Core/CoupledWire*.lean` modules (`+225` headers, `+250` frozen commands; `0` `sorry`/`admit`/`axiom`/`native_decide`/`set_option`/`whole` fallbacks).
    - `5` `BosonizeStubs/Ch21*.lean` Phase B staging modules (`+303` headers, `+193` frozen commands; `0` `sorry`/`admit`/`axiom`/`native_decide`/`set_option`/`whole` fallbacks), frozen strictly in-place inside `BosonizeStubs/` (`_is_lab_lean == True`) while keeping promotion into `Bosonize/Core/` human-gated Phase C.
- Verified strict lock and full CI compliance under `PATH="$HOME/.elan/bin:$PATH"`: `make lock-check` (`stub_lock.py --check --strict` + `core_lock.py`), `./scripts/ci.sh` (`CI OK`: `69/69` guard tests, strict `stub_lock`, `54/54` `core_lock`, `lake build Bosonize`, `lake build BosonizeStubs`, `20/20` `webllm` tests), `lake build BosonizeLab`, `uow.py check --repo bosonize-lean` & `--state qmb` (`12/12 PASS`), and `repo_governance_gate.py` (`0` errors).
- Synced Front-3 & Four-Record documentation (`KNOWLEDGE_MAP.md`, `PROJECT_STATE.yaml` registering `T4`, `CURRENT_SPRINT.md`, `CHANGELOG.md`) to reflect the two-layer cryptographic lock contract (`stub_locks.v2.json` + `core_locks.json`).

#### Code & Artifacts Changed
- Updated `docs/spec/stub_locks.v2.json`, `KNOWLEDGE_MAP.md`, `PROJECT_STATE.yaml`, `CURRENT_SPRINT.md`, and `CHANGELOG.md` (`0` `.lean` files edited).

### [2026-11-27] [QMB-P1B-04b] [Actor: Blue Orchestrator (`gemini-pro-orchestrator-neon`)] — Consolidate All 5 MAM Coupled-Wire Duality Modules onto Pinned Mathlib4 (`Bosonize/Core/CoupledWire/` + `BosonizeLab/`)
#### Ideas & Contracts Evolved
- Executed Phase 1B Priority 4 Step 2 (`QMB-P1B-04b`, branch `refactor/qmb-p1b-04b-coupled-wire-port` off `main @ 1fc35e8`), porting all 5 Mross–Alicea–Motrunich (`arXiv:1510.08455`) coupled-wire duality modules from `xxz-benchmark/lean/XXZBenchmark/` (`5,978` zero-Mathlib LOC) onto pinned Mathlib4 (`v4.35.0-rc4`: `GaussianInt`, `Matrix`, `Matrix.det`, `Matrix.fromBlocks`, `Finset.sum`, `Polynomial`) with zero wheel reinventions and full `1.81x` compression:
  - **9 cohesive Core modules + thin barrel (`3,303` LOC, max `449 <= 450` LOC, `214` public theorems/lemmas, `100` defs/structures):** `DualityMatrix` (`325`), `DualityBoundary` (`304`), `DiracMass` (`421`), `SSHZeroModes` (`373`), `BlochDiracAndGauge` (`447`), `GaugeAndConductivity` (`449`), `TPfaffianThreeCone` (`447`, including characteristic-free universal `det_fromBlocks_scalar_diag` over `[Fintype m] [CommRing R]` and the exact `-4` exponent at wire `3y+2` correcting MAM App. 4 Eq. (63)), `QED3Duality` (`192`, including universal `[Fintype ι] [CommRing R]` Euclidean `transProj`), `N2BosonicTI` (`318`, preserving `sgn(y - y')` correcting MAM App. 11), and barrel `CoupledWire.lean` (`27`).
  - **Quarantined witness library (`BosonizeLab`, `205` LOC, `20` concrete theorems):** Added `BosonizeLab` in `lakefile.toml`, thin `BosonizeLab.lean`, and `BosonizeLab/Lab/CoupledWire/CoupledWireWitnesses.lean` (`203` LOC, `_is_lab_lean == True`) isolating all `N_y = 3, 4, 5, 6` / `Fin 2..4` / `decide` non-vacuity witnesses and refutations so Core has `0` Rank-0 regressions.
- Preserved all `44` original frozen V1 `Bosonize/Core/*.lean` files, all `5` `BosonizeStubs/Ch21*.lean` files, and `docs/spec/stub_locks.v2.json` byte-for-byte untouched; registered SHA-256 hashes of the `10` new `Bosonize/Core/CoupledWire*.lean` files in `docs/spec/core_locks.json` (`54/54` verified by `core_lock.py`). Directly unblocks Round 32 `QMB-P1B-04c` full retirement of `xxz-benchmark/lean/` (`-9,114` LOC).

#### Code & Artifacts Changed
- Added `Bosonize/Core/CoupledWire.lean`, `Bosonize/Core/CoupledWire/{DualityMatrix,DualityBoundary,DiracMass,SSHZeroModes,BlochDiracAndGauge,GaugeAndConductivity,TPfaffianThreeCone,QED3Duality,N2BosonicTI}.lean`, `BosonizeLab.lean`, and `BosonizeLab/Lab/CoupledWire/CoupledWireWitnesses.lean`; updated `Bosonize.lean`, `lakefile.toml`, `docs/spec/core_locks.json`, `KNOWLEDGE_MAP.md`, `PROJECT_STATE.yaml`, `LOG_DISCOVERY_AND_PIVOTS.md`, and `CHANGELOG.md`.

### [2026-11-25] [QMB-DOC-06a] [Actor: Blue Orchestrator (`gemini-pro-orchestrator-neon`)] — Author 3-Pillar `KNOWLEDGE_MAP.md` (`6/10` QMB Coverage)
#### Ideas & Contracts Evolved
- Added repository-root [`KNOWLEDGE_MAP.md`](KNOWLEDGE_MAP.md) (QMB Round 12 `QMB-DOC-06a`, branch `doc/qmb-doc-06a` from `main @ edc6eb4`), synthesizing: (1) the four strictly separated finite-CAR / polynomial-CCR / formal-series / analytic-limit carriers and `BL-1` quantitative product residuals (`V1S6PhysicalFields`) plus Ch21 $\mathbb{Z}^4$ Klein 2-cocycle (`epsZ4`, `fourKleinOp`, `fourKleinMod2Op`), off-margin counterexample, graded budget direct sum, and unital `CStarRing` analytic Schrieffer–Wolff remainder; (2) the live layer & lock contract map (`44/44` SHA-256-locked `Bosonize/Core/` modules [`31,712` LOC, `1,270` theorem/lemma declarations] + `5/5` Ch21 Phase B `BosonizeStubs/` modules [`6,867` LOC, `383/383` audited exported declarations with `5/5` mirrored companions] + `21` chapters / `7` appendices in `notes/latex/`); and (3) active cross-repo `HC-QMB-09`, `HC-QMB-02`, and `qed3-duality` interfaces alongside human-gated Phase C / V2 deferrals.
- Preserved strictly `0` edits across all `.lean` files (`Bosonize/Core/`, `BosonizeStubs/`), `docs/spec/core_locks.json`, `docs/spec/stub_locks.v2.json`, `docs/`, `notes/`, `scripts/`, and `LOG_DISCOVERY_AND_PIVOTS.md`.

#### Code & Artifacts Changed
- Added `KNOWLEDGE_MAP.md`; updated `CHANGELOG.md` and `PROJECT_STATE.yaml`.

### [2026-11-21] [V1-S9-U8] [Actor: Antigravity] — Wave 38 V1-S9 Companion Closure & Audit Reconciliation (`Ch21CocycleAndLeakage.md`, `Ch21AnalyticSWCore.md`)
#### Ideas & Contracts Evolved
- Completed mirrored companion documentation for the remaining two Ch21 Phase B staging modules, bringing Ch21 mirrored companion coverage to `5/5` modules (`383/383` exported declarations documented):
  - `docs/companion/BosonizeStubs/Ch21CocycleAndLeakage.md`: documents all `114` exported declarations (`77` proofs: `31` `theorem`s + `46` `lemma`s; `37` data/instance commands: `30` `def`s + `2` `abbrev`s + `1` `structure` + `4` `local instance`s; `0` `private lemma`s) with exact signatures, explicit hypotheses, and LaTeX correspondence to `21.1.tex` and `21.3.tex`.
  - `docs/companion/BosonizeStubs/Ch21AnalyticSWCore.md`: documents all `25` exported declarations (`18` proofs: `7` `theorem`s + `11` `lemma`s; `7` `def`s; plus `3` file-local `private lemma`s) of the pure-Mathlib leaf `module` with exact hypotheses and LaTeX correspondence to `21.4.tex`.
- Reconciled `docs/plans/v1-s9/v1_release_readiness_audit.md` (frontmatter `depends_on`, Section 1, and Section 3), `PROJECT_STATE.yaml`, `LOG_DISCOVERY_AND_PIVOTS.md`, and `CHANGELOG.md` while keeping `.lean` files, `Bosonize/`, `BosonizeStubs/`, `core_locks.json`, `docs/spec/stub_locks.v2.json`, and `notes/latex/` untouched and Phase C promotion human-gated.

#### Code & Artifacts Changed
- Added `docs/companion/BosonizeStubs/Ch21CocycleAndLeakage.md` and `docs/companion/BosonizeStubs/Ch21AnalyticSWCore.md`; updated `docs/plans/v1-s9/v1_release_readiness_audit.md`, `PROJECT_STATE.yaml`, `LOG_DISCOVERY_AND_PIVOTS.md`, and `CHANGELOG.md`.

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
