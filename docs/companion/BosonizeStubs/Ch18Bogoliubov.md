# BosonizeStubs/Ch18Bogoliubov.lean

- Scalar review notebook tasks:
  - check that `luttingerG`, `luttingerGInv`, `g u = v1 - v2`, `g⁻¹ u = v1 + v2`, and `2us^2 = v1 - u` use only `HyperbolicParams` fields and never a hidden sign choice;
  - verify that `v2 = 0 ↔ s = 0` and `u < v1` really require the stated positivity hypotheses.
- Operator review notebook tasks:
  - expand the inverse transform with exact branch labels and signs;
  - derive the finite-sum dressed oscillator identity from the frozen per-mode theorem `A07Interactions.bogoliubov_expansion_on_budget` rather than from ad hoc commutation hypotheses;
  - combine that sum with `Ch17.luttinger_hamiltonian_on_budget` for the full Chapter 17 statement.
- Witness notebook tasks:
  - evaluate the explicit witness `(17,15,8,5/4,3/4)`;
  - confirm `Ch17.v1Velocity 1 (32π) = 17` and `Ch17.v2Velocity (30π) = 15`;
  - check `vacuumShiftScalar 8 2 8 (3/4) = 27π/8` and hence nonzero;
  - inspect that the dressed lowering action on the finite ground ket is nonzero because it lands on an explicit `Ch16.excitedKet` witness, not because a global dressed vacuum is assumed.
- SW review notebook tasks:
  - cite Core results `A10.energy_shell_discards_double_mode_one` and `A10.sw_off_zero_implies_effective_exact` when discussing shell projection;
  - keep the shell-vs-mode-decimation distinction conceptual and separate from the Bogoliubov diagonalization proof obligations above.

- Phase B review tasks added at Phase B start (review warning CH18-N15):
  - `tanh_relation_of_params`: with `cosh 2ξ = c² + s²` and `sinh 2ξ = 2cs`, check that `v2 (c² + s²) = v1 (2cs)` is the cross-multiplied form of `tanh 2ξ = v2 / v1` and needs no division by `v1`; witness `(c, s) = (5/4, 3/4)` gives `c² + s² = 17/8`, `2cs = 15/8`, and `15 · 17/8 = 17 · 15/8`.
  - `luttingerG_eq_sqrt_of_params`: `g = (c − s)²`; check that `v1 + v2 > 0` follows from the stability field `|v2| < v1` so the square root argument is well defined; witness `g = (1/2)² = 1/4 = √((17 − 15)/(17 + 15)) = √(1/16)`.
  - `luttingerGInv_eq_inv`: `(c + s)² (c − s)² = (c² − s²)² = 1`, so `luttingerGInv = g⁻¹` for every `HyperbolicPair` (no positivity needed); witness `4 = (1/4)⁻¹`.
  - `hyperbolic_coeff_eq_luttinger`: `c² + s² = (g + g⁻¹)/2` from `(c − s)² + (c + s)² = 2(c² + s²)`; witness `17/8 = (1/4 + 4)/2`.
  - `HyperbolicPair.inverse_combination`: `c(cX + sY) − s(cY + sX) = (c² − s²)X = X` on any complex module; compare the `X`/`Y` placement with the branch pairing in `A07Interactions.bogoliubovAnnihilator` / `bogoliubovCreator` before using it to invert the transform.
  - `bogoliubov_cross_annihilator_annihilator_on_budget`: expand `[Ã_R, Ã_L]` into four density commutators; check that the cross-species terms vanish by `A05.rho_cross_commute`, that the two same-branch terms cancel on the budget (opposite chiralities), and record which part of `A06.branchMargins` supplies the margin for indices `±m`.

Phase A integrated after user review. Theorems remain unproved.


Phase A finish evidence: `note/webllm/ch18/phaseA-ch18_cycle_a_6c99dd27.md`.
