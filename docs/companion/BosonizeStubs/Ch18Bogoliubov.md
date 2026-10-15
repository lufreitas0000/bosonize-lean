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

Phase A integrated after user review. Theorems remain unproved.


Phase A finish evidence: `note/webllm/ch18/phaseA-ch18_cycle_a_6c99dd27.md`.
