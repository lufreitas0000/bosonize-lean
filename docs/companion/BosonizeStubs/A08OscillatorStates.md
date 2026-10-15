# BosonizeStubs/A08OscillatorStates.lean

- Carrier review tasks:
  - verify polynomial pairing well-foundedness and non-degeneracy (`oscPairing_self_eq_zero`);
  - check that `oscWeight` values are strictly positive ($m = i.val + 1 \ge 1$) so no infinite-dimensional slice is created;
  - confirm adjointness `oscCreation_pairing_adjoint` and commutator $[A, C] = m I$ algebraically on polynomials.
- State and automorphism review tasks:
  - trace $\omega_0$ definition as vacuum state evaluation $\langle 1, \pi(a) 1 \rangle$;
  - verify that $\beta_{c,s}$ satisfies $(c^2 - s^2 = 1) \iff \beta_{c,s} \circ \beta_{c,-s} = \text{id}$ on non-empty mode sets (`bogoliubovMap_inverse_iff`);
  - verify the pullback direction $\omega_P = \omega_0 \circ \beta_{c,-s}$ so that dressed lowering operators annihilate the vacuum, and $\omega_P \circ \beta_{c,s} = \omega_0$ (`omegaP_comp_bogoliubovMap`);
  - confirm full quotient descent on all relation pairs: $[A, C] - m I$, $[A, A]$, and $[C, C]$ for both bare $\omega_0$ and dressed $\omega_P$;
  - confirm that the non-multiplicativity witness $\omega_P(A C) - \omega_P(C A) = m$ holds without assuming states are homomorphisms.
- Contraction review tasks:
  - calculate both same-branch contractions: $m s^2$ for $CA$ and $m c^2$ for $AC$;
  - check that $c^2$ remains non-zero even when $s = 0$ (free vacuum fluctuations);
  - check that cross-branch contractions have the exact $-\delta_{ij} m c s$ sign, sensitive to $\beta$ direction.
- Correlation kernel review tasks:
  - verify that $D(x,y) = L^{-2} \sum m (s^2 \zeta^{-md} + c^2 \zeta^{md})$ preserves the ordered observable and does not collapse into a cosine;
  - verify that the commutator expectation $D(x,y) - D(y,x)$ matches the $(1, -1)$ Schwinger kernel;
  - check diagonal positivity $0 < (D(x,x)).re$ under the required condition $\zeta \neq 0$ for $h > 0$ and $M \ge 1$.
- Compressed vacuum review tasks:
  - confirm $Q_R^\dagger Q_R + Q_L^\dagger Q_L = \operatorname{diag}(2s^2, c^2, c^2)$ matrix identity;
  - confirm that $s \neq 0$ implies strict positivity and trivial common kernel $\{0\}$;
  - confirm that $s = 0$ admits non-trivial kernel $(1, 0, 0)^T$, showing necessity of $s \neq 0$ for obstruction.
- Witness review tasks:
  - verify arithmetic of all conjuncts in `concrete_correlation_witness` via `norm_num`;
  - check that Fock ground state expectation $\langle \Omega, \tilde{C}_R \tilde{A}_R \Omega \rangle = 9/8 \neq 0$ witnesses that the bare Fock vacuum is not the interacting dressed vacuum.

Phase A integrated after user review. Theorems remain unproved.


Phase A finish evidence: `note/webllm/ch19/phaseA-ch19_cycle_a_e7c404b4.md`.


Phase B finish evidence: `note/webllm/ch19/phaseB-ch19_cycle_b_ac6d6ccf.md`.
