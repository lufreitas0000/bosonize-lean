### Chapter 19: Exact Correlation Functions

To calculate physical observables, we evaluate correlation functions algebraically. The formalization of states and correlators follows [Appendix A08](../appendices/a08_states_and_correlations.md).

#### 19.1 The Interacting Vacuum and Algebraic States

**Definition 19.1 (Algebraic State Functional).**
An abstract positive state $\omega_{\tilde{\Omega}}$ on the algebra of observables $\mathfrak{A}_{\mathcal{B}}$ is a normalized functional ($\omega(I)=1$). To model the quasi-free Luttinger ground state, we specify it as a state annihilated by the dressed lowering modes:
$$
\forall A, \quad \omega_{\tilde{\Omega}}(A \cdot \tilde{\rho}_{-m, \nu}) = 0 \quad \text{and} \quad \omega_{\tilde{\Omega}}(\tilde{\rho}_{m, \nu} \cdot A) = 0 \tag{19.1}
$$
*(Note: As proven in A08, a finite matrix algebra may not possess a true vacuum for these exact conditions if the budget is strictly truncated. In Lean, we can define $\omega$ formally as an abstract quasi-free functional on the untruncated CCR word algebra before applying it to finite-Fock evaluations).*

#### 19.2 Algebraic Evaluation of the Mode Correlators

By substituting the Inverse Bogoliubov transformation (Lemma 18.3) into the functional, we evaluate the bare mode correlations.

**Theorem 19.2 (Exact Interacting Mode Correlators).**
For $m, n \ge 1$:
$$
\omega_{\tilde{\Omega}}(\rho_{m, R} \rho_{-n, R}) = \delta_{mn} \cdot m \cdot s^2 \tag{19.2}
$$
$$
\omega_{\tilde{\Omega}}(\rho_{-m, R} \rho_{n, R}) = \delta_{mn} \cdot m \cdot c^2 \tag{19.3}
$$
The second equation supplies the non-zero free-vacuum fluctuation even when $s=0$ (since $c^2 - s^2 = 1 \implies c^2 = 1$). Both mode contractions are rigorously required.

#### 19.3 Real-Space Spatial Correlators

**Definition 19.3 (Spatial Density Operator).**
The bare spatial density for a branch is the exact finite Fourier sum up to cutoff $M$:
$$
\rho_R(x) := \frac{1}{L} \sum_{m=1}^{M} \left( \zeta^{-mx} \rho_{m, R} + \zeta^{mx} \rho_{-m, R} \right) \tag{19.4}
$$

**Theorem 19.4 (Exact Spatial Density Correlator).**
Expanding the product $\rho_R(x)\rho_R(y)$ and applying Theorem 19.2, the anomalous contractions $\omega(\rho_m \rho_n)$ vanish, yielding the exact ordered two-point function:
$$
D_c(x, y) := \omega_{\tilde{\Omega}} (\rho_R(x) \rho_R(y)) = \frac{1}{L^2} \sum_{m=1}^{M} m \left( s^2 \zeta^{-m(x-y)} + c^2 \zeta^{m(x-y)} \right) \tag{19.5}
$$
If we evaluate the symmetrized correlator $\frac{1}{2}\omega(\{\rho_R(x), \rho_R(y)\})$, the $c^2$ and $s^2$ terms combine symmetrically to $(c^2+s^2) \cos(\dots)$, reflecting the Luttinger parameter $K_L$. However, the strictly ordered correlator uniquely preserves the exact $c^2, s^2$ distinction required to match the finite vacuum variance.

#### 19.4 Technical Notes for the Lean 4 Formalization

1. **Explicit Finite Kernels:**
   * Prove finite character-sum formulas explicitly. A periodic finite sum does not establish a power-law decay theorem automatically.
   * If continuum asymptotics are required, specify the scaling variables and limiting sequence in a completely separate analytic module. Do not use $\propto$ to hide finite regulator dependence.
2. **Two-Point Contractions:**
   * Apply the functional linearity `map_add` and both the $c^2$ and $s^2$ evaluations. Do not omit the free-vacuum fluctuations.
