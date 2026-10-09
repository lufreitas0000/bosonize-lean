### Chapter 19: Exact Correlation Functions

To calculate physical observables, we evaluate correlation functions algebraically. The formalization of states and correlators follows [Appendix A08](../appendices/a08_states_and_correlations.md).

#### 19.1 The Interacting Vacuum and Algebraic States

**Definition 19.1 (Algebraic State Functional).**
An abstract positive state $\omega_{\tilde{\Omega}}$ on the algebra of observables $\mathfrak{A}_{\mathcal{B}}$ is a normalized functional ($\omega(I)=1$). To model the quasi-free Luttinger ground state, we specify it as a state annihilated by the dressed lowering modes:
$$
\forall A, \quad \omega_{\tilde{\Omega}}(A \cdot \tilde{\rho}_{-m, \nu}) = 0 \quad \text{and} \quad \omega_{\tilde{\Omega}}(\tilde{\rho}_{m, \nu} \cdot A) = 0 \tag{19.1}
$$
*(Note: As proven in A08, a finite matrix algebra may not possess a true vacuum for these exact conditions if the budget is strictly truncated. In Lean, we can define $\omega$ formally as an abstract quasi-free functional on the untruncated CCR word algebra before applying it to finite-Fock evaluations).*

*Lean 4 Proof Strategy:*
Formalize the untruncated CCR word algebra using a free algebra quotiented by the CCR relations. Define the state $\omega_{\tilde{\Omega}}$ as a `LinearMap` from this algebra to the base field ($\mathbb{C}$ or $\mathbb{R}$). Impose the properties `omega (1) = 1`, `omega (A * rho_tilde_minus) = 0`, and `omega (rho_tilde_plus * A) = 0`. To prove the existence of such a state, use the GNS construction or formally construct the quasi-free state using Wick's theorem defined recursively on the generators. The property of positivity (`omega (A^* * A) >= 0`) should be stated as a typeclass or structure field.

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

*Lean 4 Proof Strategy:*
Use the Inverse Bogoliubov transformation to express the bare modes $\rho_{m,R}$ in terms of the dressed modes $\tilde{\rho}_{m,R}$ and $\tilde{\rho}_{m,L}$. Substitute this into the linear functional $\omega_{\tilde{\Omega}}$. Apply the linearity of the functional and the annihilation conditions from Definition 19.1 to simplify the terms. The non-vanishing terms will come from the canonical commutation relations of the dressed modes, producing the $\delta_{mn}$ and factors of $c$ and $s$. Auxiliary lemmas needed include the expression of bare modes in terms of dressed modes (Lemma 18.3) and the CCR for dressed modes.

#### 19.3 Real-Space Spatial Correlators

**Definition 19.3 (Spatial Density Operator).**
The bare spatial density for a branch is the exact finite Fourier sum up to cutoff $M$:
$$
\rho_R(x) := \frac{1}{L} \sum_{m=1}^{M} \left( \zeta^{-mx} \rho_{m, R} + \zeta^{mx} \rho_{-m, R} \right) \tag{19.4}
$$

*Lean 4 Proof Strategy:*
Define $\rho_R(x)$ as a finite sum using `Finset.sum` over the range `1` to `M`. This is a formal linear combination of the algebraic generators $\rho_{m,R}$ and $\rho_{-m,R}$ with coefficients in $\mathbb{C}$ (where $\zeta$ is a primitive phase or $e^{i 2\pi / L}$). Ensure the coefficients and generators belong to the same algebra structure using scalar multiplication (`smul`).

**Theorem 19.4 (Exact Spatial Density Correlator).**
Expanding the product $\rho_R(x)\rho_R(y)$ and applying Theorem 19.2, the anomalous contractions $\omega(\rho_m \rho_n)$ vanish, yielding the exact ordered two-point function:
$$
D_c(x, y) := \omega_{\tilde{\Omega}} (\rho_R(x) \rho_R(y)) = \frac{1}{L^2} \sum_{m=1}^{M} m \left( s^2 \zeta^{-m(x-y)} + c^2 \zeta^{m(x-y)} \right) \tag{19.5}
$$
If we evaluate the symmetrized correlator $\frac{1}{2}\omega(\{\rho_R(x), \rho_R(y)\})$, the $c^2$ and $s^2$ terms combine symmetrically to $(c^2+s^2) \cos(\dots)$, reflecting the Luttinger parameter $K_L$. However, the strictly ordered correlator uniquely preserves the exact $c^2, s^2$ distinction required to match the finite vacuum variance.

*Lean 4 Proof Strategy:*
Use the linearity of $\omega_{\tilde{\Omega}}$ to move it inside the double `Finset.sum` resulting from the product of the two density operators. Distribute the product inside the sums. Apply Theorem 19.2 to evaluate the expectations of the mode pairings. Terms of the form $\omega(\rho_{m,R} \rho_{n,R})$ and $\omega(\rho_{-m,R} \rho_{-n,R})$ will vanish due to the definition of the state and conservation of momentum. The remaining terms are exactly the two contractions given in Theorem 19.2. Sum over the Kronecker deltas to collapse one of the sums, yielding the final exact expression for the correlator. Needed auxiliary lemmas include `map_sum` for linear functionals and distribution of multiplication over addition in the algebra.

#### 19.4 Technical Notes for the Lean 4 Formalization

1. **Explicit Finite Kernels:**
   * Prove finite character-sum formulas explicitly. A periodic finite sum does not establish a power-law decay theorem automatically.
   * If continuum asymptotics are required, specify the scaling variables and limiting sequence in a completely separate analytic module. Do not use $\propto$ to hide finite regulator dependence.
2. **Two-Point Contractions:**
   * Apply the functional linearity `map_add` and both the $c^2$ and $s^2$ evaluations. Do not omit the free-vacuum fluctuations.
