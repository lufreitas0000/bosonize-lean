### Chapter 17: Forward Scattering & The Luttinger Hamiltonian

In 1+1 dimensions, the physics is famously different. Interacting fermions cannot pass each other, so individual quasi-particle excitations are strictly forbidden. All excitations must become collective waves.
We focus on forward scattering density-density interactions. The formalization strictly follows [Appendix A07](../appendices/a07_interactions_and_bogoliubov.md) and [Appendix A10](../appendices/a10_discrete_rg_and_schrieffer_wolff.md).

#### 17.1 Definitions of the 4-Fermion Interactions

We specify a transfer domain, e.g. $-M \le m \le M$, with every pair filtered by $k+m$ in the finite band.

**Definition 17.1 (Raw Intra-branch Interaction $g_4$).**
Let $g_4 \in \mathbb{R}$. The intra-branch interaction involves two particles of the same species:
$$
H_{4, \text{raw}} := \frac{g_4}{2L} \sum_{\nu \in \{R, L\}} \sum_{m=-M}^{M} \sum_{k, p \in \Lambda^*} :\! c^\dagger_{(\nu, k+m)} c_{(\nu, k)} c^\dagger_{(\nu, p-m)} c_{(\nu, p)} \!: \tag{17.1}
$$

**Definition 17.2 (Raw Inter-branch Interaction $g_2$).**
Let $g_2 \in \mathbb{R}$. The momentum exchange $m$ shifts one Right-mover and one Left-mover. While fundamental fermions anticommute across species, even-degree bilinears commute:
$$
H_{2, \text{raw}} := \frac{g_2}{L} \sum_{m=-M}^{M} \left( \sum_{k \in \Lambda^*} :\!c^\dagger_{(R, k+m)} c_{(R, k)}\!: \right) \left( \sum_{p \in \Lambda^*} :\!c^\dagger_{(L, p-m)} c_{(L, p)}\!: \right) \tag{17.2}
$$

#### 17.2 Algebraic Reduction to Bosonic Modes

**Lemma 17.3 (Exact Factorization of Inter-branch $g_2$).**
Because even bilinears commute across branches, $H_{2, \text{raw}}$ maps exactly to a purely bilinear sum of density modes. Depending on the chiral momentum mapping convention to opposite branches (see A07), this produces either a hopping form ($C_R A_L + C_L A_R$) or a pairing form ($C_R C_L + A_R A_L$). The Luttinger model physically requires the hyperbolic **pairing form**:
$$
H_{2, \text{raw}} = \frac{g_2}{L} \sum_{m=1}^{M} m \left( \rho_{m, R} \rho_{m, L} + \rho_{-m, R} \rho_{-m, L} \right) \tag{17.3}
$$

**Lemma 17.4 (Exact Factorization of Intra-branch $g_4$).**
For intra-branch scattering, reordering a middle creator past an annihilator uses the exact anticommutator $c_k c_p^\dagger = \delta_{kp} I - c_p^\dagger c_k$. This swap generates a trace term that reconstructs exactly the particle number operator shifts. To match the $N(N+1)/2$ ground shifts from Chapter 12 without mismatching factors of $N$, an explicit chemical-potential subtraction is required. On the budget subspace:
$$
H_{4, \text{raw}} = \frac{g_4}{L} \sum_{\nu \in \{R, L\}} \sum_{m=1}^{M} m \rho_{m, \nu} \rho_{-m, \nu} + E_{4,\text{zero}} \tag{17.4}
$$

#### 17.3 The Interacting Luttinger Hamiltonian

**Theorem 17.5 (The Bosonized Luttinger Hamiltonian).**
Combining the free $H_0$ and the forward scattering terms on the budget subspace, the Hamiltonian evaluates exactly to the pairing quadratic form:
$$
H_{\text{Lutt}} = \frac{2\pi}{L} \sum_{m=1}^{M} m \left[ v_1 \left( \rho_{m, R} \rho_{-m, R} + \rho_{m, L} \rho_{-m, L} \right) + v_2 \left( \rho_{m, R} \rho_{m, L} + \rho_{-m, R} \rho_{-m, L} \right) \right] + E_{\text{zero}} \tag{17.5}
$$
where $v_1 = v_F + \frac{g_4}{2\pi}$ and $v_2 = \frac{g_2}{2\pi}$.

**Theorem 17.6 (Exact Luttinger Fixed Line under SWT).**
Because $H_{\text{Lutt}}$ is strictly quadratic and exactly block-diagonalizable on the discrete partition basis, applying the Discrete Schrieffer-Wolff projection $\mathbb{E}_K$ (see Appendix A10) yields exactly zero interaction loop corrections between modes $m$. The continuous Luttinger liquid is thereby an exact discrete algebraic fixed line under mode decimation.

#### 17.4 Technical Notes for the Lean 4 Formalization

1. **Reordering via CAR (`c† c = δ - c c†`):**
   * Do not use generic commutators for the middle fermions. Expand with distributivity and the CAR rules, then normalize scalar coefficients.
2. **Transfer Domain Filtering:**
   * Enforce the boundaries of the discrete lattice explicitly in the sums. Do not allow modes to wrap non-physically via modulo arithmetic unless using an explicitly defined modular scattering theory.
