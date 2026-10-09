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

*Lean 4 Proof Strategy:*
Define `H_4_raw` as a sum over the transfer domain `Finset`s using the underlying `FermionAlgebra`. Normal ordering $:\! \dots \!:$ should be implemented by an explicit subtraction of the vacuum expectation value or by structurally moving creation operators to the left. The transfer domain $-M \le m \le M$ and band limits must be strictly bounded with appropriate summation indices and `Icc` intervals.

**Definition 17.2 (Raw Inter-branch Interaction $g_2$).**
Let $g_2 \in \mathbb{R}$. The momentum exchange $m$ shifts one Right-mover and one Left-mover. While fundamental fermions anticommute across species, even-degree bilinears commute:
$$
H_{2, \text{raw}} := \frac{g_2}{L} \sum_{m=-M}^{M} \left( \sum_{k \in \Lambda^*} :\!c^\dagger_{(R, k+m)} c_{(R, k)}\!: \right) \left( \sum_{p \in \Lambda^*} :\!c^\dagger_{(L, p-m)} c_{(L, p)}\!: \right) \tag{17.2}
$$

*Lean 4 Proof Strategy:*
Define `H_2_raw` similarly to $g_4$, but operating on distinct branch indices $R$ and $L$. Since even-degree bilinears of different species commute, normal ordering can be cleanly factored across branches. This definition should directly reference the previously defined `DensityMode` (`ρ`) operators to group the sums.

#### 17.2 Algebraic Reduction to Bosonic Modes

**Lemma 17.3 (Exact Factorization of Inter-branch $g_2$).**
Because even bilinears commute across branches, $H_{2, \text{raw}}$ maps exactly to a purely bilinear sum of density modes. Depending on the chiral momentum mapping convention to opposite branches (see A07), this produces either a hopping form ($C_R A_L + C_L A_R$) or a pairing form ($C_R C_L + A_R A_L$). The Luttinger model physically requires the hyperbolic **pairing form**:
$$
H_{2, \text{raw}} = \frac{g_2}{L} \sum_{m=1}^{M} m \left( \rho_{m, R} \rho_{m, L} + \rho_{-m, R} \rho_{-m, L} \right) \tag{17.3}
$$

*Lean 4 Proof Strategy:*
Prove the algebraic equivalence between the four-fermion sum and the bosonic bilinear pair.
*Auxiliary lemmas needed:*
1. Commutativity of cross-branch bilinears: `[c†_{R,k} c_{R,k'}, c†_{L,p} c_{L,p'}] = 0`.
2. Definition of the density modes: `ρ_{m, ν} = ∑_k : c†_{ν, k+m} c_{ν, k} :`.
The proof substitutes the density mode definitions directly into the factored sum in $H_{2, \text{raw}}$, exploiting commutativity. The hyperbolic pairing form follows from correctly identifying the chiral index mappings for opposite-moving branches.

**Lemma 17.4 (Exact Factorization of Intra-branch $g_4$).**
For intra-branch scattering, reordering a middle creator past an annihilator uses the exact anticommutator $c_k c_p^\dagger = \delta_{kp} I - c_p^\dagger c_k$. This swap generates a trace term that reconstructs exactly the particle number operator shifts. To match the $N(N+1)/2$ ground shifts from Chapter 12 without mismatching factors of $N$, an explicit chemical-potential subtraction is required. On the budget subspace:
$$
H_{4, \text{raw}} = \frac{g_4}{L} \sum_{\nu \in \{R, L\}} \sum_{m=1}^{M} m \rho_{m, \nu} \rho_{-m, \nu} + E_{4,\text{zero}} \tag{17.4}
$$

*Lean 4 Proof Strategy:*
Prove the reduction of $H_{4, \text{raw}}$ into purely quadratic density modes of the same branch.
*Auxiliary lemmas needed:*
1. Repeated canonical anticommutation relations (CAR): `c_k c†_p = δ_{kp} I - c†_p c_k`.
2. The Kac-Moody algebra structure for density operators of the same species: `[ρ_{m, ν}, ρ_{n, ν}] = m δ_{m+n, 0}`.
The proof requires expanding the normal-ordered product of four fermions, using the CAR distributive property to pass operators through one another, and collecting them into density modes. The trace terms resulting from the $\delta_{kp}$ contractions reconstruct the shift $E_{4,\text{zero}}$, which must be carefully bookkept against the budget subspace.

#### 17.3 The Interacting Luttinger Hamiltonian

**Theorem 17.5 (The Bosonized Luttinger Hamiltonian).**
Combining the free $H_0$ and the forward scattering terms on the budget subspace, the Hamiltonian evaluates exactly to the pairing quadratic form:
$$
H_{\text{Lutt}} = \frac{2\pi}{L} \sum_{m=1}^{M} m \left[ v_1 \left( \rho_{m, R} \rho_{-m, R} + \rho_{m, L} \rho_{-m, L} \right) + v_2 \left( \rho_{m, R} \rho_{m, L} + \rho_{-m, R} \rho_{-m, L} \right) \right] + E_{\text{zero}} \tag{17.5}
$$
where $v_1 = v_F + \frac{g_4}{2\pi}$ and $v_2 = \frac{g_2}{2\pi}$.

*Lean 4 Proof Strategy:*
Combine the non-interacting bosonized Hamiltonian $H_0$ with the scattering results from Lemmas 17.3 and 17.4.
*Auxiliary lemma needed:* The equivalence of the free Dirac Hamiltonian $H_0$ to its bosonic density form $\sum m \rho \rho$ (established in a prior chapter).
The proof is a direct algebraic summation and grouping of terms: substitute the factored bosonic expressions, factor out the common operators, and simplify the scalar coefficients to obtain $v_1$ and $v_2$.

**Theorem 17.6 (Exact Luttinger Fixed Line under SWT).**
Because $H_{\text{Lutt}}$ is strictly quadratic and exactly block-diagonalizable on the discrete partition basis, applying the Discrete Schrieffer-Wolff projection $\mathbb{E}_K$ (see Appendix A10) yields exactly zero interaction loop corrections between modes $m$. The continuous Luttinger liquid is thereby an exact discrete algebraic fixed line under mode decimation.

*Lean 4 Proof Strategy:*
Prove that applying the discrete Schrieffer-Wolff transformation (SWT) projection operator $\mathbb{E}_K$ to $H_{\text{Lutt}}$ yields the same Hamiltonian up to a scale or vacuum energy shift.
*Auxiliary lemmas needed:*
1. $H_{\text{Lutt}}$ is purely quadratic in the set of independent operators $\rho_m$.
2. For any purely quadratic Hamiltonian that is block-diagonal in $m$, integrating out high-momentum modes using SWT produces no new cross-mode interaction terms (commutators of quadratic modes preserve the quadratic algebraic closure).
The proof evaluates the SWT commutators layer by layer, showing they naturally truncate and preserve the functional form of $H_{\text{Lutt}}$.

#### 17.4 Technical Notes for the Lean 4 Formalization

1. **Reordering via CAR (`c† c = δ - c c†`):**
   * Do not use generic commutators for the middle fermions. Expand with distributivity and the CAR rules, then normalize scalar coefficients.
2. **Transfer Domain Filtering:**
   * Enforce the boundaries of the discrete lattice explicitly in the sums. Do not allow modes to wrap non-physically via modulo arithmetic unless using an explicitly defined modular scattering theory.
