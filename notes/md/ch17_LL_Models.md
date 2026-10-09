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

We maintain the consistent current convention of Chapters 8–13 for both branches $\nu \in \{R, L\}$:
$$
C_\nu := \rho_{m, \nu} \quad (\text{creator for } m > 0), \qquad A_\nu := \rho_{-m, \nu} \quad (\text{annihilator for } m > 0),
$$
satisfying the Kac-Moody CCR $[A_\nu, C_\nu] = m I$ on permitted budgets, with $A_\nu |\vec{N}\rangle_0 = 0$.

**Lemma 17.3 (Inter-branch Scattering: Hopping Reduction vs. Pairing Model).**
Because even bilinears commute across branches, $H_{2, \text{raw}}$ maps to bilinear sums of density modes:
1. *Raw transfer reduction (Hopping Form):* Evaluating the raw opposite-transfer interaction (17.2) (which transfers $+m$ on $R$ and $-m$ on $L$ in computational momentum) yields the number-conserving **hopping interaction**:
$$
H_{2, \text{raw}} = \frac{g_2}{L} \left[ N_R N_L + \sum_{m=1}^{M} \left( \rho_{m, R} \rho_{-m, L} + \rho_{-m, R} \rho_{m, L} \right) \right] = \frac{g_2}{L} \left[ N_R N_L + \sum_{m=1}^M \left( C_R A_L + A_R C_L \right) \right] \tag{17.3}
$$
Notice that $(C_R A_L + A_R C_L) |\vec{N}\rangle_0 = 0$ annihilates the joint sector ground state.
2. *Luttinger Pairing Model (Pairing Form):* The standard solvable Luttinger liquid Hamiltonian requires the hyperbolic **pairing interaction**:
$$
H_{2, \text{pair}} := \frac{g_2}{L} \left[ N_R N_L + \sum_{m=1}^{M} \left( \rho_{m, R} \rho_{m, L} + \rho_{-m, R} \rho_{-m, L} \right) \right] = \frac{g_2}{L} \left[ N_R N_L + \sum_{m=1}^M \left( C_R C_L + A_R A_L \right) \right] \tag{17.4}
$$
In physical fermion language, this pairing form arises from the pairing channel where the transfer on the left branch is $+m$ in computational momentum ($p \to p+m$). Because the hopping and pairing models are distinct quadratic forms with different spectra, we define the interacting Luttinger Hamiltonian $H_{\text{Lutt}}$ directly as the pairing model $H_{\text{pair}}$, retaining consistent computational creators $C_\nu = \rho_{m,\nu}$ on both branches.

**Lemma 17.4 (Exact Factorization of Intra-branch $g_4$ and Sea Normal Ordering).**
Fermionic normal-ordering is defined relative to the half-filled Dirac sea $S_0 = \{k \in \Lambda^* : k \le 0\}$:
$$
:\! c^\dagger_k c_k \!: \;:= c^\dagger_k c_k - \langle\Omega| c^\dagger_k c_k |\Omega\rangle I = \begin{cases} c^\dagger_k c_k & (k > 0) \\ - c_k c^\dagger_k & (k \le 0) \end{cases}
$$
so that the total normal-ordered charge operator is $\sum_k :\! c^\dagger_{\nu,k} c_{\nu,k} \!: \;= \hat{N}_\nu$.
For intra-branch scattering (17.1), commuting middle operators via CAR $c_k c_p^\dagger = \delta_{kp} I - c_p^\dagger c_k$ generates the diagonal density sum plus the $m=0$ charge square $\frac{g_4}{2L} \hat{N}_\nu^2$:
$$
H_{4, \text{raw}} = \frac{g_4}{L} \sum_{\nu \in \{R, L\}} \sum_{m=1}^{M} \rho_{m, \nu} \rho_{-m, \nu} + \frac{g_4}{2L} (N_R^2 + N_L^2) \tag{17.5}
$$
without redundant outer $m$ factors.

#### 17.3 The Interacting Luttinger Hamiltonian

**Theorem 17.5 (The Bosonized Luttinger Hamiltonian).**
Combining the free Sugawara kinetic energy $H_0$ from Chapter 12, the intra-branch scattering $H_4$, the pairing interaction $H_{2,\text{pair}}$, and a chemical potential term $-\mu(\hat{N}_R + \hat{N}_L)$, the Hamiltonian on the budget subspace evaluates to:
$$
H_{\text{Lutt}} = \frac{2\pi}{L} \sum_{m=1}^{M} \left[ v_1 \left( \rho_{m, R} \rho_{-m, R} + \rho_{m, L} \rho_{-m, L} \right) + v_2 \left( \rho_{m, R} \rho_{m, L} + \rho_{-m, R} \rho_{-m, L} \right) \right] + E_{\text{zero}} \tag{17.6}
$$
where $v_1 = v_F + \frac{g_4}{2\pi}$, $v_2 = \frac{g_2}{2\pi}$, and the exact zero-mode energy is:
$$
E_{\text{zero}} = \frac{2\pi v_F}{L} \sum_{\nu \in \{R,L\}} \frac{N_\nu(N_\nu+1)}{2} + \frac{g_4}{2L}(N_R^2 + N_L^2) + \frac{g_2}{L} N_R N_L - \mu(N_R + N_L) \tag{17.7}
$$
Choosing the chemical potential $\mu := \frac{\pi v_F}{L}$ cancels the linear term $\frac{2\pi v_F}{L}\frac{N_\nu}{2}$, reducing the zero-mode energy to the symmetric quadratic form:
$$
E_{\text{zero}} = \frac{\pi v_1}{L}(N_R^2 + N_L^2) + \frac{g_2}{L} N_R N_L.
$$

*Lean 4 Proof Strategy:*
Combine the non-interacting bosonized Hamiltonian $H_0$ with the scattering results from Lemmas 17.3 and 17.4. Group terms by mode $m$ and match the scalar prefactors to $v_1, v_2$ and $E_{\text{zero}}$.

**Theorem 17.6 (Energy-Shell Schrieffer-Wolff Decomposition).**
Let $\mathcal{B}_K = \mathcal{B}_{K-1} \oplus \mathcal{H}_K$ be the budget decomposition by total energy shell ($K \ge 1$), and let $P_{K-1}$ be the orthogonal projection onto $\mathcal{B}_{K-1}$.
1. *Energy shell vs. mode decimation:* $\mathcal{B}_K = \mathcal{B}_{K-1} \oplus \mathcal{H}_K$ is an energy-shell filter, not a single-mode factor decimation (e.g., at $K=2$, $\mathcal{B}_2$ retains $\{1, X_1, X_1^2, X_2\}$, whereas deleting mode 2 alone would retain $\{1, X_1, X_1^2\}$).
2. *Second-order SW effective Hamiltonian:* For a perturbation $V$ with unperturbed block-diagonal baseline $H_0$, the Schrieffer-Wolff effective Hamiltonian on the low-energy shell is an expansion modulo $t^3$ (or $O(V^3)$):
$$
H_{\text{eff}} = P H_0 P + t P V P + \frac{t^2}{2} P [S_1, V] P + O(t^3).
$$
3. *Vanishing of off-block correction:* If the perturbation satisfies $P V Q = Q V P = 0$ (where $Q = I - P$), then the first-order generator $S_1 = 0$, so the second-order correction $\frac{1}{2} P [S_1, V] P$ vanishes identically.

*Lean 4 Proof Strategy:*
Formalize the block decomposition of the budget space $\mathcal{B}_K$. Prove that when $P V Q = 0$, the generator equation $[S_1, H_0] = - P V Q$ is solved by $S_1 = 0$, implying $H_{\text{eff}} = P (H_0 + t V) P$ exactly without second-order correction. Separate the formal expansion modulo $t^3$ from any continuous Wilsonian RG flow interpretation.

#### 17.4 Technical Notes for the Lean 4 Formalization

1. **Reordering via CAR (`c† c = δ - c c†`):**
   * Do not use commutators for fermionic reordering. Expand with distributivity and the CAR rules, then normalize scalar coefficients.
2. **Transfer Domain Filtering:**
   * Enforce the boundaries of the discrete lattice explicitly in the sums. Do not allow modes to wrap non-physically via modulo arithmetic unless using an explicitly defined modular scattering theory.
3. **Current Normalization:**
   * Raw currents $\rho_{m,\nu}$ satisfy $[\rho_{-m,\nu}, \rho_{m,\nu}] = m I$. Do not insert extra factors of $m$ in quadratic Hamiltonian sums.
