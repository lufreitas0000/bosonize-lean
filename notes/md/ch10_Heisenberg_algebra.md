### Chapter 10: Heisenberg Algebra and the Exact Schwinger Term

To understand how fermionic bilinears can perfectly mimic bosonic operators without infinite topological limits, we must establish the boundary mechanics of the finite dual band. The mathematical regularization adheres strictly to the budget margins established in [Appendix A03](../appendices/a03_energy_budgets_and_filtered_maps.md) and [Appendix A04](../appendices/a04_density_partitions_and_sugawara.md).

#### 10.1 The Exact Diagonal Commutator and Edge Formula

We evaluate the pure algebraic commutator of opposing density modes, $[\rho_{-m}, \rho_m]$ for an integer $m \ge 1$, across the entire finite-dimensional Fock space $\mathcal{F}$, without any budget restrictions yet.

Because $\rho_m = d\Gamma(T_m)$, the second-quantization map preserves commutators exactly:
$$
[\rho_{-m}, \rho_m] = d\Gamma([T_{-m}, T_m]) \tag{10.1}
$$

The single-particle matrices strictly commute in the bulk of the band. The non-zero entries of $[T_{-m}, T_m]$ exist only where the finite band boundaries truncate the shift operations. Subtracting the left-acting and right-acting domains yields exactly two residual edge zones.

**Lemma 10.1 (The Exact Diagonal Edge Formula).**
For any integer $1 \le m \le h$, evaluating the algebraic commutator $[\rho_{-m}, \rho_m]$ on the full Fock space $\mathcal{F}$ yields exactly the difference in occupation between the bottom $m$ modes and the top $m$ modes:

$$
\forall 1 \le m \le h, \quad [\rho_{-m}, \rho_m] = \sum_{q = -h+1}^{-h+m} n_q - \sum_{q = h-m+1}^{h} n_q \tag{10.2}
$$

*Physical Note:* This operator identity is exact on the entire Fock space. It is a dynamical operator, not a scalar. The algebra only becomes bosonic (scalar) when evaluated on vectors restricted by the energy budget.

#### 10.2 The Schwinger Term and Margin Accounting

**Lemma 10.2 (Regime M1: The Diagonal Buffer Zone).**
Let $\psi \in B(N,K)$ be an arbitrary state in the fixed-charge energy budget. To evaluate the edge operators, we use the Frozen Margins theorem (Lemma 7.5). If the parameters satisfy the **M1 Margin Condition**:

$$
m + K + \vert{}N\vert{} \le h \tag{10.3}
$$

every mode in the Bottom Edge interval is identically full ($n_q \psi = \psi$), and every mode in the Top Edge interval is identically empty ($n_q \psi = 0$). Therefore, the operator evaluates to exactly the scalar Schwinger term:

$$
\forall \psi \in B(N,K), \quad [\rho_{-m}, \rho_m] \psi = m \psi \tag{10.4}
$$

#### 10.3 The General Kac-Moody Algebra and Excursion Tracking

For off-diagonal commutators $[\rho_m, \rho_n]$ where $m+n \neq 0$, the edge formula yields hopping operators $c^\dagger_{q+m+n} c_q$. To ensure these exactly annihilate the state, we require a broader margin.

**Lemma 10.3 (Regime M2: Off-Diagonal Suppression).**
If the parameters $m, n \in \mathbb{Z}$ satisfy the **M2 Margin Condition**:

$$
\vert{}m\vert{} + \vert{}n\vert{} + K + \vert{}N\vert{} \le h \tag{10.5}
$$

every hopping operator in the residual edge domains strictly annihilates $\psi \in B(N,K)$. Thus:

$$
\forall m+n \neq 0, \quad [\rho_m, \rho_n] \psi = 0 \tag{10.6}
$$

**Theorem 10.4 (The U(1) Kac-Moody Algebra on the Budget).**
Combining these results and the normal ordering $:\!\rho_m\!: \ := \rho_m - \delta_{m0} h I$, we obtain the exact Kac-Moody algebra on the budget subspace:

$$
\forall \psi \in B(N,K), \quad [:\!\rho_m\!:, :\!\rho_n\!:] \psi = -m \delta_{m+n, 0} \psi \tag{10.7}
$$

*(Note: $\rho_m$ for $m > 0$ physically acts as a creation mode, raising energy, mathematically matching the lowering current $J_{-m}$, yielding the minus sign).*

**Lemma 10.5 (Composition Margin Accounting).**
Because $[\rho_{-m}, \rho_m] = \rho_{-m}\rho_m - \rho_m\rho_{-m}$ consists of operator products, the intermediate state after the first application must also satisfy the margin conditions. An input-only margin is not a margin for the entire calculation. When commuting a word of multiple density operators bounded by a maximum mode cutoff $M$, we define the maximum cumulative upward energy excursion $K_{\text{excursion}}$. The conservative uniform condition for all such commutators to act as exact scalars is:

$$
2M + K + K_{\text{excursion}} + |N| \le h \tag{10.8}
$$
Every restricted scalar identity remains a theorem about its strictly typed action on input vectors, and must not be blindly substituted as a global endomorphism equality over the entire finite carrier.
