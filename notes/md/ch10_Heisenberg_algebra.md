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

*Lean 4 Proof Strategy:*
Formalize $[\rho_{-m}, \rho_m]$ as `Commutator (rho (-m)) (rho m)`. The proof strategy relies on an auxiliary lemma `dGamma_commutator` establishing $[d\Gamma(A), d\Gamma(B)] = d\Gamma([A,B])$. We then define the single-particle shift matrices $T_m$ and evaluate their commutator $[T_{-m}, T_m]$. By matrix arithmetic on the finite basis $q \in [-h+1, h]$, the non-zero entries of this matrix are exactly the diagonal elements at the bottom `m` and top `m` modes. We then use another auxiliary lemma `dGamma_diagonal` which maps a diagonal single-particle operator to a sum of occupation number operators $n_q$.

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

*Lean 4 Proof Strategy:*
We apply Lemma 10.1 to rewrite the commutator as a difference of occupation number sums. Then, introduce an auxiliary lemma `frozen_margins_eval` which states that for any $\psi \in B(N,K)$, if $q \le -h + m$ (which is in the bottom frozen margin due to $m + K + |N| \le h$), $n_q\psi = \psi$. Similarly, if $q > h - m$, $n_q\psi = 0$. Summing over the `m` terms in the bottom edge yields $m\psi$, and summing over the top edge yields $0\psi$. The proof requires `simp` with `frozen_margins_eval` and `Finset.sum_const`.

#### 10.3 The General Kac-Moody Algebra and Excursion Tracking

For off-diagonal commutators $[\rho_m, \rho_n]$ where $m+n \neq 0$, the edge formula yields hopping operators $c^\dagger_{q+m+n} c_q^{\phantom{\dagger}}$. To ensure these exactly annihilate the state, we require a broader margin.

**Lemma 10.3 (Regime M2: Off-Diagonal Suppression).**
If the parameters $m, n \in \mathbb{Z}$ satisfy the **M2 Margin Condition**:

$$
\vert{}m\vert{} + \vert{}n\vert{} + K + \vert{}N\vert{} \le h \tag{10.5}
$$

every hopping operator in the residual edge domains strictly annihilates $\psi \in B(N,K)$. Thus:

$$
\forall m+n \neq 0, \quad [\rho_m, \rho_n] \psi = 0 \tag{10.6}
$$

*Lean 4 Proof Strategy:*
Similar to Lemma 10.1, we evaluate the single-particle commutator $[T_m, T_n]$, which results in off-diagonal hopping terms $c^\dagger_{q+m+n} c_q^{\phantom{\dagger}}$ located only at the edges of the spectrum. We then state an auxiliary lemma `frozen_margins_hopping_annihilation`: for $\psi \in B(N,K)$, any hopping operator originating from the top frozen margin or landing in the bottom frozen margin will annihilate `psi`. Under the M2 Margin Condition, all residual edge hoppings satisfy this criteria. `simp` using this auxiliary lemma yields `0`.

**Theorem 10.4 (The U(1) Kac-Moody Algebra on the Budget).**
Let $M \ge 1$ be a mode cutoff. Under the uniform margin condition:

$$
2M + K + |N| \le h
$$

which simultaneously satisfies the M1 condition for opposite modes ($|m| + K + |N| \le h$) and the M2 condition for unequal modes ($|m| + |n| + K + |N| \le h$), the normal-ordered densities $:\!\rho_m\!: \ := \rho_m - \delta_{m0} h I$ for all $|m|, |n| \le M$ satisfy the exact Kac-Moody algebra on the budget subspace:

$$
\forall \psi \in B(N,K), \quad [:\!\rho_m\!:, :\!\rho_n\!:] \psi = -m \delta_{m+n, 0} \psi \tag{10.7}
$$

*(Note: Without these margin hypotheses, the identity is false: the unrestricted commutator on the full Fock space contains the finite edge terms of Lemma 10.1 and Lemma 10.3).*

*Lean 4 Proof Strategy:*
State the signed integer mode bounds with consistent natural/Int casts. Expand normal ordering and handle m=0 or n=0 by the exact number-conservation identity. For opposite nonzero modes apply Lemma 10.2 to the positive absolute mode and use commutator antisymmetry for the sign −m; for unequal modes apply Lemma 10.3 with its two-mode margin. Preserve the input ψ throughout, then simplify the Kronecker delta.

*(Note: $\rho_m$ for $m > 0$ physically acts as a creation mode, raising energy, mathematically matching the lowering current $J_{-m}$, yielding the minus sign).*

**Lemma 10.5 (Composition Margin Accounting).**
A proved restricted identity $[\rho_{-m},\rho_m]\psi=m\psi$ needs its stated input margin on $\psi$ only. When substituting such an identity inside a longer word, check the state produced by the right suffix at the substitution point. The two products in the already proved commutator do not impose a second same-budget premise by themselves.
When evaluating an operator word of density modes bounded by mode cutoff $M$, let $K_{\text{excursion}}$ denote the maximum cumulative intermediate upward excitation energy added beyond the input energy $K$ (so that the maximum intermediate energy is bounded by $K + K_{\text{excursion}}$).
The conservative uniform condition for all intermediate states and commutators to remain valid and act as exact scalars is:

$$
2M + K + K_{\text{excursion}} + |N| \le h \tag{10.8}
$$

*Lean 4 Proof Strategy:*
Formalize `K_excursion` by defining an upper bound on the cumulative energy increase caused by sequential applications of density operators up to mode `M`. State a helper lemma `energy_bound_rho`: $\rho_m$ changes the energy of a state by at most `m` and the charge by `0`. We formalize the condition as a predicate `ValidMarginSeq` for a list of operators. The proof proceeds by induction on the length of the operator word. For each step, we show that applying $\rho_m$ yields a new state in $B(N,K')$ where $K' \le K + K_{\mathrm{excursion}}$. As long as the maximal `K'` still satisfies the margin $2M + K' + |N| \le h$, the individual commutator evaluations remain valid.

Every restricted scalar identity remains a theorem about its strictly typed action on input vectors, and must not be blindly substituted as a global endomorphism equality over the entire finite carrier.
