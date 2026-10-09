### Chapter 7: Vacuum, Sectors, Energy, Budget

*Assumption:* From this chapter onward, we strictly require the lattice size $L = 2h$ to be an even integer. This guarantees the existence of a perfectly half-filled Fermi sea in the asymmetric dual band $\Lambda^* = \{-h+1, \dots, h\}$. The mathematical formulation of the budget bounds follows [Appendix A03](../appendices/a03_energy_budgets_and_filtered_maps.md).

**Intuition for the "Energy Budget":**
In continuum quantum field theory, the Dirac sea has infinite depth. Taking the limit $L \to \infty$ naively results in unbounded operators and divergences. To formalize this rigorously without resorting to topology, we use a truncation scheme called the **Energy Budget**, restricting our operators and states to a finite-dimensional subspace governed by excitation energy ($K$) and net charge deviation ($N_{\max}$).

---

#### 7.1 Definitions

**Definition 7.1 (Dirac Vacuum).**
The vacuum state subset $S_\Omega \subseteq \Lambda^*$ corresponds to the exactly $h$ occupied modes $k \le 0$:

$$
S_\Omega := \{k \in \Lambda^* \mid k \le 0\} \tag{7.1}
$$

The vacuum state vector is defined on the Fock basis as $|\Omega\rangle := \delta_{S_\Omega}$.

**Definition 7.2 (Integer Charge and Energy).**
To avoid natural subtraction anomalies, we define all fundamental combinatorial quantities strictly in $\mathbb{Z}$:

$$
N(S) := (\#S : \mathbb{Z}) - h \tag{7.2}
$$
$$
P(S) := \sum_{k \in S} k - \sum_{k \le 0} k \tag{7.3}
$$

The ground-energy integer $t(N)$ is defined as the unique integer satisfying $2 t(N) = N(N+1)$. The true excitation energy is precisely:

$$
e(S) := P(S) - t(N(S)) \tag{7.4}
$$

**Definition 7.3 (Budget Subspaces).**
We explicitly distinguish three orthogonal coordinate spans of the occupation basis:
1. **Fixed-Energy Space:** $H(N,E) := \mathrm{span}_{\mathbb{C}} \{ \delta_S \mid N(S) = N \land e(S) = E \}$.
2. **Fixed-Charge Budget:** $B(N,K) := \mathrm{span}_{\mathbb{C}} \{ \delta_S \mid N(S) = N \land e(S) \le K \}$.
3. **Charge-Box Budget:** $\mathcal{B}_{K,N_{\max}} := \mathrm{span}_{\mathbb{C}} \{ \delta_S \mid e(S) \le K \land |N(S)| \le N_{\max} \}$.

A coordinate projection $P_K$ deletes coefficients outside the subset, acting perfectly as an exact orthogonal projection without analytic completions.

---

#### 7.2 Properties of the Vacuum, Energy, and the Budget Subspace

**Lemma 7.4 (Rank Formula and Monotonic Displacements).**
For an arbitrary configuration sorted from lowest to highest, $s_1 < s_2 < \dots < s_{h+N}$, the perfect ground reference is $g_i = -h+1+i$ (0-based index). The independent displacement is $d_i = s_i - g_i$. We rigorously establish that $d_i \ge 0$ and the sequence is monotonically non-decreasing.

$$
e(S) = \sum_i d_i \tag{7.5}
$$

This guarantees algebraically that $e(S) \ge 0$, and the sector ground kets ($|N\rangle_0$) are precisely the unique vectors satisfying $e(S) = 0$.

**Lemma 7.5 (Frozen Margins).**
Because the sequence $d_i$ is non-decreasing and non-negative, the sum $e(S) \le K$ tightly binds the configuration:
1. For all $k \le N-K$, the mode is rigidly full.
2. For all $k > N+K$, the mode is rigidly empty.

**Lemma 7.6 (Filtered Operator Action).**
An operator $A$ with energy shift $d \ge 0$ maps the budget $B(N,K)$ strictly into the expanded budget $B(N, K+d)$. It does not act as an endomorphism on $B(N,K)$. For negative shifts $d < 0$, we apply strict integer cutoffs to handle annihilation below the ground state. If a compressed endomorphism is required, it must be explicitly defined as $A_K := P_K A$.

**Lemma 7.7 (Composition Margin Accounting).**
When composing operators, partial equality must respect target margins. If $A = B$ strictly on a subspace $W$, and an operator $C$ maps subspace $V$ into $W$, then exactly $AC = BC$ on $V$. When determining the required uniform band cutoffs, the budget $K$ must explicitly include the maximum cumulative upward excursion of intermediate words:

$$
2M + K_{\text{excursion}} + N_{\max} \le h \tag{7.6}
$$
