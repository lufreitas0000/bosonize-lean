### Chapter 7: Vacuum, Sectors, Energy, Budget

*Assumption:* From Chapter 5 onward, the lattice size $L = 2h$ is strictly required to be a positive even integer with $h > 0$. This guarantees the existence of a perfectly half-filled Fermi sea in the asymmetric dual band $\Lambda^* = \{-h+1, \dots, h\}$. The mathematical formulation of the budget bounds follows [Appendix A03](../appendices/a03_energy_budgets_and_filtered_maps.md).

**Intuition for the "Energy Budget":**
In continuum quantum field theory, the Dirac sea has infinite depth. Taking the limit $L \to \infty$ naively results in unbounded operators and divergences. To formalize this rigorously without resorting to topology, we use a truncation scheme called the **Energy Budget**, restricting our operators and states to a finite-dimensional subspace governed by excitation energy ($K$) and net charge deviation ($N_{\max}$).

---

#### 7.1 Definitions

**Definition 7.1 (Dirac Vacuum and Admissible Sectors).**
The charge sector $N$ is admissible if $-h \le N \le h$. Outside this range, the sector subspace is empty (dimension zero), and there is no nonzero ground state.
For any admissible $N \in \{-h, \dots, h\}$, the sector ground configuration is:

$$
S_N := \{k \in \Lambda^* \mid k \le N\} \tag{7.1}
$$

For $N = 0$, this is the Dirac vacuum subset $S_\Omega := S_0 = \{k \in \Lambda^* \mid k \le 0\}$, containing exactly $h$ occupied modes.
The sector ground state vector is defined on the Fock basis as $|N\rangle_0 := \delta_{S_N}$, with Dirac vacuum $|\Omega\rangle := |0\rangle_0 = \delta_{S_\Omega}$.

*Lean 4 Proof Strategy:*
Formalize admissible sectors with the subtype `{N : ℤ // -h ≤ N ∧ N ≤ h}`. Define `S_N` as `{k : Int // k ∈ Λ* ∧ k ≤ N}`. Show `S_N.card = h + N`. The ground ket `|N⟩_0` is `Finsupp.single S_N 1` or `PiLp.basisFun S_N`.

**Definition 7.2 (Integer Charge, Energy, and Observables).**
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

We define the diagonal relative-charge observable $\hat{N}$ and excitation energy observable $\hat{E}$ once on the Fock basis:

$$
\hat{N} \delta_S := N(S) \delta_S, \qquad \hat{E} \delta_S := e(S) \delta_S
$$

distinguishing these operator observables from the scalar functions $N(S), e(S)$.

*Lean 4 Proof Strategy:*
Define `N(S)` and `P(S)` as computable functions returning `Int`.
- `N (S : Finset Int) : Int := S.card - h`
- `P (S : Finset Int) : Int := (∑ k in S, k) - (∑ k in S_Omega, k)`
`t(N) := (N * (N + 1)) / 2`, proving `Even (N * (N + 1))`. Define `E_hat` and `N_hat` as diagonal linear maps on `FockSpace`.
**Auxiliary Lemmas:**
- `t_N_is_integer`: Proof that `N * (N + 1)` is always even.
- `P_Omega_zero`: `P(S_Omega) = 0`.
- `e_Omega_zero`: `e(S_Omega) = 0`.

**Definition 7.3 (Budget Subspaces and Projections).**
We distinguish the nested coordinate spans of the occupation basis:
1. **Fixed-Energy Space:** $H(N,E) := \mathrm{span}_{\mathbb{C}} \{ \delta_S \mid N(S) = N \land e(S) = E \}$.
2. **Fixed-Charge Budget:** $B(N,K) := \mathrm{span}_{\mathbb{C}} \{ \delta_S \mid N(S) = N \land e(S) \le K \} = \bigoplus_{E=0}^K H(N,E)$.
3. **Charge-Box Budget:** $\mathcal{B}_{K,N_{\max}} := \mathrm{span}_{\mathbb{C}} \{ \delta_S \mid e(S) \le K \land |N(S)| \le N_{\max} \} = \bigoplus_{|N| \le N_{\max}} B(N,K)$.

For multi-species systems $\vec{N} = (N_\nu)$, the excitation budget convention is explicitly the total excitation energy $\sum_\nu e_\nu(S_\nu) \le K$ (distinguished from independent per-species cutoffs).
The orthogonal coordinate projections are labeled by their full retained data:
- $P_{N,K}$ projects onto $B(N,K)$.
- $P_{K,N_{\max}}$ projects onto $\mathcal{B}_{K,N_{\max}}$.

*Lean 4 Proof Strategy:*
Budget subspaces are formalized as `Submodule ℂ FockSpace`. Fixed-energy spaces with distinct $E$ or $N$ are mutually orthogonal. $B(N,K)$ is the internal direct sum of $H(N,E)$ for $0 \le E \le K$. Coordinate projections `P_{N,K}` and `P_{K,N_max}` are idempotent and self-adjoint.

---

#### 7.2 Properties of the Vacuum, Energy, and the Budget Subspace

**Lemma 7.4 (Rank Formula and Monotonic Displacements).**
For an arbitrary configuration $S$ sorted from lowest to highest, $s_0 < s_1 < \dots < s_{\#S - 1}$ with $0 \le i < \#S = h+N$, the ground reference configuration is $g_i = -h+1+i$. The independent displacement is $d_i = s_i - g_i$. We rigorously establish that $d_i \ge 0$ and the sequence is monotonically non-decreasing ($d_{i+1} \ge d_i$).

$$
e(S) = \sum_{i=0}^{h+N-1} d_i \tag{7.5}
$$

This guarantees algebraically that $e(S) \ge 0$. In each admissible sector $-h \le N \le h$, the ground configuration $S_N$ is the unique **configuration** satisfying $e(S) = 0$, and the zero-energy space $H(N,0) = \mathbb{C} \cdot |N\rangle_0$ is the one-dimensional span of the ground ket.

*Lean 4 Proof Strategy:*
Map configuration `S` to a sorted sequence using `Finset.sort`.
Let `s` be the `Fin` indexed array of size `h + N`. Ground reference `g i := -h + 1 + i`.
Displacement `d i := s i - g i`.
To prove $d_i \ge 0$, proceed by induction on $i$.
**Auxiliary Lemmas:**
- `g_is_minimal`: Proof that any strictly increasing sequence `s` in $\Lambda^*$ satisfies `s i \ge g i`.
- `e_eq_sum_d`: Proof that $e(S) = \sum_i d_i$.
- `e_nonneg`: Proof that $e(S) \ge 0$ for all $S$.
- `e_zero_iff_ground`: Proof that $e(S) = 0 \iff S = S_N$, ensuring the zero-energy subspace has dimension 1.

**Lemma 7.5 (Frozen Margins).**
Because the sequence $d_i$ is non-decreasing and non-negative, the sum $e(S) \le K$ tightly binds the configuration:
1. For all $k \le N-K$, the mode is rigidly full.
2. For all $k > N+K$, the mode is rigidly empty.

*Lean 4 Proof Strategy:*
Given $\sum d_i = e(S) \le K$ and $d_i \ge 0$, we have $d_i \le K$ for all $i$. 
If a mode at $k \le N-K$ were empty, or $k > N+K$ were occupied, $\sum d_i$ would exceed $K$.
**Auxiliary Lemmas:**
- `empty_deep_implies_large_e`: If missing a particle at $k \le N-K$, $e(S) > K$.
- `occupied_high_implies_large_e`: If a particle is at $k > N+K$, $e(S) > K$.

**Lemma 7.6 (Filtered Operator Action).**
An operator $A$ with energy shift $d$ and charge shift $q$ (satisfying $[\hat{N}, A] = q A$ and mapping states of energy $e$ to states of energy at most $e+d$) maps the budget $B(N,K)$ strictly into the budget $B(N+q, K+d)$ (for $d \ge 0$, and into $B(N+q, \max(0, K+d))$ for negative shifts). Charge preservation ($q=0$) is an explicit hypothesis if the target sector is to remain $N$.
If a compressed endomorphism on $B(N,K)$ is required, it must be explicitly defined as $A_{N,K} := P_{N,K} A P_{N,K}$.

*Lean 4 Proof Strategy:*
Formalize bounded energy and charge shifts: $A$ has shift $(q, d)$ if for all basis states $\delta_S$, $A(\delta_S)$ is supported on states with $N(S') = N(S) + q$ and $e(S') \le e(S) + d$.
**Auxiliary Lemmas:**
- `map_budget_le`: Proof that $\forall x \in B(N,K), A x \in B(N+q, K+d)$.
- Definition of compressed operator $A_{N,K} := P_{N,K} \circ A \circ P_{N,K}$.

**Lemma 7.7 (Composition Margin Accounting).**
When composing operators, partial equality must respect target margins. If $A = B$ strictly on a subspace $W$, and an operator $C$ maps subspace $V$ into $W$, then $AC = BC$ on $V$.
When evaluating words of density operators with mode cutoff $M$, intermediate states experience transient energy excursions. Let $K_{\text{excursion}}$ denote the maximum cumulative upward energy excursion beyond the input budget $K$ (so the maximum intermediate energy is $K + K_{\text{excursion}}$). The conservative uniform condition ensuring that all intermediate states stay within the linear band regime without hitting the band edges is:

$$
2M + K + K_{\text{excursion}} + N_{\max} \le h \tag{7.6}
$$

*Lean 4 Proof Strategy:*
Formalize `K_excursion` as the maximum intermediate energy increase during word evaluation.
The condition $2M + K + K_{\text{excursion}} + N_{\max} \le h$ guarantees that the active window of intermediate states stays strictly within $[-h+1, h]$.
**Auxiliary Lemmas:**
- `comp_eq_on_submodule`: General lemma for equality of composed maps on restricted domains.
- `no_band_collision`: Under $2M + K + K_{\text{excursion}} + N_{\max} \le h$, the frozen margins prevent band-edge saturation for all intermediate steps.
