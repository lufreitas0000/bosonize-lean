### Chapter 11: Haldane Completeness

We have established that density modes $\rho_m$ behave algebraically like independent bosonic creation and annihilation operators. To formalize **Haldane Completeness**—demonstrating that the collective bosonic density waves span the low-energy fermionic space—we implement the strict combinatorial counts and Gram induction defined in [Appendix A04](../appendices/a04_density_partitions_and_sugawara.md).

#### 11.1 Bosonic Partition States

Imagine the sector ground state $|N\rangle_0$ as the undisturbed Fermi sea. We add energy $K$ using combinations of density creation modes ($m > 0$). These correspond to integer partitions of $K$.

**Definition 11.1 (Bosonic Partition States).**
*Lean 4 Proof Strategy:*
Use `List.foldr` or `List.foldl` over a sorted list of integer parts to implement the ordered product of density creation modes `ρ_m`. The type for integer partitions could be `Nat.Partition K` from Mathlib. We need an auxiliary lemma showing that since `[ρ_m, ρ_n] = 0` for `m, n > 0` (Lemma 9.5), any permutation of the ordered product yields the exact same operator on the Hilbert space, ensuring the state depends only on the partition (multiplicities `r_m`) and not the ordering.

Let $K \in \mathbb{N}$. Let $\lambda \vdash K$ be an integer partition, represented by the multiplicities $r_m$ of each integer part $m \ge 1$. We construct the state using an explicit ordered product (e.g., a fold over a sorted list), because generic endomorphisms do not commute.

$$
\forall \lambda \vdash K, \quad |\lambda; N\rangle := \left( \overrightarrow{\prod_{m \ge 1}} \rho_m^{r_m} \right) |N\rangle_0 \tag{11.1}
$$

Because all positive density modes globally commute (Lemma 9.5), this state definition is ultimately independent of the chosen ordering.

**Definition 11.2 (Fixed-Energy Sector Subspace).**
*Lean 4 Proof Strategy:*
Use `Submodule ℂ ℋ` to define the subspace. To formalize "coordinate span", we can use `Submodule.span ℂ {v | ∃ S, v = δ_S ∧ N(S) = N ∧ e(S) = K}`. Here, `δ_S` are the computational basis states corresponding to valid fermionic configurations `S`.

The fixed-energy fermionic subspace is defined exactly as the coordinate span:

$$
\mathcal{H}^N_K := \mathrm{span}_{\mathbb{C}} \{ \delta_S \mid N(S) = N \text{ and } e(S) = K \} \tag{11.2}
$$

#### 11.2 Regime R1: The Rectangle Bijection

**Lemma 11.3 (Regime R1: Exact Partition Counting).**
*Lean 4 Proof Strategy:*
Construct an explicit `Equiv` (bijection) between valid fermionic configurations `S` of energy `K` and integer partitions of `K`. Use `Finset.card_congr` to show the cardinalities match. The bounding condition `K ≤ min(h+N, h-N)` should be introduced as a hypothesis to ensure the bijection maps precisely to unrestricted partitions of `K`, since the physical "rectangle" of available states is not saturated. The proof relies on `Fintype.card` or `Module.finrank` matching `p(K)`.

To prove that $\dim(\mathcal{H}^N_K) = p(K)$, we do not rely on topological limits. For $n = h+N$ occupied modes, the non-decreasing displacements $d_i = s_i - g_i$ physically encode an integer partition fitting inside a rectangle of $n$ rows and $L-n$ columns.

We construct an explicit algebraic bijection between valid configurations $S$ and these bounded partitions. When the energy $K$ satisfies the **R1 Margin Condition**:

$$
K \le \min(h+N, h-N) \tag{11.3}
$$

the rectangle bounds are guaranteed never to be saturated. The bounded counting reduces exactly to the unrestricted integer partitions $\mathrm{Nat.Partition \ K}$, rigorously proving:

$$
\dim_{\mathbb{C}} (\mathcal{H}^N_K) = p(K) \tag{11.4}
$$

#### 11.3 Regime R2: Gram Induction and Completeness

**Lemma 11.4 (Regime R2: Bosonic Orthogonality).**
*Lean 4 Proof Strategy:*
Proceed by induction on the length (or total energy) of the partition `λ`. Use an auxiliary "pull-through" lemma (`commutator_through_word`) to evaluate inner products $\langle N \mid \prod \rho_{-n} \prod \rho_m \mid N \rangle_0$.
Each part $m$ satisfies $m \le K$, and any intermediate prefix product of creation modes has excitation energy bounded by $K$. Annihilating through the word never increases energy beyond $K$. Thus the effective mode cutoff is $M = K$, and the maximum intermediate energy is bounded by $K$. The R2 condition $2K + |N| \le h$ rigorously validates every intermediate Kac-Moody commutator step via the M2 margin.
Prove the normalization factor $z_\lambda$ by recursively applying the commutator $[\rho_m, \rho_{-m}] = m$.

To prove orthogonality, we compute the Gram matrix by commuting annihilation modes through the word of creation modes. For any partition $\lambda \vdash K$, every mode part satisfies $m \le K$.
When commuting a lowering mode $\rho_{-m}$ ($m \le K$) past a creation mode $\rho_n$ ($n \le K$), the commutator $[\rho_{-m}, \rho_n]$ acts on the remainder sub-word to the right of $\rho_n$. Because the total excitation energy of the partition word is at most $K$, this remainder has energy $E \le K - n$.
Consequently, the joint excursion for the commutator satisfies:
$$
m + n + E \le m + n + (K - n) = m + K \le 2K.
$$
Therefore, under the **R2 Margin Condition**:

$$
2K + \vert{}N\vert{} \le h \tag{11.5}
$$

we have $m + n + E + |N| \le 2K + |N| \le h$, which rigorously satisfies the M2 margin hypothesis for every off-diagonal commutator (and the M1 margin $2m + E + |N| \le 2K + |N| \le h$ for diagonal steps). A rigorous formal induction (commutator-through-a-word lemma) reduces the inner product to the vacuum, yielding the standard Hall inner product:

$$
\langle \lambda; N \mid \mu; N \rangle = \delta_{\lambda\mu} z_\lambda \tag{11.6}
$$

where the exact normalization is $z_\lambda = \prod m^{r_m} r_m!$.

**Theorem 11.5 (Haldane Completeness at Energy $K$).**
*Lean 4 Proof Strategy:*
Combine `Lemma 11.3` and `Lemma 11.4`. First, use `Lemma 11.4` (orthogonality with strictly positive norm $z_λ \ge 1$) to prove that the set of states `{|λ; N⟩}` is linearly independent. Then, observe that the cardinality of this set is `p(K)`. Since they belong to `ℋ^N_K` and their cardinality equals the dimension of `ℋ^N_K` (from `Lemma 11.3`), they must form a basis. Use Mathlib's linear algebra results (e.g., `basisOfLinearIndependentOfCardEqDim`) to formalize completeness over `ℂ`.

Because $z_\lambda \ge 1$, the norm of every partition state is strictly positive over $\mathbb{C}$, proving linear independence. Combining membership in $\mathcal{H}^N_K$, linear independence, and the exact dimension count established by the rectangle bijection, the set $\{|\lambda; N\rangle \mid \lambda \vdash K \}$ forms a complete orthogonal basis for the fixed-energy subspace $\mathcal{H}^N_K = H(N,K)$.

**Corollary 11.6 (Whole Budget Basis Assembly).**
The full fixed-charge budget subspace $B(N,K)$ decomposes as the orthogonal direct sum of fixed-energy spaces:

$$
B(N,K) = \bigoplus_{E=0}^K H(N,E) \tag{11.7}
$$

Because the R2 condition at $K$ ($2K + |N| \le h$) implies the R2 condition at every $E \le K$ ($2E + |N| \le 2K + |N| \le h$), applying Theorem 11.5 at each $0 \le E \le K$ yields that the disjoint union of partition bases:

$$
\mathcal{B}_{\text{basis}}(N,K) := \bigcup_{E=0}^K \{ |\lambda; N\rangle \mid \lambda \vdash E \} \tag{11.8}
$$

(where $E=0$ is spanned by the unique ground ket $|0; N\rangle = |N\rangle_0$) forms a complete orthogonal basis for the entire budget subspace $B(N,K)$.

*Lean 4 Proof Strategy:*
Formalize as an internal direct sum of `Submodule`s: `B(N,K) = ⨁_{E ≤ K} H(N,E)`. Use `Basis.sum` or linear combination of the bases of each $H(N,E)$ to construct the basis of $B(N,K)$. Prove that each $E \le K$ inherits $2E + |N| \le h$ from `2K + |N| ≤ h`.
