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
Proceed by induction on the length (or total energy) of the partition `λ`. Use an auxiliary "pull-through" lemma (`commutator_through_word`) to evaluate inner products like `⟨0| ρ_{m_1} ... ρ_{m_k} ρ_{-n_1} ... ρ_{-n_l} |0⟩`. The `R2 Margin Condition` (`2K + |N| ≤ h`) must be passed as an explicit assumption to justify the use of Kac-Moody algebra commutators without hitting the edge of the finite Dirac sea. Prove the normalization factor `z_λ` by recursively applying the commutator `[ρ_m, ρ_{-m}] = m`.

To prove orthogonality, we compute the Gram matrix by commuting annihilation modes through the word of creation modes. The intermediate mathematical states acquire transient energies. The required conservative margin must track the maximum upward excursion of these intermediate prefix products. If the parameters satisfy the **R2 Margin Condition**:

$$
2K + \vert{}N\vert{} \le h \tag{11.5}
$$

then every intermediate step of the nested Kac-Moody commutators is justified by the M2 margin. A rigorous formal induction (commutator-through-a-word lemma) reduces the inner product to the vacuum, yielding the standard Hall inner product:

$$
\langle \lambda; N \mid \mu; N \rangle = \delta_{\lambda\mu} z_\lambda \tag{11.6}
$$

where the exact normalization is $z_\lambda = \prod m^{r_m} r_m!$.

**Theorem 11.5 (Haldane Completeness).**
*Lean 4 Proof Strategy:*
Combine `Lemma 11.3` and `Lemma 11.4`. First, use `Lemma 11.4` (orthogonality with strictly positive norm $z_λ \ge 1$) to prove that the set of states `{|λ; N⟩}` is linearly independent. Then, observe that the cardinality of this set is `p(K)`. Since they belong to `ℋ^N_K` and their cardinality equals the dimension of `ℋ^N_K` (from `Lemma 11.3`), they must form a basis. Use Mathlib's linear algebra results (e.g., `basisOfLinearIndependentOfCardEqDim`) to formalize completeness over `ℂ`.

Because $z_\lambda \ge 1$, the norm of every partition state is strictly positive over $\mathbb{C}$, proving linear independence. Combining membership in $\mathcal{H}^N_K$, linear independence, and the exact dimension count established by the rectangle bijection, the set $\{|\lambda; N\rangle \mid \lambda \vdash K \}$ forms a complete orthogonal basis for the fermionic subspace $\mathcal{H}^N_K$.
