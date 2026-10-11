### Chapter 11: Haldane Completeness

We have established that density modes $\rho_m$ behave algebraically like independent bosonic creation and annihilation operators. To formalize **Haldane Completeness**—demonstrating that the collective bosonic density waves span the low-energy fermionic space—we implement the strict combinatorial counts and Gram induction defined in [Appendix A04](../appendices/a04_density_partitions_and_sugawara.md).

#### 11.1 Bosonic Partition States

Imagine the sector ground state $|N\rangle_0$ as the undisturbed Fermi sea. We add energy $K$ using combinations of density creation modes ($m > 0$). These correspond to integer partitions of $K$.

**Definition 11.1 (Bosonic Partition States).**
*Lean 4 Proof Strategy:*
Use `List.foldr` or `List.foldl` over a sorted list of integer parts to implement the ordered product of density creation modes $\rho_m$. The type for integer partitions could be `Nat.Partition K` from Mathlib. We need an auxiliary lemma showing that since $[\rho_m,\rho_n]=0$ for $m,n>0$ (Lemma 9.5), any permutation of the ordered product yields the exact same operator on the Hilbert space, ensuring the state depends only on the partition (multiplicities $r_m$) and not the ordering.

Let $K \in \mathbb{N}$. Let $\lambda \vdash K$ be an integer partition, represented by the multiplicities $r_m$ of each integer part $m \ge 1$. We construct the state using an explicit ordered product (e.g., a fold over a sorted list), because generic endomorphisms do not commute.

$$
\forall \lambda \vdash K, \quad |\lambda; N\rangle := \left( \overrightarrow{\prod_{m \ge 1}} \rho_m^{r_m} \right) |N\rangle_0 \tag{11.1}
$$

Because all positive density modes globally commute (Lemma 9.5), this state definition is ultimately independent of the chosen ordering.

**Definition 11.2 (Fixed-Energy Sector Subspace).**
*Lean 4 Proof Strategy:*
Use `Submodule ℂ ℋ` to define the subspace. To formalize "coordinate span", we can use `Submodule.span ℂ {v | ∃ S, v = δ_S ∧ N(S) = N ∧ e(S) = K}`. Here, $\delta_S$ are the computational basis states corresponding to valid fermionic configurations `S`.

The fixed-energy fermionic subspace is defined exactly as the coordinate span:

$$
\mathcal{H}^N_K := \mathrm{span}_{\mathbb{C}} \{ \delta_S \mid N(S) = N \text{ and } e(S) = K \} \tag{11.2}
$$

#### 11.2 Regime R1: The Rectangle Bijection

**Lemma 11.3 (Regime R1: Exact Partition Counting).**
*Lean 4 Proof Strategy:*
Construct an explicit `Equiv` (bijection) between valid fermionic configurations `S` of energy `K` and integer partitions of `K`. Use `Finset.card_congr` to show the cardinalities match. The bounding condition $K \le \min(h+N,h-N)$ should be introduced as a hypothesis to ensure the bijection maps precisely to unrestricted partitions of `K`, since the physical "rectangle" of available states is not saturated. The proof relies on `Fintype.card` or `Module.finrank` matching $p(K)$.

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
Use the right-remainder invariant: when passing a lowering mode m across a creator n in a word of total energy at most K, the remainder has energy E ≤ K−n. Hence m+n+E ≤ m+K ≤ 2K. Preserve this invariant through the induction, instead of applying a uniform cutoff bound to the whole prefix.
Prove the normalization factor $z_\lambda$ by recursively applying the commutator $[\rho_{-m}, \rho_m] = m I$.

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

we have $m + n + E + |N| \le 2K + |N| \le h$, which rigorously satisfies the M2 margin hypothesis for every off-diagonal commutator (and the M1 margin $m + E + |N| \le 2K + |N| \le h$ for diagonal steps). A rigorous formal induction (commutator-through-a-word lemma) reduces the inner product to the vacuum, yielding the standard Hall inner product:

$$
\langle \lambda; N \mid \mu; N \rangle = \delta_{\lambda\mu} z_\lambda \tag{11.6}
$$

where the exact normalization is $z_\lambda = \prod m^{r_m} r_m!$.

**Theorem 11.5 (Haldane Completeness at Energy $K$).**
*Lean 4 Proof Strategy:*
Combine Lemma 11.3 and Lemma 11.4. First, use Lemma 11.4 (orthogonality with strictly positive norm $z_\lambda\ge1$) to prove that the set of states $\{|\lambda;N\rangle\}$ is linearly independent. Then, observe that the cardinality of this set is $p(K)$. Since they belong to $\mathcal H^N_K$ and their cardinality equals the dimension of $\mathcal H^N_K$ (from Lemma 11.3), they must form a basis. Use Mathlib's linear algebra results (e.g., `basisOfLinearIndependentOfCardEqFinrank'` (checked in the installed Mathlib; supply linear independence and cardinality = finrank)) to formalize completeness over `ℂ`.

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
Index the budget basis by a dependent pair of energy E ≤ K and a partition of E. Prove linear independence using orthogonality across energy blocks and the Gram lemma within each block; prove spanning by the coordinate energy decomposition. Construct a basis from these proved properties rather than relying on an unverified `Basis.sum` name.

#### 11.4 Constructive realization in Lean

The construction described here is proved and promoted to Core. Its declarations have complete proofs and use only the permitted standard axioms; the formal companions record validation evidence.

The [partition construction](../../Bosonize/Core/A04PartitionCombinatorics.lean) and [CH11 construction](../../Bosonize/Core/Ch11HaldaneCompleteness.lean), with their [A04 companion](../../docs/companion/Bosonize/Core/A04PartitionCombinatorics.md) and [CH11 companion](../../docs/companion/Bosonize/Core/Ch11HaldaneCompleteness.md), give the finite realization of the theory above. The proof-strategy paragraphs remain reference guidance; the construction uses the actual occupation coordinates and density operators already introduced in Chapters 7 and 9.

The ambient Hilbert space is the finite complex space with orthonormal basis $\delta_S$, where $S$ ranges over subsets of the signed momentum band

$$
B=\{-h+1,\ldots,h\},\qquad h>0.
$$

The sector charge is $N=|S|-h$, with $-h\le N\le h$. Excitation is measured relative to the ground configuration of that same charge, using the existing sea subtraction and ground-energy shift $N(N+1)/2$. Thus the energies in this chapter are integer excitations. The previously proved cancellation of a uniform physical momentum offset in a fixed-charge excitation, and the matching twisted Fourier dictionary for the density bilinears, continue to apply. These cancellations do not change the sea or assert cancellation of the absolute sector energy.

**From occupations to partitions, with an explicit inverse.** Order the occupied labels as $s_0<\cdots<s_{n-1}$, where $n=h+N$, and compare them with the consecutive ground labels $g_i=-h+1+i$. Their displacements satisfy

$$
0\le d_0\le\cdots\le d_{n-1}\le 2h-n,
\qquad d_i=s_i-g_i,
\qquad e(S)=\sum_{i=0}^{n-1}d_i.
$$

Discarding the zero displacements gives the positive parts of a partition of $e(S)$. It fits the rectangle with $n$ rows and $2h-n$ columns. Conversely, given such a partition, sort its parts in ascending order, prepend enough zeros to obtain exactly $n$ entries, and set

$$
s_i=-h+1+i+d_i.
$$

The rectangle bound puts every reconstructed label in $B$; monotonicity of the displacements makes these labels strictly increasing. Their occupation set has exactly $n$ elements. Its sorted labels recover the formula above, so its charge, energy and displacement partition are the prescribed ones. In the other direction, restoring the discarded zeros recovers the entire original displacement list and hence the original occupation set. Both inverse identities are established, including the empty and full sectors.

Every positive part of a partition of $K$ is at most $K$, and the number of its parts is at most $K$. Consequently R1 ensures that every partition of $K$ fits the rectangle, and the actual occupation configurations at energy $K$ are in bijection with all partitions of $K$. Restricting the orthonormal occupation basis to these coordinates yields $\dim H(N,K)=p(K)$. Equality is allowed in R1: a partition may reach a rectangle boundary. The intended meaning of the earlier phrase “never to be saturated” is that the rectangle excludes no partition of $K$, not that every bound is strict.

**The physical density states and their Gram matrix.** The construction takes a descending list $[m_1,\ldots,m_r]$ of a partition's positive parts and forms

$$
W([m_1,\ldots,m_r])
=\rho_{m_1}\cdots\rho_{m_r}|N\rangle_0.
$$

This is a written product, so its rightmost current acts first. Positive currents commute on the whole ambient carrier, giving independence of the chosen ordering. Exact grading places the resulting vector in $H(N,\sum_i m_i)$; an upper budget bound alone would not establish this equality of energy.

For the Gram calculation, move a lowering current through the written product. At a step involving the creator $\rho_n$, its input is the remaining word to the right, of energy $E$. If the whole creator word has energy at most $K$, then $n+E\le K$. For $m\le K$, R2 gives

$$
m+n+E+|N|\le m+K+|N|\le 2K+|N|\le h.
$$

The restricted commutator therefore applies to precisely this remainder. Its diagonal coefficient is $+m$ and its off-diagonal coefficient is zero. Repeating the step and using $\rho_{-m}|N\rangle_0=0$ gives a contraction for each occurrence of $m$. Since the creators commute, removing any matching occurrence gives the same state, so the contraction becomes

$$
\rho_{-m}W(w)=m\,r_m(w)\,W(w\setminus\{m\}).
$$

Here $w$ has positive parts and total energy at most $K$, $0<m\le K$, and R2 holds at $K$. The formula includes the zero result when $m$ does not occur. Actual Hilbert adjoints move creators from the left side of an inner product to lowering currents on the right. Induction then gives the diagonal Gram formula, with

$$
\|\,|\lambda;N\rangle\,\|^2
=z_\lambda=\prod_{m\ge1}m^{r_m}r_m!>0.
$$

Thus $z_\lambda$ is the squared norm. Its factorial counts successive matching contractions; positivity follows from positive mode weights. The argument also treats creator words of different total energies, yielding orthogonality across the energy blocks.

**Completeness and assembly of the budget.** R2 implies R1. The Gram formula proves that the actual density states are nonzero and linearly independent; their exact-energy membership and the independently established dimension count then give spanning and a basis of $H(N,K)$. The basis vectors are precisely the density products defined above.

For the whole budget, label a vector by a pair $(E,\lambda)$ with $0\le E\le K$ and $\lambda\vdash E$. R2 at $K$ implies the corresponding condition at every such $E$. The Gram formula gives independence of the entire family. Each coordinate ket in $B(N,K)$ has a nonnegative excitation $E\le K$, so fixed-energy spanning puts it in the span of the family. This proves spanning of the budget and constructs its orthogonal basis, including the ground at $E=0$.

R1 is the combinatorial counting regime; R2 is the stronger regime used for the density Gram formula and completeness. These statements concern finite occupation spaces and the action of actual currents on their specified vectors. Sugawara energy equivalence remains the separate Chapter 12 task.
