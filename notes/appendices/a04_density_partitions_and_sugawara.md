# Appendix A04 proposal: truncated density modes, partitions, and Sugawara

## Density definition and finite edge identity

A shift is an integer, not a band element. Define the valid-pair set

$$
 D_m=\{(p,k)\in B\times B:p=k+m\},\qquad
 \rho_m=\sum_{(p,k)\in D_m}c_p^\dagger c_k^{\phantom{\dagger}}.
$$

*Lean 4 Proof Strategy:*
**Definition (Density modes):** Filter the finite product `Ch01.Band L × Ch01.Band L` with `p.val = k.val + m`, where m is an integer. Sum the CAR bilinears on that domain. Retain the frozen signed band; neither residue addition nor bare zero-based `Fin L` labels describe nonwrapping integer shifts.

Introduce a one-particle partial shift matrix T_m, and the second-quantization map dΓ taking a matrix A to $\sum_{p,k}A_{pk}c_p^\dagger c_k^{\phantom{\dagger}}$. Prove $d\Gamma([A,B])=[d\Gamma(A),d\Gamma(B)]$ from the CAR bilinear identity. Then ρ_m=dΓ(T_m). This reduces many boundary calculations to finite matrices/intervals before lifting to Fock space.

*Lean 4 Proof Strategy:*
**Definition (Partial shift matrix and dΓ):** Index both matrix axes by `Ch01.Band L`, define entries using integer-label equality, and define dΓ by scalar-weighted CAR bilinears. It is a linear Lie map, not an associative algebra homomorphism.
**Lemma (dΓ Lie algebra homomorphism):** Expand the commutator $[d\Gamma(A),d\Gamma(B)]$ into a quadruple sum. Use the CAR bilinear identity $[c_p^\dagger c_k^{\phantom{\dagger}}, c_q^\dagger c_l^{\phantom{\dagger}}] = \delta_{kq} c_p^\dagger c_l^{\phantom{\dagger}} - \delta_{pl} c_q^\dagger c_k^{\phantom{\dagger}}$ to reduce the expression. Collect terms to show it equals $d\Gamma(AB-BA)=d\Gamma([A,B])$.

The density-kinematics and current-margin constructions now establish the following chain; the proof strategies below retain the reference design:

1. T_m and ρ_m vanish for |m|≥L.
2. T_m†=T_−m and ρ_m†=ρ_−m by reindexing valid pairs.
3. Same-sign partial shifts commute; for nonnegative m,n, T_m T_n=T_(m+n). Hence positive density modes commute globally, not only on a budget.
4. Opposite shifts have a diagonal edge commutator; derive the bottom-minus-top occupation formula for 1≤m≤h.
5. General opposite-sign unequal shifts have explicitly supported edge hoppings; identify both source and target frozen regions.
6. Apply occupation/hop laws to frozen margins and lift from occupation kets to the budget span.

*Lean 4 Proof Strategy:*
**Lemma (Density Mode Properties):**

1. Prove $D_m = \emptyset$ for $|m| \geq L$ by the bounds $-h+1\le p.\mathrm{val},k.\mathrm{val}\le h$ and their maximal difference L−1. Hence the sum is empty.
2. For the adjoint, use the property $(c_p^\dagger c_k^{\phantom{\dagger}})^\dagger = c_k^\dagger c_p^{\phantom{\dagger}}$. The index change `p = k + m` maps to `k = p - m`, so `D_m` reflects to `D_{-m}`.
3. For m,n≥0, show matrix multiplication $T_m T_n = T_{m+n}$ by tracking indices. Mixed-sign composition retains an intermediate-in-band indicator. Then $[\rho_m, \rho_n] = dΓ([T_m, T_n]) = 0$ since `T_m` and `T_n` commute.
4. For opposite shifts, evaluate $[T_m,T_{-m}]$ explicitly to find it is diagonal, representing the difference in occupations of the top and bottom edge states. Lift to $\rho_m$ via `dΓ`.
5. For unequal opposite shifts, compute $[T_m,T_{-n}]$ to find hopping terms strictly located at the boundaries of the band.
6. To lift these identities, show that on the restricted budget span (e.g., specific margins of holes and particles), the boundary terms evaluate deterministically or vanish, leveraging the algebraic identities established for `T_m`. This requires an auxiliary lemma about the action of boundary $c_k^\dagger c_k^{\phantom{\dagger}}$ operators on states within the budget span.

This avoids proving the general Schwinger theorem directly by a large double CAR sum. Every restricted scalar identity must remain a theorem about action on input vectors, not an endomorphism CCR of a finite budget carrier.

## Energy and linear independence

The bare Hamiltonian is H₀=Σ k n_k. Its vacuum eigenvalue is $-h(h-1)/2$, not zero unless h=1. Introduce the normal-ordered Hamiltonian P̂=H₀−EΩ I once. Density covariance holds for both; the eigenvalues of ρ_mΩ under the bare H₀ are EΩ+m. This corrects chapter 9's proof sketch without changing its intended linear-independence result.

*Lean 4 Proof Strategy:*
**Definition (Normal-ordered Hamiltonian):** Define $H_0 = \sum_k k c_k^\dagger c_k^{\phantom{\dagger}}$. Calculate the vacuum energy $E_\Omega = \langle \Omega | H_0 | \Omega \rangle$ and prove it equals $-h(h-1)/2$. Define $\hat{P} = H_0 - E_\Omega I$.
**Theorem (Density covariance):** Prove $[H_0, \rho_m] = m \rho_m$ by expanding and using CAR. Then apply this to the vacuum state to show $H_0 (\rho_m \Omega) = (E_\Omega + m) \rho_m \Omega$.

First prove the explicit vacuum norm $\|\rho_m\Omega\|^2=m$ for 1≤m≤h using orthogonal hop kets. Then distinct energy eigenvalues give linear independence. Using the Schwinger term to prove the first nonzero action would risk a circular dependency if the Schwinger proof itself uses nondegeneracy.

*Lean 4 Proof Strategy:*
**Lemma (Vacuum norm of density modes):** Compute ρmΩ as the sum of the m allowed occupation-hop kets, using CAR signs. Distinct hops are orthogonal and each sign has squared norm 1, so the norm squared is m. This establishes first nonzero action independently of the restricted scalar CCR now proved in Chapter 10.
**Theorem (Linear independence of density excitations):** Since $\rho_m \Omega$ has eigenvalue $E_\Omega + m$ under `H_0`, and $||\rho_m \Omega|| > 0$ for $1 \le m \le h$, the states for different `m` belong to distinct eigenspaces of a Hermitian operator, and thus are linearly independent.

## Partitions and completeness

For n=h+N occupied modes, their nondecreasing displacements d_i=s_i−g_i encode a partition of total energy E fitting a rectangle with n rows and L−n columns. Construct both directions and prove the inverse identities and energy preservation. This gives exact finite counting before passing to unrestricted partitions under E≤min(n,L−n).

*Lean 4 Proof Strategy:*
**Theorem (Displacement partition bijection):** Define a mapping from valid momentum configurations (displacements `d_i`) to integer partitions bounded by `n` rows and `L-n` columns. Prove it is a bijection by constructing the explicit inverse mapping. Show that $\sum d_i = E$, matching the partition weight. Use `Finset.sum` over the modes and verify energy preservation.

Use `Nat.Partition E`, whose parts are a multiset of positive naturals, or finitely supported multiplicities r with Σ m r_m=E. The installed module is `Mathlib.Combinatorics.Enumerative.Partition.Basic`; the source's suggested module path and `Nat.Partition.partitions` name should not be assumed to exist. The installed type has a finite instance, so a finite enumeration can use `Finset.univ` when needed.

Construct partition-state products as ordered lists/folds in the noncommutative endomorphism algebra. Once same-sign commutativity is proved, establish independence of the chosen ordering. This is more appropriate than requiring a false `CommMonoid` instance on all endomorphisms.

*Lean 4 Proof Strategy:*
**Definition (Partition-state products):** Given a partition represented by frequencies `r_m`, define the state $(\prod_m \rho_m^{r_m}) \Omega$. Formalize this using a list of parts $[m_1, m_2, \dots]$ sorted descending, and fold the application of $\rho_m$ over the vacuum ket.
**Theorem (Ordering independence):** Use the previously proved $[\rho_m, \rho_n] = 0$ (for `m, n > 0`) to show by induction over list permutations that any ordering of the same multiset of parts yields the identical state vector.

For the Gram theorem, first prove a commutator-through-a-word lemma with the right-remainder energy invariant. When commuting $\rho_{-m}$ ($m \le K$) past $\rho_n$ ($n \le K$), the remainder to the right has energy $E \le K - n$, so the joint excursion satisfies $m + n + E \le m + K \le 2K$. Under the R2 condition $2K + |N| \le h$, the M2 hypothesis $|m| + |n| + E + |N| \le h$ is satisfied at every step. Then prove the vacuum reduction recursively. The norm is $z_\lambda = \prod m^{r_m} r_m!$, nonzero over $\mathbb{C}$. Completeness follows from membership, linear independence, and the rectangle-counting bijection. A mere dimension count without the bijection is a substantial missing proof.

*Lean 4 Proof Strategy:*
**Lemma (Commutator-through-a-word and vacuum reduction):** Prove $[\rho_{-m}, \prod \rho_{m_i}]$ recursively on the list `[m_i]`. Each pass leaves a term proportional to `m` times the remaining product if `m_i = m`. Use induction on the length of the list, applying the edge commutator identities.
**Theorem (Gram theorem and Completeness):** Use the word commutator lemma to calculate the inner product of two partition states $\langle \Omega | \prod \rho_{-m_i} \prod \rho_{n_j} | \Omega \rangle$. Show it equals $\delta_{\lambda, \mu} z_\lambda$. Conclude linear independence since the Gram matrix is diagonal with positive entries. Completeness then follows since the dimension of the subspace matches the cardinality of the bounded partitions (from the bijection theorem).

## Sugawara statement repair

Write H_sug^(M)=Σ_(m=1)^M ρ_mρ_−m, identifying M explicitly. The assertion that h−1 includes all nonzero density modes is false: nonzero modes can occur up to L−1. For its action on B(N,K), M≥K is a useful sufficient cutoff because lowering modes m>K annihilate the input.

*Lean 4 Proof Strategy:*
**Definition (Sugawara Hamiltonian):** Define $H_{sug}^{(M)} = \sum_{m=1}^M \rho_m \rho_{-m}$. Formulate it using `Finset.sum` over $1 \le m \le M$ acting as an operator on the Hilbert space.

*(Historical Audit Note: In the original unrevised draft, Chapter 12 attempted to prove Sugawara equivalence by using an unrestricted mode commutation identity, which failed at small h/cutoffs, e.g. at h=1, K=N=0).*

A safe, non-circular proof order is:

1. Prove Haldane completeness for fixed-energy subspaces: for each $0 \le E \le K$, $\{|\lambda; N\rangle \mid \lambda \vdash E\}$ forms an orthogonal basis of $H(N,E)$.
2. Assemble the whole budget basis of $B(N,K) = \bigoplus_{E=0}^K H(N,E)$ as the disjoint union $\bigcup_{E=0}^K \{|\lambda; N\rangle \mid \lambda \vdash E\}$ (with $E=0$ spanned by the ground ket $|N\rangle_0$).
3. Evaluate $H_{\text{sug}}^{(M)}$ on each partition state of energy $E \le K \le M$, obtaining $H_{\text{sug}}^{(M)}|\lambda; N\rangle = E |\lambda; N\rangle = \hat{E}|\lambda; N\rangle$.
4. Extend by linearity across the whole budget basis to establish $\hat{E}\psi = H_{\text{sug}}^{(M)}\psi$ for all $\psi \in B(N,K)$.
5. Derive commutation as a corollary on a specified range of $n$ for which both the input and shifted output lie in budgets where this equivalence has been proved.

*Lean 4 Proof Strategy:*
**Theorem (Sugawara equivalence on whole budget spans):**

1. **Lemma:** Prove $H_{sug}^{(M)} |\lambda\rangle = E |\lambda\rangle$ for any partition state $|\lambda\rangle$ of energy $E \le K$, provided $M\ge K$.
2. **Whole budget basis assembly:** Construct `Basis` of $B(N,K)$ from the direct sum $\bigoplus_{E\le K}H(N,E)$.
3. **Theorem:** Since $H_{\mathrm{sug}}^{(M)}$ and $\hat{E}$ agree on every basis vector in $\mathcal{B}_{basis}(N,K)$, $\hat{E} \psi = H_{sug}^{(M)} \psi$ on the entire budget $B(N,K)$.
4. **Corollary:** For the commutation relation $[H_{\mathrm{sug}}^{(M)}, \rho_n] \psi = n \rho_n \psi$, note that if $\psi \in B(N,K)$, then $\rho_n \psi \in B(N, K+n)$. Assuming enlarged margins $2(K+n) + |N| \le h$ and cutoff $M \ge K+n$, apply the eigenvalue equivalence to both $\psi$ and $\rho_n \psi$.

For example, an upward shift n>0 needs an equivalence theorem also on B(N,K+n), a cutoff M≥K+n, and a sufficient enlarged margin such as $2(K+n)+|N|\le h$. This is a sufficient repaired corollary, not a claim of optimal margins. It avoids using an overstrong commutation lemma to establish the equivalence circularly.

Keep the ground-energy shift $N(N+1)/2$. Chapter 17 now explicitly subtracts chemical potential $\mu=\pi v_F/L$ in physical units; this accounts for its symmetric N² form. The raw-quartic/current relation is the separate exact sea-Wick correction of Chapter 17, Lemma 17.4a; it does not use Sugawara or scalar CCR.

*Proof-design invariant:* Gram pull-through uses the right remainder E≤K−n, giving m+n+E≤m+K≤2K. For Sugawara, split off inactive modes m>K: their lowering action on the right is zero by grading, so no extra margin depending on those inactive modes is needed. Mixed-sign one-particle shift compositions retain the intermediate-in-band indicator.

## Constructive realization of the finite density-kinematics portion

The implemented portion of this appendix isolates the finite one-particle calculation and its lift to the concrete CAR representation. The restricted scalar CCR is now proved in Chapter 10 using the current-margin construction described below. The partition bijection, Gram theorem, completeness and Sugawara arguments above remain reference theory and future formalization obligations. The [A04 Lean source](../../Bosonize/Core/A04DensityKinematics.lean) and [formal companion](../../docs/companion/Bosonize/Core/A04DensityKinematics.md) describe this completed kinematic portion; Chapter 9 separately develops its density grading and first sea norm.

For any finite ring length $L$, let $B$ be the frozen signed integer band defined by $-L<2k\le L$. At even length $L=2h$ this is $\{-h+1,\ldots,h\}$, retaining the positive Nyquist representative. Matrices are indexed directly by $B$ on both axes. The partial shift has coefficient

$$
(T_m)_{p,k}=\mathbf 1_{p=k+m},\qquad m\in\mathbb Z.
$$

There is no residue addition in this definition. Expanding a matrix product reveals the unique possible intermediate label $k+n$, and gives the exact entry formula

$$
(T_mT_n)_{p,k}
=\mathbf 1_{p=k+m+n}\,\mathbf 1_{k+n\in B}.
$$

This intermediate indicator is the essential finite-boundary information. For transfers with the same sign, the intermediate lies between source and target. The product then equals $T_{m+n}$ globally. The construction proves this for both nonnegative and nonpositive transfers. For mixed signs the indicator remains, and the commutator has coefficient

$$
[T_m,T_n]_{p,k}
=\mathbf 1_{p=k+m+n}
 \bigl(\mathbf 1_{k+n\in B}-\mathbf 1_{k+m\in B}\bigr).
$$

Thus a nonzero edge coefficient requires the expected transfer and exactly one admissible intermediate. This expression explains why a globally scalar finite-dimensional current CCR would discard real boundary data.

The boundary support is particularly transparent for $L=2h$, with endpoints $a=-h+1$ and $b=h$. For nonnegative $m,n$,

$$
[T_{-m},T_n]_{p,k}
=\mathbf 1_{p=k+n-m}
 \bigl(\mathbf 1_{k<a+m}-\mathbf 1_{b-n<k}\bigr).
$$

For a nonzero entry, either both source and target lie near the bottom, with $k<a+m$ and $p<a+n$, or both lie near the top, with $b-n<k$ and $b-m<p$. Recording both endpoints is necessary for the current-margin Pauli-blocking arguments: knowing only the source location does not prove that an off-diagonal hop vanishes on a frozen occupation margin. When $m=n$, the edge matrix is diagonal and gives bottom occupation minus top occupation. Reversing commutator order reverses this sign.

The other one-particle results follow from the same entries. The zero shift is the identity matrix. Conjugate transpose gives $T_m^\dagger=T_{-m}$ because transposition exchanges source and target. Since the signed band has diameter at most $L-1$, $T_m=0$ and the valid-pair set is empty for $|m|\ge L$. Conversely, any concrete allowed source-target pair witnesses that its shift matrix is nonzero. These generic statements include odd lengths and the empty band at $L=0$; even length is needed only when using the explicit $h$-endpoint formulas.

Second quantization is defined on any ordered finite mode set by the actual finite sum

$$
d\Gamma(A)=\sum_{p,k} A_{p,k}\,c_p^\dagger c_k^{\phantom{\dagger}}.
$$

The CAR bilinear identity contracts the four-index commutator sum to the two matrix products, proving

$$
[d\Gamma(A),d\Gamma(B)]=d\Gamma(AB-BA).
$$

The construction is complex linear and respects actual Hilbert adjoints: $d\Gamma(A)^\dagger=d\Gamma(A^\dagger)$. A diagonal matrix lifts to the corresponding weighted occupation observable. In particular, $d\Gamma(I)=\hat N$, so the Lie identity must not be mistaken for an associative, unital algebra homomorphism. The finite edge formulas lift as commutator identities even though products do not lift multiplicatively.

These exact matrix and CAR results supply the boundary calculations used by the completed current-margin and Chapter 10 proofs. Frozen edge occupations, unequal-shift hop annihilation and signed suffix-energy accounting are now proved on the prescribed budget spans. No partition counting, bosonic Gram formula or Sugawara equivalence follows merely from these current-algebra results.


## Constructive realization of the current-margin portion

The [A04 current-margin source](../../Bosonize/Core/A04CurrentMargins.lean) and [formal companion](../../docs/companion/Bosonize/Core/A04CurrentMargins.md) complete the passage from finite edge matrices to restricted action. [Chapter 10's constructive lecture](../md/ch10_Heisenberg_algebra.md#106-constructive-realization-in-lean), [source](../../Bosonize/Core/Ch10Heisenberg.lean) and [companion](../../docs/companion/Bosonize/Core/Ch10Heisenberg.md) then combine this support into the signed current algebra and word-margin theorems. This extends the completed kinematic portion above while leaving the partition and Sugawara program visible as future work.

For $h>0$, the budget is the span of actual occupation kets of relative charge $N$ and excitation at most the signed bound $K$. Equality of linear actions on those generators extends to the entire span. The frozen-occupation inequalities become concrete operator laws:

$$
k\le N-K\ \Longrightarrow\ n_k\psi=\psi,
\qquad N+K<k\ \Longrightarrow\ n_k\psi=0,
\qquad \psi\in B(N,K).
$$

An empty source blocks $c_p^\dagger c_k^{\phantom{\dagger}}$; a full destination blocks it only for $p\ne k$. The unequal mixed-shift support calculation supplies both endpoints and the nonzero transfer, permitting precisely these two laws to eliminate all residual hops under $|m|+|n|+K+|N|\le h$.

The diagonal calculation is separate and sharper. Filtering the signed band gives bottom $\{-h+1,\ldots,-h+m\}$ and top $\{h-m+1,\ldots,h\}$, each of cardinality $m$ for $0\le m\le h$. The CAR lift of their diagonal difference is the full-space edge observable. Under $m+K+|N|\le h$ with $K\ge0$, every bottom number operator contributes $\psi$ and every top one contributes zero, yielding $m\psi$. Chapter 10 handles negative budgets by proving their only vector is zero before using natural edge cardinalities. It derives the coefficient $-m\delta_{m+n,0}$ by reversing the commutator where needed, and proves that subtracting the central normal-ordering scalar preserves it.

The word construction independently proves exact signed target budgets and then bounds each applied prefix by its maximum cumulative upward excursion. A written product is reversed to obtain application order, so these prefixes are its actual right suffixes. The resulting uniform bound permits a CCR at the suffix input; it does not establish the partition Gram induction or completeness automatically. Each future pull-through argument must verify its own remainder and margin.

The reconstructed partial-current theorem retains an arbitrary boundary twist through the matching twisted Fourier dictionary. It does not identify the cyclic site Fourier density with a partial current: that density retains its wrap remainder. Nonzero admissible sector grounds witness inhabited nonnegative budgets, while the nonzero empty occupation ket gives a concrete obstruction to any global nonzero scalar current CCR. The completed portion is therefore an exact finite, restricted current realization. The partition bijection, ordering and Gram arguments for partition-state products, completeness and Sugawara equivalence above still require their own proofs.
