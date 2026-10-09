# Appendix A04 proposal: truncated density modes, partitions, and Sugawara

## Density definition and finite edge identity

A shift is an integer, not a band element. Define the valid-pair set

\[
 D_m=\{(p,k)\in B\times B:p=k+m\},\qquad
 \rho_m=\sum_{(p,k)\in D_m}c_p^\dagger c_k.
\]

*Lean 4 Proof Strategy:*
**Definition (Density modes):** Define `D_m` using `Finset.filter` on `Finset.product univ univ` with the condition `p = k + m`, ensuring `p` and `k` are in the band `B` (e.g., `Fin L`). Define `ρ_m` by folding the creation and annihilation operators over this `Finset`. Avoid wrapping addition (`+` modulo `L`) by treating `p, k` as integers or casting to `Int` before checking equality `p = k + m`.

Introduce a one-particle partial shift matrix T_m, and the second-quantization map dΓ taking a matrix A to `Σ A_pk c_p†c_k`. Prove `dΓ([A,B])=[dΓ(A),dΓ(B)]` from the CAR bilinear identity. Then ρ_m=dΓ(T_m). This reduces many boundary calculations to finite matrices/intervals before lifting to Fock space.

*Lean 4 Proof Strategy:*
**Definition (Partial shift matrix and dΓ):** Define `T_m` as an `L \times L` matrix where `(T_m)_{p,k} = 1` if `p = k + m` and `0` otherwise. Define `dΓ(A)` as a linear map from `Matrix (Fin L) (Fin L) ℂ` to the CAR algebra by a double sum over `p, k` of `A_{p,k} c_p^\dagger c_k`.
**Lemma (dΓ Lie algebra homomorphism):** Expand the commutator `[dΓ(A), dΓ(B)]` into a quadruple sum. Use the CAR bilinear identity `[c_p^\dagger c_k, c_q^\dagger c_l] = \delta_{kq} c_p^\dagger c_l - \delta_{pl} c_q^\dagger c_k` to reduce the expression. Collect terms to show it equals `dΓ(A B - B A) = dΓ([A, B])`.

The next lemma chain should establish:

1. T_m and ρ_m vanish for |m|≥L.
2. T_m†=T_−m and ρ_m†=ρ_−m by reindexing valid pairs.
3. Same-sign partial shifts commute; for nonnegative m,n, T_m T_n=T_(m+n). Hence positive density modes commute globally, not only on a budget.
4. Opposite shifts have a diagonal edge commutator; derive the bottom-minus-top occupation formula for 1≤m≤h.
5. General opposite-sign unequal shifts have explicitly supported edge hoppings; identify both source and target frozen regions.
6. Apply occupation/hop laws to frozen margins and lift from occupation kets to the budget span.

*Lean 4 Proof Strategy:*
**Lemma (Density Mode Properties):**
1. Prove `D_m = \emptyset` for `|m| \geq L` because `p, k \in [0, L-1]`. Hence the sum is empty.
2. For the adjoint, use the property `(c_p^\dagger c_k)^\dagger = c_k^\dagger c_p`. The index change `p = k + m` maps to `k = p - m`, so `D_m` reflects to `D_{-m}`.
3. Show matrix multiplication `T_m T_n = T_{m+n}` by tracking indices. Then `[\rho_m, \rho_n] = dΓ([T_m, T_n]) = 0` since `T_m` and `T_n` commute.
4. For opposite shifts, evaluate `[T_m, T_{-m}]` explicitly to find it is diagonal, representing the difference in occupations of the top and bottom edge states. Lift to `\rho_m` via `dΓ`.
5. For unequal opposite shifts, compute `[T_m, T_{-n}]` to find hopping terms strictly located at the boundaries of the band.
6. To lift these identities, show that on the restricted budget span (e.g., specific margins of holes and particles), the boundary terms evaluate deterministically or vanish, leveraging the algebraic identities established for `T_m`. This requires an auxiliary lemma about the action of boundary `c_k^\dagger c_k` operators on states within the budget span.

This avoids proving the general Schwinger theorem directly by a large double CAR sum. Every restricted scalar identity must remain a theorem about action on input vectors, not an endomorphism CCR of a finite budget carrier.

## Energy and linear independence

The bare Hamiltonian is H₀=Σ k n_k. Its vacuum eigenvalue is `−h(h−1)/2`, not zero unless h=1. Introduce the normal-ordered Hamiltonian P̂=H₀−EΩ I once. Density covariance holds for both; the eigenvalues of ρ_mΩ under the bare H₀ are EΩ+m. This corrects chapter 9's proof sketch without changing its intended linear-independence result.

*Lean 4 Proof Strategy:*
**Definition (Normal-ordered Hamiltonian):** Define `H_0 = \sum_k k c_k^\dagger c_k`. Calculate the vacuum energy `E_\Omega = \langle \Omega | H_0 | \Omega \rangle` and prove it equals `-h(h-1)/2`. Define `\hat{P} = H_0 - E_\Omega I`.
**Theorem (Density covariance):** Prove `[H_0, \rho_m] = m \rho_m` by expanding and using CAR. Then apply this to the vacuum state to show `H_0 (\rho_m \Omega) = (E_\Omega + m) \rho_m \Omega`.

First prove the explicit vacuum norm `||ρ_m Ω||²=m` for 1≤m≤h using orthogonal hop kets. Then distinct energy eigenvalues give linear independence. Using the Schwinger term to prove the first nonzero action would risk a circular dependency if the Schwinger proof itself uses nondegeneracy.

*Lean 4 Proof Strategy:*
**Lemma (Vacuum norm of density modes):** Expand `||\rho_m \Omega||^2 = \langle \Omega | \rho_{-m} \rho_m | \Omega \rangle`. Use the commutator `[\rho_{-m}, \rho_m]` on the vacuum. Since `\rho_{-m}` annihilates the vacuum for `m > 0`, it reduces to the expectation value of the commutator, which by the edge occupation formula is precisely `m`.
**Theorem (Linear independence of density excitations):** Since `\rho_m \Omega` has eigenvalue `E_\Omega + m` under `H_0`, and `||\rho_m \Omega|| > 0` for `1 \le m \le h`, the states for different `m` belong to distinct eigenspaces of a Hermitian operator, and thus are linearly independent.

## Partitions and completeness

For n=h+N occupied modes, their nondecreasing displacements d_i=s_i−g_i encode a partition of total energy E fitting a rectangle with n rows and L−n columns. Construct both directions and prove the inverse identities and energy preservation. This gives exact finite counting before passing to unrestricted partitions under E≤min(n,L−n).

*Lean 4 Proof Strategy:*
**Theorem (Displacement partition bijection):** Define a mapping from valid momentum configurations (displacements `d_i`) to integer partitions bounded by `n` rows and `L-n` columns. Prove it is a bijection by constructing the explicit inverse mapping. Show that `\sum d_i = E`, matching the partition weight. Use `Finset.sum` over the modes and verify energy preservation.

Use `Nat.Partition E`, whose parts are a multiset of positive naturals, or finitely supported multiplicities r with Σ m r_m=E. The installed module is `Mathlib.Combinatorics.Enumerative.Partition.Basic`; the source's suggested module path and `Nat.Partition.partitions` name should not be assumed to exist. The installed type has a finite instance, so a finite enumeration can use `Finset.univ` when needed.

Construct partition-state products as ordered lists/folds in the noncommutative endomorphism algebra. Once same-sign commutativity is proved, establish independence of the chosen ordering. This is more appropriate than requiring a false `CommMonoid` instance on all endomorphisms.

*Lean 4 Proof Strategy:*
**Definition (Partition-state products):** Given a partition represented by frequencies `r_m`, define the state `(\prod_m \rho_m^{r_m}) \Omega`. Formalize this using a list of parts `[m_1, m_2, \dots]` sorted descending, and fold the application of `\rho_m` over the vacuum ket.
**Theorem (Ordering independence):** Use the previously proved `[\rho_m, \rho_n] = 0` (for `m, n > 0`) to show by induction over list permutations that any ordering of the same multiset of parts yields the identical state vector.

For the Gram theorem, first prove a commutator-through-a-word lemma with all prefix energy bounds. Then prove the vacuum reduction recursively. Use the explicit R2 regime only after deriving that every required M1/M2 application is justified. The norm is `z_λ=∏ m^(r_m) r_m!`, nonzero over ℂ. Completeness follows from membership, linear independence, and the rectangle-counting bijection. A mere dimension count without the bijection is a substantial missing proof.

*Lean 4 Proof Strategy:*
**Lemma (Commutator-through-a-word and vacuum reduction):** Prove `[\rho_{-m}, \prod \rho_{m_i}]` recursively on the list `[m_i]`. Each pass leaves a term proportional to `m` times the remaining product if `m_i = m`. Use induction on the length of the list, applying the edge commutator identities.
**Theorem (Gram theorem and Completeness):** Use the word commutator lemma to calculate the inner product of two partition states `\langle \Omega | \prod \rho_{-m_i} \prod \rho_{n_j} | \Omega \rangle`. Show it equals `\delta_{\lambda, \mu} z_\lambda`. Conclude linear independence since the Gram matrix is diagonal with positive entries. Completeness then follows since the dimension of the subspace matches the cardinality of the bounded partitions (from the bijection theorem).

## Sugawara statement repair

Write H_sug^(M)=Σ_(m=1)^M ρ_mρ_−m, identifying M explicitly. The assertion that h−1 includes all nonzero density modes is false: nonzero modes can occur up to L−1. For its action on B(N,K), M≥K is a useful sufficient cutoff because lowering modes m>K annihilate the input.

*Lean 4 Proof Strategy:*
**Definition (Sugawara Hamiltonian):** Define `H_{sug}^{(M)} = \sum_{m=1}^M \rho_m \rho_{-m}`. Formulate it using `Finset.sum` over `1 \le m \le M` acting as an operator on the Hilbert space.

Chapter 12.2, as stated for every nonzero n under only `2K+|N|≤h`, is false. At h=1, K=N=0, its H_sug sum is empty, but ρ₁Ω≠0; thus `[H_sug,ρ₁]Ω=0` differs from ρ₁Ω. A saved finite CAR computation checks this case.

A safer proof order is:

1. Evaluate H_sug on each admissible partition state, obtaining its total energy eigenvalue with the needed word margins.
2. Use Haldane completeness to prove Êψ=H_sugψ on B(N,K).
3. Derive commutation as a corollary on a specified range of n for which both the input and shifted output lie in budgets where this equivalence has been proved.

*Lean 4 Proof Strategy:*
**Theorem (Sugawara equivalence on budget spans):**
1. **Lemma:** Prove `H_{sug}^{(M)} |\lambda\rangle = E_\lambda |\lambda\rangle` for any partition state `|\lambda\rangle` by using the word commutator and the vacuum reduction lemma, provided `M` is larger than any part in `\lambda`.
2. **Theorem:** By the completeness theorem, any state `\psi \in B(N,K)` is a linear combination of partition states. Thus `\hat{P} \psi = H_{sug}^{(M)} \psi` on this subspace.
3. **Corollary:** For the commutation relation `[H_{sug}^{(M)}, \rho_n] \psi = n \rho_n \psi`, prove it by noting that if `\psi \in B(N,K)`, then `\rho_n \psi \in B(N, K+n)`. Assuming the margins hold for both budgets, apply the eigenvalue equivalence to both `\psi` and `\rho_n \psi`.

For example, an upward shift n>0 needs an equivalence theorem also on B(N,K+n), a cutoff M≥K+n, and a sufficient enlarged margin such as `2(K+n)+|N|≤h`. This is a sufficient repaired corollary, not a claim of optimal margins. It avoids using an overstrong commutation lemma to establish the equivalence circularly.

Keep the ground-energy shift `N(N+1)/2`. Changing to N²/2 requires a stated chemical-potential subtraction of N/2, which chapter 17 presently omits.
