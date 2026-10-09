# Appendix A04 proposal: truncated density modes, partitions, and Sugawara

## Density definition and finite edge identity

A shift is an integer, not a band element. Define the valid-pair set

\[
 D_m=\{(p,k)\in B\times B:p=k+m\},\qquad
 \rho_m=\sum_{(p,k)\in D_m}c_p^\dagger c_k.
\]

This formulation avoids constructing the subtype `k+m` from a predicate about membership inside a filtered sum. An equivalent dependent-if implementation is acceptable after proving its sum formula. Do not use wrapped band addition in D_m.

Introduce a one-particle partial shift matrix T_m, and the second-quantization map dΓ taking a matrix A to `Σ A_pk c_p†c_k`. Prove `dΓ([A,B])=[dΓ(A),dΓ(B)]` from the CAR bilinear identity. Then ρ_m=dΓ(T_m). This reduces many boundary calculations to finite matrices/intervals before lifting to Fock space.

The next lemma chain should establish:

1. T_m and ρ_m vanish for |m|≥L.
2. T_m†=T_−m and ρ_m†=ρ_−m by reindexing valid pairs.
3. Same-sign partial shifts commute; for nonnegative m,n, T_m T_n=T_(m+n). Hence positive density modes commute globally, not only on a budget.
4. Opposite shifts have a diagonal edge commutator; derive the bottom-minus-top occupation formula for 1≤m≤h.
5. General opposite-sign unequal shifts have explicitly supported edge hoppings; identify both source and target frozen regions.
6. Apply occupation/hop laws to frozen margins and lift from occupation kets to the budget span.

This avoids proving the general Schwinger theorem directly by a large double CAR sum. Every restricted scalar identity must remain a theorem about action on input vectors, not an endomorphism CCR of a finite budget carrier.

## Energy and linear independence

The bare Hamiltonian is H₀=Σ k n_k. Its vacuum eigenvalue is `−h(h−1)/2`, not zero unless h=1. Introduce the normal-ordered Hamiltonian P̂=H₀−EΩ I once. Density covariance holds for both; the eigenvalues of ρ_mΩ under the bare H₀ are EΩ+m. This corrects chapter 9's proof sketch without changing its intended linear-independence result.

First prove the explicit vacuum norm `||ρ_m Ω||²=m` for 1≤m≤h using orthogonal hop kets. Then distinct energy eigenvalues give linear independence. Using the Schwinger term to prove the first nonzero action would risk a circular dependency if the Schwinger proof itself uses nondegeneracy.

## Partitions and completeness

For n=h+N occupied modes, their nondecreasing displacements d_i=s_i−g_i encode a partition of total energy E fitting a rectangle with n rows and L−n columns. Construct both directions and prove the inverse identities and energy preservation. This gives exact finite counting before passing to unrestricted partitions under E≤min(n,L−n).

Use `Nat.Partition E`, whose parts are a multiset of positive naturals, or finitely supported multiplicities r with Σ m r_m=E. The installed module is `Mathlib.Combinatorics.Enumerative.Partition.Basic`; the source's suggested module path and `Nat.Partition.partitions` name should not be assumed to exist. The installed type has a finite instance, so a finite enumeration can use `Finset.univ` when needed.

Construct partition-state products as ordered lists/folds in the noncommutative endomorphism algebra. Once same-sign commutativity is proved, establish independence of the chosen ordering. This is more appropriate than requiring a false `CommMonoid` instance on all endomorphisms.

For the Gram theorem, first prove a commutator-through-a-word lemma with all prefix energy bounds. Then prove the vacuum reduction recursively. Use the explicit R2 regime only after deriving that every required M1/M2 application is justified. The norm is `z_λ=∏ m^(r_m) r_m!`, nonzero over ℂ. Completeness follows from membership, linear independence, and the rectangle-counting bijection. A mere dimension count without the bijection is a substantial missing proof.

## Sugawara statement repair

Write H_sug^(M)=Σ_(m=1)^M ρ_mρ_−m, identifying M explicitly. The assertion that h−1 includes all nonzero density modes is false: nonzero modes can occur up to L−1. For its action on B(N,K), M≥K is a useful sufficient cutoff because lowering modes m>K annihilate the input.

Chapter 12.2, as stated for every nonzero n under only `2K+|N|≤h`, is false. At h=1, K=N=0, its H_sug sum is empty, but ρ₁Ω≠0; thus `[H_sug,ρ₁]Ω=0` differs from ρ₁Ω. A saved finite CAR computation checks this case.

A safer proof order is:

1. Evaluate H_sug on each admissible partition state, obtaining its total energy eigenvalue with the needed word margins.
2. Use Haldane completeness to prove Êψ=H_sugψ on B(N,K).
3. Derive commutation as a corollary on a specified range of n for which both the input and shifted output lie in budgets where this equivalence has been proved.

For example, an upward shift n>0 needs an equivalence theorem also on B(N,K+n), a cutoff M≥K+n, and a sufficient enlarged margin such as `2(K+n)+|N|≤h`. This is a sufficient repaired corollary, not a claim of optimal margins. It avoids using an overstrong commutation lemma to establish the equivalence circularly.

Keep the ground-energy shift `N(N+1)/2`. Changing to N²/2 requires a stated chemical-potential subtraction of N/2, which chapter 17 presently omits.
