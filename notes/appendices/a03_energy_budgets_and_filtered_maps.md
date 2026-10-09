# Appendix A03 proposal: integer energies and filtered operator domains

## Arithmetic and basis subsets

Take a positive natural h and set L = 2h for half-filled chapters. The asymmetric band is `[-h+1,h]`; do not call it a reflection-symmetric set of integer representatives. It has exactly h occupied modes k ≤ 0.

Define relative charge in ℤ, not by natural subtraction: `N(S) = (#S : ℤ) − h`. Define P(S) in ℤ. Define the ground-energy integer t(N) by the unique integer satisfying `2 t(N) = N(N+1)`, proving that the product is even. Then `e(S)=P(S)−t(N(S))` is an integer. Prove e(S) ≥ 0 before converting it to a natural number. No rational or real division is needed in the combinatorial layer.

For sorted occupied modes s_i indexed by `Fin (#S)`, the ground reference is `g_i=−h+1+i` with zero-based i. Prove reindexing of sums, strict monotonicity, s_i ≥ g_i, and `e(S)=Σ_i(s_i−g_i)`. The empty configuration must be covered. Derive nonnegative, nondecreasing displacements d_i; this extra monotonicity is needed for efficient frozen-margin proofs, beyond the loose bound d_i ≤ K.

Distinguish fixed-charge budgets B(N,K), fixed-energy spaces H(N,E), and the charge-box budget B(K,Nmax). All three are coordinate spans of explicitly specified subsets of the occupation basis. A coordinate projection deletes coefficients outside the subset. This is a concrete algebraic projection and, with the orthonormal occupation basis, also the orthogonal projection; no general analytic projection construction is needed.

Prove the sector ground ket belongs to B(N,K) and is nonzero for every admissible N. At K=0 the fixed-charge budget has dimension one. Do not require every anti-vacuity example to have dimension greater than one; use K≥1 when proving an excited witness.

## Ambient action and budget maps

An operator A of energy shift d is an ambient linear map with a grading theorem. For d≥0 it maps B(N,K) into B(N,K+d), not generally into B(N,K). For negative shifts, formulate output budgets using integer cutoffs, declaring negative-energy spaces zero, or split the case K<|d| and prove annihilation before taking natural subtraction.

If compression is desired, define A_K = P_K A inclusion explicitly. Ambient and compressed powers are different operations. The notation `A^j ψ` must identify which is used.

For polynomial creation of weight m, `C_m : F≤K → F≤(K+m)` is the natural typed map. Only `P_K C_m` is an endomorphism of F≤K. Its CCR has a boundary correction; a scalar CCR on all of the finite slice contradicts the trace theorem already proved in chapter 2.

## Composition theorem and margin accounting

If A=B only on a subspace V, the equality cannot automatically be substituted in A Cψ unless Cψ lies in V. Introduce a reusable lemma:

- C sends V into W;
- A and B agree on W;
- therefore AC and BC agree on V.

For an operator word with shifts d₁,…,d_r in the actual right-to-left application order, define the maximum cumulative upward excursion. A conservative bound is the sum of positive shifts. Use K plus this excursion in every M1/M2 check needed during a rewrite. An input-only margin is not a margin for the entire calculation.

Projection must also be tracked. In general `P A P B P ≠ P A B P`; discarded intermediate states can return into the retained slice. This is exactly why projected creators acquire edge terms. Similarly, a restricted equality `(A−B)P=0` implies `P(A†−B†)=0`, not `(A†−B†)P=0`. Adjoint identities require their own source/target argument.

## Uniform mode cutoffs

Introduce an independent mode cutoff M. The natural conservative uniform condition for all pairwise density commutators of modes |m|,|n|≤M on the input budget is

\[
 2M+K+N_{max}\le h.
\]

The chapter formulas summing m=1,…,h−1 do not satisfy this uniformly when h is large. Repeated products require replacing K by the intermediate-energy bound as well. Algebraic vanishing of a lowering mode m>K does not imply that a raising mode m>K vanishes; it maps out of the budget and is often nonzero.

The constants in sharper R1/R2 proofs should be derived from the actual word being commuted, rather than adding a guessed strengthening everywhere. Record these dependencies before freezing a theorem.
