# Appendix A09 proposal: duality, spin/charge constraints, and Umklapp

## Duality requires an actual map and mapped domains

**Proposed Definition (Duality data; operator map pending):** The scalar record involution sends `(u,c,s,g,gInv)` to `(u,c,−s,gInv,g)`. Construct the actual generator/star map and its inverse between specified carriers before naming an algebra equivalence. With the proposed charge map f(NR,NL)=(NR,−NL), CDW shift (+1,−1) maps to (+1,+1), whereas SC shifts (−1,−1). The former direct CDW→SC claim is withdrawn; a candidate SC adjoint needs its exact sign/phase and Klein ordering computed.

*Lean 4 Proof Strategy:*
To formalize the duality map, define an equivalence between two model instances `Model P` and `Model P*`. Auxiliary lemmas prove that the proposed algebraic map preserves the canonical commutation relations (CCR) and the involution (adjoints), while mapping charge sectors and excitation energy cutoffs explicitly.

Swapping the symmetric and antisymmetric combinations amounts to changing the sign of the left field. At the fermion level this corresponds to a left-mover particle-hole transformation, changing the Dirac sea and the charge region. The intended duality must therefore be constructed between two explicitly related models $\mathcal{M}(P)$ and $\mathcal{M}(P^*)$ and their mapped budgets, rather than a fixed-budget symmetry of a single instance.

**Theorem (Order-parameter transformation):** Prove order-parameter transformation including phases, adjoints, and zero modes. The proportional vertex formulas in chapter 20 are insufficient to freeze the exact isomorphism. Interpretation as topological T-duality also needs a compactification/charge-lattice specification; an algebraic variable exchange alone does not provide that interpretation.

*Lean 4 Proof Strategy:*
Formalize the transformation of the order-parameter vertex operators by applying the duality `AlgEquiv`. We need to define the vertex operators algebraically (e.g., as normal-ordered exponentials) and prove transformation rules for the zero-mode operators and the Klein factors.
**Auxiliary lemmas:** Prove that the conjugation of a vertex operator by the duality map yields the dual vertex operator up to an explicitly computed phase.
**Missing information:** The exact compactification radius and charge lattice structure must be specified algebraically (e.g., as a free abelian group with a specific intersection form) to correctly define the topological T-duality context.

## Spin/charge normalization and sectors

Square roots can again be isolated.

**Definition (Raw charge and spin currents):** Define raw charge and spin currents

\[
 R_m^c=\rho_{m,\uparrow}+\rho_{m,\downarrow},\quad
 R_m^s=\rho_{m,\uparrow}-\rho_{m,\downarrow}.
\]

*Lean 4 Proof Strategy:*
Define `R_c m` and `R_s m` simply as sums and differences of the single-species density operators `rho m ↑` and `rho m ↓` in the algebra. This avoids introducing `√2` factors.
**Auxiliary lemmas:** Expand the raw-current commutators preserving order. On the common action regime, `[R_-m^c,R_m^c]=[R_-m^s,R_m^s]=2mI`, while mixed charge/spin commutators are the difference of the same-species edge terms. Reverse mode order changes the sign.

On a regime where the two species edge terms each evaluate to m, each raw self-CCR coefficient is 2m and the mixed coefficient is zero. Normalize by one fixed real scalar b with 2b²=1 only if canonical m normalization is required. The raw version avoids √2 in most polynomial algebra, at the cost of explicit factors two.

**Lemma (Global mixed spin/charge commutativity):** Cross-species commutativity alone does not give global mixed spin/charge commutativity: the remaining expression is the difference of the two same-species edge commutators. These need not coincide on arbitrary finite-Fock states. Require the common frozen-margin regime, or retain the edge operator difference.

*Lean 4 Proof Strategy:*
Formalize the commutator `[R_m^c, R_n^s]`. Since it simplifies to `[rho_{m,up}, rho_{n,up}] - [rho_{m,down}, rho_{n,down}]`, define a `frozen_margin_regime` as a subspace where both species' edge terms evaluate to the same scalar `c`.
**Auxiliary lemma:** Prove that restricted to the `frozen_margin_regime`, the difference of the commutators vanishes, establishing `[R_m^c, R_n^s] = 0` on this subspace.

**Definition (Zero-mode charges):** For zero-mode charges set Q_c=N_up+N_down and Q_s=N_up−N_down.

*Lean 4 Proof Strategy:*
Define the zero mode charges `Q_c` and `Q_s` as linear combinations of the species number operators `N_up` and `N_down`.

**Lemma (Parity-constrained sublattice):** Their image satisfies `Q_c≡Q_s mod 2`, and the inverse has division by two. Consequently the allowed charge lattice is a parity-constrained sublattice, not a product of unrestricted independent integer charge labels. A budget with total energy ≤K is likewise a direct sum of tensor factors with K_c+K_s≤K, not the tensor product of two independent ≤K slices.

*Lean 4 Proof Strategy:*
Define the charge lattice `Λ_{c,s}` as the set of pairs `(Q_c, Q_s) : ℤ × ℤ` such that `Q_c ≡ Q_s [ZMOD 2]`.
**Auxiliary lemma:** Construct the integer charge-lattice equivalence with its parity-proved inverse `(Qc+Qs)/2, (Qc−Qs)/2`. Define energy budgets by coordinate support/span of configurations with total energy ≤K, and prove the sum over compatible energy splits; there is no ordinary vector inequality `Hψ≤Kψ`.

> [!WARNING]
> **Proof-review correction (2026-10-09):** The retired predicate `{ψ | H ψ ≤ K ψ}` is not a defined energy subspace on an ordinary complex vector space. Use the span/support of configurations of excitation energy at most K, or introduce a separately justified spectral projection. The charge-lattice equivalence also needs its parity-proved integer inverse, and the total-energy decomposition must sum over compatible energy splits.

**Lemma (Charge/spin block decomposition):** Spin exchange symmetry of the quadratic coupling matrix yields a charge/spin block decomposition. It does not imply unequal velocities for every parameter choice: the free spin-independent model is a counterexample. State the nondegeneracy condition needed for `u_c≠u_s` separately.

*Lean 4 Proof Strategy:*
Formalize the quadratic coupling matrix and its block-diagonalization via an orthogonal transformation.
*(Historical note: an earlier draft assigned a single Klein factor to both singlet terms; Chapter 21 now uses two distinct Klein products $K_1 = F_{R\uparrow} F_{L\downarrow} Z_{R\uparrow} Z_{L\downarrow}$ and $K_2 = F_{R\downarrow} F_{L\uparrow} Z_{R\downarrow} Z_{L\uparrow}$, because the two terms shift distinct species-charge vectors).* Both terms share the collective charge phase fields, while carrying distinct Klein factors and opposite relative spin-phase signs.

## Exact Umklapp charges and leakage

**Definition (Exact Umklapp operator):** For the explicitly written operator

\[
 O_U=c^\dagger_{L\uparrow}c^\dagger_{L\downarrow}c_{R\downarrow}c_{R\uparrow},
\]

each elementary creator adds one to its species charge and each annihilator subtracts one.

*Lean 4 Proof Strategy:*
Formalize `O_U` as an element of the CAR (Canonical Anticommutation Relation) algebra built from the creation and annihilation operators.

**Theorem (Exact Umklapp charge shift):** Therefore the exact shift is

\[
 \Delta\vec N=e_{L\uparrow}+e_{L\downarrow}-e_{R\downarrow}-e_{R\uparrow}.
\]

The current Chapter 21 now has the corrected species shift ±1; the branch total is ±2. Prove `[N_ν,O_U]=(ΔN)_ν O_U` directly from the CAR number commutator. The former species factor-two issue is historical.

*Lean 4 Proof Strategy:*
Use the fundamental properties `[N, c^\dagger] = c^\dagger` and `[N, c] = -c` in the CAR algebra to compute `[N_\nu, O_U]`.
**Auxiliary lemma:** Prove and apply the Leibniz derivation rule for commutators iteratively on the product of 4 operators (`[A, BC] = [A, B]C + B[A, C]`) to rigorously deduce `[N_\nu, O_U] = (\Delta N)_\nu O_U`.

**Lemma (Leakage condition):** A leakage statement needs an actual nonzero-action witness outside a specified budget, with g₃≠0, suitable occupations, and no cancellation in the spatial sum. An arbitrary boundary ket can be killed by Pauli exclusion, and the whole term vanishes when g₃=0. Sector nonconservation is distinct from noninvariance of every selected budget; a budget equal to the full carrier is invariant.

*Lean 4 Proof Strategy:*
Formalize "leakage" as the condition that the Hamiltonian `H` does not preserve a subspace `V` (i.e., `∃ ψ ∈ V, H ψ ∉ V`).
Construct an explicit witness Fock state `ψ` (e.g., a specific configuration of filled momentum states near the cutoff) where `O_U ψ` has non-zero norm and lies strictly outside `V`.
**Auxiliary lemma:** Prove that for the given witness state, the matrix element of `O_U` does not completely vanish when integrated over the spatial sum.

One can formalize nonzero charge-shift witnesses and failure of a fixed-sector quadratic-density description algebraically. A Mott gap requires a spectral statement, parameter regime, and usually scaling/thermodynamic analysis. Leakage from a cutoff is not a proof of a physical gap. Keep that interpretation outside the exact finite theorem until the additional analysis is supplied.

*Leakage revision:* Use a nonzero outward charge projection or an explicit outside occupation coefficient. Nonzero total `HU ψ` may be entirely inward. Chapter 21 gives a proper-box counterexample and Proposed Lemma 21.8 gives a useful zero-charge witness family with selected coefficient `σ*gU/L²`. Prove its CAR sign and spatial sum directly, without importing unnecessary current margins.
