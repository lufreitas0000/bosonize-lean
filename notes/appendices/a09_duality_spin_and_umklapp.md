# Appendix A09 proposal: duality, spin/charge constraints, and Umklapp

## Constructed algebraic duality and its scope

Use the charge/CCR tensor algebra and formal Weyl-type vertices specified in A08 and Chapter 20. The parameter involution is P*=(u,c,−s,gInv,g). The oscillator map sends bare R generators to their negatives and fixes L generators. On the charge module, the unitary permutation δ_N↦δ_(NR,−NL) induces conjugation; with the fixed R<L signs it gives D F_R=F_R and **D F_L=−F_L†**. It sends N_L↦−N_L and Z_L↦Z_L†. These are involutive relation-preserving star maps and define the tensor-algebra map, not just a substitution on scalar parameters.

The zero-mode products obey D K_CDW(x)=ζ^x K_SC(x)† and D K_SC(x)=ζ^x K_CDW(x)†. D maps dressed R(P) to −R(P*) and dressed L(P) to L(P*), giving D X_CDW(P)=−X_SC(P*) and the converse. Therefore the exact formal vertex laws are
$$
D W_{CDW}(P,t,x)=\zeta^x W_{SC}(P^*,t,x)^*,\qquad
D W_{SC}(P,t,x)=\zeta^x W_{CDW}(P^*,t,x)^*.
$$
Charge shifts (+1,−1) map to (+1,+1), explaining the required adjoint. The source character and shifted Klein order explain ζ^x; neither can be omitted as a proportionality factor.

*Lean 4 Proof Strategy:*
Define generator maps on the quotient and prove relation/star preservation and inverse. On finite-support charge kets compute the signed shift conjugations, then prove each Klein-phase product by basis extensionality. Extend to the generated charge algebra, tensor algebra and formal series. Prove `D β_P = β_P* D`, vacuum invariance, and the charge-indexed state law `ω_(P*,f(N)) ∘ D = ω_(P,N)`. Fixed-charge invariance is not asserted. The symmetric chemically adjusted quadratic Hamiltonian of Chapter 20 satisfies D H(P)=H(P*); the unsymmetrized linear charge term must not be discarded silently.

This is an uncompressed algebraic model equivalence. A finite CAR particle-hole map, mapped budgets, or finite spectral equivalence needs its own construction. A topological T-duality interpretation additionally needs a compactification and charge-lattice form; it is physical context outside this theorem.

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

**Lemma (Restricted mixed spin/charge commutativity and global edge formula):** Cross-species commutativity alone does not give global mixed spin/charge commutativity: the remaining expression is the difference of the two same-species edge commutators. These need not coincide on arbitrary finite-Fock states. Require the common frozen-margin regime, or retain the edge operator difference.

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

**Lemma (Charge/spin block decomposition):** Spin exchange symmetry of the quadratic coupling matrix yields a charge/spin block decomposition. It does not imply unequal velocities for every parameter choice: the free spin-independent model is a counterexample. State the nondegeneracy condition needed for `u_c≠u_s` separately.

*Lean 4 Proof Strategy:*
Formalize the quadratic coupling matrix and its block-diagonalization via an orthogonal transformation.
For each spin-index quadratic matrix `[[a,b],[b,a]]`, raw-current substitution gives coefficients `(a+b)/2` and `(a−b)/2`. Distinct velocities need distinct positive squared pairing velocities; symmetry alone is insufficient. Chapter 21 now gives two typed singlet channels with separate Klein products, intermediate budgets, and projection residuals. Collective phase rewriting does not justify combining their compressed exponentials.

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

**Lemma (Leakage condition):** A leakage statement needs an actual nonzero-action witness outside a specified budget, with g_U≠0, suitable occupations, and no cancellation in the spatial sum. An arbitrary boundary ket can be killed by Pauli exclusion, and the whole term vanishes when g_U=0. Sector nonconservation is distinct from noninvariance of every selected budget; a budget equal to the full carrier is invariant.

*Lean 4 Proof Strategy:*
Formalize "leakage" as the condition that the Hamiltonian `H` does not preserve a subspace `V` (i.e., `∃ ψ ∈ V, H ψ ∉ V`).
Construct an explicit witness Fock state `ψ` (e.g., a specific configuration of filled momentum states near the cutoff) where `O_U ψ` has non-zero norm and lies strictly outside `V`.
**Auxiliary lemma:** Prove that for the given witness state, the matrix element of `O_U` does not completely vanish when integrated over the spatial sum.

One can formalize nonzero charge-shift witnesses and failure of a fixed-sector quadratic-density description algebraically. A Mott gap requires a spectral statement, parameter regime, and usually scaling/thermodynamic analysis. Leakage from a cutoff is not a proof of a physical gap. Keep that interpretation outside the exact finite theorem until the additional analysis is supplied.

*Leakage revision:* Use a nonzero outward charge projection or an explicit outside occupation coefficient. Nonzero total `HU ψ` may be entirely inward. Chapter 21 gives a proper-box counterexample and Lemma 21.8 gives the zero-charge witness family with exact coefficient `−g_U/L²` for species order `(L↑,L↓,R↑,R↓)` and ascending momenta. Prove the preceding counts `2h,3h−1,2h,h`, odd total `8h−1`, and constant character directly, without importing current margins.
