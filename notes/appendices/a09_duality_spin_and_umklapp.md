# Appendix A09 proposal: duality, spin/charge constraints, and Umklapp

## Duality requires an actual map and mapped domains

An exchange φ↔θ is not by itself an `AlgEquiv` of a finite budget endomorphism algebra. Define its action on fundamental generators, prove every relation including adjointness, construct an inverse, and show how it maps charge sectors, the vacuum, and energy/charge cutoffs. Parameterize the Hamiltonian by a complete set of parameters: g alone does not determine u or the zero-mode energy.

Swapping the symmetric and antisymmetric combinations amounts to changing the sign of the left field. At the fermion level a candidate may involve a left particle-hole transformation. Such a transformation can change the sea and the charge/budget region; it is not automatically an automorphism of the original restricted carrier. A reasonable proposal is an equivalence between two explicitly related models and their mapped budgets, rather than a fixed-budget symmetry asserted before its construction.

Prove order-parameter transformation including phases, adjoints, and zero modes. The proportional vertex formulas in chapter 20 are insufficient to freeze the exact isomorphism. Interpretation as topological T-duality also needs a compactification/charge-lattice specification; an algebraic variable exchange alone does not provide that interpretation.

## Spin/charge normalization and sectors

Square roots can again be isolated. Define raw charge and spin currents

\[
 R_m^c=\rho_{m,\uparrow}+\rho_{m,\downarrow},\quad
 R_m^s=\rho_{m,\uparrow}-\rho_{m,\downarrow}.
\]

On a regime where the two species edge terms each evaluate to m, each raw self-CCR coefficient is 2m and the mixed coefficient is zero. Normalize by one fixed real scalar b with 2b²=1 only if canonical m normalization is required. The raw version avoids √2 in most polynomial algebra, at the cost of explicit factors two.

Cross-species commutativity alone does not give global mixed spin/charge commutativity: the remaining expression is the difference of the two same-species edge commutators. These need not coincide on arbitrary finite-Fock states. Require the common frozen-margin regime, or retain the edge operator difference.

For zero-mode charges set Q_c=N_up+N_down and Q_s=N_up−N_down. Their image satisfies `Q_c≡Q_s mod 2`, and the inverse has division by two. Consequently the allowed charge lattice is a parity-constrained sublattice, not a product of unrestricted independent integer charge labels. A budget with total energy ≤K is likewise a direct sum of tensor factors with K_c+K_s≤K, not the tensor product of two independent ≤K slices.

Spin exchange symmetry of the quadratic coupling matrix yields a charge/spin block decomposition. It does not imply unequal velocities for every parameter choice: the free spin-independent model is a counterexample. State the nondegeneracy condition needed for `u_c≠u_s` separately.

The pair expression in chapter 21.10 also needs coefficient checking: reconstructing each original spin species from normalized charge/spin fields introduces 1/√2 in the exponent, and the two singlet terms can carry different Klein/zero-mode products. Define the claimed `Ψ_spin` rather than leaving it an unspecified residual expression.

## Exact Umklapp charges and leakage

For the explicitly written operator

\[
 O_U=c^\dagger_{L\uparrow}c^\dagger_{L\downarrow}c_{R\downarrow}c_{R\uparrow},
\]

each elementary creator adds one to its species charge and each annihilator subtracts one. Therefore the exact shift is

\[
 \Delta\vec N=e_{L\uparrow}+e_{L\downarrow}-e_{R\downarrow}-e_{R\uparrow}.
\]

Chapter 21.13 has an erroneous factor two on each species. The total branch shifts are ΔN_L=+2 and ΔN_R=−2; that does not mean each spin species shifts by two. Prove `[N_ν,O_U]=(ΔN)_ν O_U` directly from the CAR number commutator.

A leakage statement needs an actual nonzero-action witness outside a specified budget, with g₃≠0, suitable occupations, and no cancellation in the spatial sum. An arbitrary boundary ket can be killed by Pauli exclusion, and the whole term vanishes when g₃=0. Sector nonconservation is distinct from noninvariance of every selected budget; a budget equal to the full carrier is invariant.

One can formalize nonzero charge-shift witnesses and failure of a fixed-sector quadratic-density description algebraically. A Mott gap requires a spectral statement, parameter regime, and usually scaling/thermodynamic analysis. Leakage from a cutoff is not a proof of a physical gap. Keep that interpretation outside the exact finite theorem until the additional analysis is supplied.
