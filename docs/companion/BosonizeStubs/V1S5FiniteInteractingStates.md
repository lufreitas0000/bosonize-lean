# V1-S5 finite interacting states — staging companion

Status: Phase A draft; not independently approved, locked, proved or promoted.
Baseline: `5865ca33d6c1c8731bf7b8bb743e632b650240fa` (accepted S4).
Sources: `V1S5FiniteGroundState.lean`, `V1S5MomentObstruction.lean`, and
`V1S5SmallInteractingModel.lean` in `BosonizeStubs/`.

## Carrier and physical conventions

The carrier is the subtype of A05's actual fixed-charge **total** excitation
budget, inherited from the finite occupation Hilbert space. It is not a product
of per-mode cutoffs. Admissible charges and `h>0` give the nonzero free sea.
The subtype inclusion preserves the inherited norm. Its adjoint is the
orthogonal restriction and its ambient product is the coordinate projection.

The chosen ambient Hamiltonian is exactly
`Ch17.luttingerBosonizedHamiltonian h M vF g4 g2 mu branches`. With
`L=2h`, `v1=vF+g4/(2π)`, `v2=g2/(2π)`, its oscillator part is

\[
 \frac{2\pi}{L}\sum_{m=1}^M
 [v_1(C_{Rm}A_{Rm}+C_{Lm}A_{Lm})
   +v_2(C_{Rm}C_{Lm}+A_{Rm}A_{Lm})].
\]

Here `C=rho(+m)`, `A=rho(-m)`. The full zero-mode charge observable
operator is retained, with sector value

\[
 \frac{2\pi v_F}{L}\frac{N_R(N_R+1)+N_L(N_L+1)}2
 +\frac{g_4}{2L}(N_R^2+N_L^2)+\frac{g_2}{L}N_RN_L
 -\mu(N_R+N_L).
\]

No Bogoliubov vacuum constant is added. This is the accepted pairing model,
identified unconditionally with `luttingerChosenModel` by Chapter 17.
Identification with `luttingerFermionChosenModel` requires its separate
Sugawara-margin theorem; it is not a global equality to raw four-fermion data.
The finite effective operator is `i† H_F i`; budget invariance is unnecessary.

## Parameterized state construction

`GroundVector H` contains a real energy, ket of norm one, actual eigenvalue
equation and the inequality `energy * norm(v)^2 ≤ re(inner v (H v))` for every
vector. A finite-dimensional symmetric operator on a nonzero carrier has such
a vector. The intended proof uses the minimum of the quadratic form on the
compact unit sphere and Mathlib's Rayleigh/eigenvector theorem. Degeneracy
permits an arbitrary selected pure ground vector; no uniqueness is claimed.

The complex linear functional is `X ↦ inner ket (X ket)`. Its value on
`X†X` is the real nonnegative squared norm `norm(X ket)^2`; its identity
value is one and its energy value is the ground energy. Compression extends
it to the ambient algebra by the vector `i ket`. This proves positivity and
normalization without asserting that compression preserves products. The
ground minimum remains a statement about the compressed operator only.

## Raw moment obstruction and proof route

For `q*m>K`, inductively apply `A05.rho_budget_map` to actual lowering
currents. If `m>K`, the first lowering already vanishes by
`rho_lowering_budget_zero`. Otherwise it maps into cutoff `K-m`; induction
on `q` terminates in a negative budget, which is zero by the actual
nonnegative excitation grading. This establishes annihilation on the entire
budget, and hence zero expectation of the ambient word `C^q A^q` with final
compression. Lowering preserves the budget, so a separate proof gives the
same zero result for powers of already compressed operators.

For the oscillator functional, A08's inverse substitution sends
`A_R` to `c A_R-s C_L`. On the polynomial vacuum its qth power is
`(-s)^q X_L^q`. The accepted word-adjoint pairing and diagonal monomial norm
give `q! (m s²)^q`. This reuses the actual A08 representation and does not
postulate Gaussianity. It is nonzero for `s≠0`, since all mode weights are
positive. The draft includes an actual zero-charge, `h=8,K=2,m=1,q=3`
sea witness with the accepted nonzero squeeze.

This concerns the **raw** dictionary, not S4's inverse-transformed observables
in the free sea. No vanishing for reverse ambient words `A^q C^q` is inferred:
such a word can leave the budget and return.

## Complete small model target

The eight explicitly normalized actual partition vectors are ordered
`vac,R1,L1,R11,L11,R1L1,R2,L2`; the double/single-mode-2 states carry
`1/sqrt(2)`, all others coefficient one. The carrier remains the whole
`B((0,0),2)` at `h=8`. Completeness must follow the existing partition basis,
not an enumeration of the ambient occupation matrix.

Take `M=2,vF=1,g4=32π,g2=30π,mu=canonicalMu(8,1)`. Existing Chapter 18
parameters give `v1=17,v2=15,u=8,c=5/4,s=3/4`. The zero-mode term is zero.
Writing `α=π/8`, the matrix target has entries `15α` at `(0,5),(5,0)`,
diagonal `0,17α,17α,34α,34α,34α,34α,34α`, and zero elsewhere.
The m=2 pair-creation channels leave this budget and are removed by final
compression; dropping them before proving that projection would be invalid.

The `small_spectral_basis` contract requires a complete orthonormal eigenbasis
whose indexed eigenvalues encode both multiplicities. The 2×2 eigenvalues are `α(17±sqrt(514))`, and the other six are
`17α` twice and `34α` four times. With
`eta=15/(17+sqrt(514))`, the target ket is
`(vac-eta*pair)/sqrt(1+eta²)`. The required inequality ranges over every
vector in the full eight-dimensional budget, not just this block.

Selected ambient products, with final compression, are
`rho_R(+1)*rho_R(-1)` and `rho_R(+1)*rho_L(+1)`. Their targets are
`(1-17/sqrt(514))/2` and `-15/(2sqrt(514))`, respectively.
A08 gives `9/16` and `-15/16` at the same parameters. The draft requires
exact inequalities. These remain theorem contracts, not accepted calculations.

## Reviews and evidence

Initial native reviewer: `/root/s5_review`, read-only, no source authorship.
It found the mathematical candidate consistent and verified the subtype
inference repair in scratch. This initial diagnosis is not interface approval.
Exact reviewed hashes, resolutions, scoped locks, proofs and later phase
receipts must be added before acceptance. Existing Core remains immutable.

No S6, physical-field equality, finite particle-hole symmetry, A10, finiteQMB,
analytic limit, global finite CCR, ambient ground minimum or release is part
of these contracts.
