# V1-S5 finite interacting states — verified construction

Status: Phase C complete and accepted after independent review and local CI.
This companion supersedes the historical staging checkpoints. Exact acceptance
status and reproducibility receipts are in the [S5 validation record](../../../plans/v1-s5/phase-c-acceptance-2026-10-19.md).
The four modules share namespace `Bosonize.V1S5`; 43 named theorems and
65 explicit declarations are audited, including the `Budget` abbreviation. The accepted S4 baseline is `5865ca33`.

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
a vector. The proof uses the minimum of the quadratic form on the
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
positive. The proof includes an actual zero-charge, `h=8,K=2,m=1,q=3`
sea witness with the accepted nonzero squeeze.

This concerns the **raw** dictionary, not S4's inverse-transformed observables
in the free sea. No vanishing for reverse ambient words `A^q C^q` is inferred:
such a word can leave the budget and return.

## Complete small model

The eight explicitly normalized actual partition vectors are ordered
`vac,R1,L1,R11,L11,R1L1,R2,L2`; the double/single-mode-2 states carry
`1/sqrt(2)`, all others coefficient one. The carrier remains the whole
`B((0,0),2)` at `h=8`. Completeness follows the existing partition basis,
not an enumeration of the ambient occupation matrix.

Take `M=2,vF=1,g4=32π,g2=30π,mu=canonicalMu(8,1)`. Existing Chapter 18
parameters give `v1=17,v2=15,u=8,c=5/4,s=3/4`. The zero-mode term is zero.
Writing `α=π/8`, the derived matrix has entries `15α` at `(0,5),(5,0)`,
diagonal `0,17α,17α,34α,34α,34α,34α,34α`, and zero elsewhere.
The m=2 pair-creation channels leave this budget and are removed by final
compression; dropping them before proving that projection would be invalid.

The `small_spectral_basis` theorem provides a complete orthonormal eigenbasis
whose indexed eigenvalues encode both multiplicities. The 2×2 eigenvalues are `α(17±sqrt(514))`, and the other six are
`17α` twice and `34α` four times. With
`eta=15/(17+sqrt(514))`, the selected ket is
`(vac-eta*pair)/sqrt(1+eta²)`. The proved inequality ranges over every
vector in the full eight-dimensional budget, not just this block.

Selected ambient products, with final compression, are
`rho_R(+1)*rho_R(-1)` and `rho_R(+1)*rho_L(+1)`. Their exact values are
`(1-17/sqrt(514))/2` and `-15/(2sqrt(514))`, respectively.
A08 gives `9/16` and `-15/16` at the same parameters. Both inequalities are proved in `small_number_discrepancy` and
`small_pair_discrepancy`.

## Proof architecture and source mapping

The source-path migration preserves every mathematical definition, theorem
header and proof body. Its only source substitutions are the three imports
from staging dependencies to their promoted Core paths.

| Module | Constructive content and principal declarations |
| --- | --- |
| [FiniteVectorStates](../../../../Bosonize/Core/V1S5FiniteVectorStates.lean) | `GroundVector`, `ground_vector_exists`, `vector_state_one`, `vector_state_positive`, `ground_energy_evaluation`; generic inclusion/adjoint and compression pairings; `extended_state_vector`, `extended_state_one`, `extended_state_positive`; the orthonormal plane rotation and complete diagonalization helpers. |
| [FiniteGroundState](../../../../Bosonize/Core/V1S5FiniteGroundState.lean) | `Budget`, actual `ambientHamiltonian` and `budgetHamiltonian`; `budget_nontrivial`, `inclusion_isometric`, `inclusion_adjoint_inclusion`, `inclusion_projection`, `ambient_hamiltonian_self_adjoint`, `budget_hamiltonian_symmetric`, `physical_ground_exists`. |
| [MomentObstruction](../../../../Bosonize/Core/V1S5MomentObstruction.lean) | `repeated_lowering_zero`, `finite_normal_moment_zero`, separately `compressed_lowering_zero` and `compressed_normal_moment_zero`; `oscillator_normal_moment`, `raw_dictionary_obstruction`, `raw_obstruction_witness`, `ground_state_raw_obstruction`. |
| [SmallInteractingModel](../../../../Bosonize/Core/V1S5SmallInteractingModel.lean) | The actual partition labels, Gram normalization and complete basis; `current_word_lowering`, `small_current_lowering`; `small_matrix_action`, `small_spectral_basis`, `small_ground`; both selected ambient-product moments and both discrepancies. |

The small matrix is derived by transferring creators across the inner product
as actual adjoints, so only lowering on low-energy partition states is needed.
The partition Gram theorem supplies every coefficient, and completeness comes
from the accepted partition basis. This avoids ambient occupation enumeration
and does not assume an identity beyond its current margin. The generic plane
diagonalization takes the proved actual matrix action as a hypothesis; it does
not install a surrogate Hamiltonian. The global minimum follows by expanding
an arbitrary budget vector in all eight eigenvectors and comparing each real
eigenvalue with the lowest one.

The raw obstruction reuses A05's actual grade-lowering filtration and A08's
polynomial oscillator representation. Suggested broad interacting moment
matching is rejected on this fixed raw dictionary. S4's transformed-observable
comparison remains valid with its word-dependent margins; it is not a theorem
identifying the finite interacting state with the squeezed functional.

## Review, validation and preservation

Independent native reviewer: `/root/s5_review`, read-only diagnosis/review with
no proof authorship, as explicitly authorized in the S5 brief. Interface,
scoped amendments, full mathematical proofs, import/path migration and additive
pedagogy are independently reviewed. Early unsuccessful candidates, resource
obstructions and quota checkpoints remain historical evidence under
`docs/plans/v1-s5/`; they are not the status of these final proofs.

The historical Phase B script audits 64 non-abbreviation declarations. The
final Core-aggregator script additionally audits `Budget`, covering all 65
explicit declarations in the source inventory. Only `propext`,
`Classical.choice`, `Quot.sound` are permitted. Fresh zero-warning builds and
zero placeholders are required. The v2 lock migration changes precisely four
paths, three import-command records and their induced context hashes; all
unchanged declaration-header and command hashes are preserved. All 39 earlier
Core files and hashes are preserved byte-for-byte.

Pedagogical mapping is the additive S5 realization section of
[Chapter 20](../../../../notes/md/ch20_CDW.md). The complete prior chapter text,
including reference exposition, citations and S1–S4 sections, remains an exact
prefix. The independently reviewed draft explains the actual budget, minimum,
positive state, both compression placements, general obstruction and complete
small model in mathematical prose. The acceptance receipt records the final
source/companion/chapter hashes, review verdicts, guard results and local CI.

No S6, physical-field equality, finite particle-hole symmetry, A10 application,
finiteQMB migration, global finite CCR, ambient ground minimum, analytic limit,
continuum exponent, thermodynamic gap, push or release is claimed by S5.

## Final acceptance evidence

Phase B accepted at `4e79e55`; the reviewed four-source path/import migration
is committed at `7f90a30`. Local `make ci` passes: 69 guard tests, 18 artifact/
proof-verifier tests, both strict guards and both library builds (Core with
warnings treated as errors). All 65 direct Core-aggregator axiom audits pass;
all 43 named theorems have zero placeholders and warnings. Exact current
hashes, declaration inventory, CI/audit output and independent final verdict
are saved in the linked acceptance receipt. The complete Chapter 20 prefix
and its approved additive suffix are checked byte-for-byte. No S6 work began.
