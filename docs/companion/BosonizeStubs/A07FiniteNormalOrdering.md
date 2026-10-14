# A07FiniteNormalOrdering: verified Phase B support, Phase C pending

The six theorem contracts and seventeen data declarations have completed proof
bodies and fresh Phase B compiler/axiom evidence. A07 acceptance used the existing
runner at support finish `46cab18`; CH16 acceptance and Phase C are tracked
separately. This document is prepared for migration, not evidence of final Phase C
acceptance. The final source hash, promotion guards and independent pedagogical
review will be recorded by the orchestrator.

Source after promotion:
[A07FiniteNormalOrdering.lean](../../../../Bosonize/Core/A07FiniteNormalOrdering.lean).
Pedagogical mapping: supporting portion of
[Appendix A06](../../../../notes/appendices/a06_chiral_fields_and_lattice_kernels.md#constructive-realization-of-normal-ordering-and-field-energy-in-lean),
with downstream [Chapter 16](../../../../notes/md/ch16_field_Hamiltonian.md).
It does not implement `notes/appendices/a07_interactions_and_bogoliubov.md`.

## Exact declaration and argument mapping

| Proved contract | Mathematical content and dependencies |
| --- | --- |
| `normal_evaluation_add` | Additivity of finite coefficient-weighted evaluation. |
| `normal_evaluation_smul` | Complex scalar compatibility of the same evaluation. |
| `normal_pair_contraction` | Case split on creator flags; normal minus raw equals the reversed-current commutator precisely when a swap occurs. |
| `contraction_on_joint_budget` | Same-branch contraction `-m` on matching modes, zero otherwise; A06 joint signed CCR on the original input, with both positive mode bounds supplying the margin. |
| `chiral_gradient_representation` | Finite label enumeration, explicit `Fin M` to `Icc 1 M` bijection, and A06's exact forward-difference expansion for each orientation. |
| `dual_square_chiral_decomposition` | Scalar coefficient identity for the two dual-field squares; ordered cross coefficients cancel separately. |

The seventeen data declarations are `Letter`, `QuadraticSymbol`, `orientation`,
`natMode`, `phaseSign`, `signedMode`, `current`, `rawPair`, `normalPair`,
`rawEvaluation`, `normalEvaluation`, `squareSymbol`, `gradientCoefficient`,
`chiralCoefficient`, `phiCoefficient`, `thetaCoefficient`, and `dualSquareSymbol`.
The carrier is a complex coefficient function on finite ordered signed-current
pairs; evaluation gives ambient endomorphisms of the existing multispecies
occupation Fock space. No new current representation, Hilbert carrier, or axiom
is introduced.

The support compiler and all six theorem axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`; the fresh verifier audits data as well.
Frozen definitions and headers are unchanged. The contraction preserves the
coefficient `-m` and its actual joint-budget hypothesis. Gradient representation
retains the exact difference multiplier, rather than a spectral derivative.
The Fin bijection includes the empty-cutoff case without fabricating a zero mode.

CH16 supplies spatial collapse, factor-four field energy, ground annihilation,
single-excitation eigenvectors, and a genuine unequal-weight error witness.
These are downstream contracts, not additional A07 declarations. Neither module
claims analytic asymptotics, a multiword kernel classification, or general weight
positivity.

## Historical Phase A and development checkpoint

The record below is preserved verbatim. Its unproved/dependency-blocked status
sentences describe earlier snapshots and are superseded by the verified Phase B
support status above. Its proposal language must not be read as current compiler
evidence. Final Phase C acceptance remains pending.

# BosonizeStubs/A07FiniteNormalOrdering.lean

**Finite carrier audit.** The `A07.Letter` label has `(branch, m, creator)` and `m ∈ {1,…,M}` by construction. `signedMode` yields `+m` for a creator, `-m` for an annihilator. `gradientCoefficient` is obtained by *expanding the existing A06 forward difference*, not by introducing a spectral derivative. The value of the square is the linear evaluation of the coefficient function on **ordered pairs**, so contractions are not hidden in an inconsistent post-evaluation rewrite. Verify `normal_pair_contraction` by cases on the two creator flags. For the same species, compare the paired mode indices and apply `A06.joint_signed_current_commutator` on the actual input subspace. Across species, use `A05.rho_cross_commute`.

**Cancellation and Fourier calculation.** At fixed `x`, write `a=Δφ_right`, `b=Δφ_left` at the symbol level. Expand `(a+b)^2+(a-b)^2=2(a²+b²)` as an ordered-word identity: the `ab` and `ba` coefficients cancel separately. For each chirality, the four sign combinations of momentum indices leave two opposite-sign pairings after summing the character over `ZMod (2*h)`. The others have frequency `±(m+n)` and vanish since `1≤m,n≤M`, `0<m+n≤2M<2h`. Opposite-sign terms enforce `m=n` and produce *two* identical `rho_m rho_-m` terms after normal ordering. Each spatial sum contributes `(2*h)`; their combined coefficient is `2*(2*h) (ζ^m-1)(ζ^-m-1)/m²`. Multiplication by the dual-square decomposition gives `4*epsilon(m)` on each of the two branches. Do not treat a formal symbol cancellation as a global current CCR identity.

**Ground, reference modes, and witness.** Because `rho_-m groundKet=0` for `m>0`, the weighted error annihilates the ground ket. With `g0=epsilon(1)`, the one-mode excited ket at `m=1` is in the kernel. For a general `m`, move the only rightmost lowering mode through `rho_m groundKet` with the signed budget CCR. The nonzero scalar `m` times the nonzero ground ket also proves `rho_m groundKet≠0`; no independent cyclicity or occupation axiom is assumed. The conclusion for `m≥2` requires the **separate** hypothesis `epsilon(m)≠g0`. For a concrete gap test, `h=8`, `M=2`, `K=2`, `ζ=canonicalRoot 16`, zero charges and distinct species `0,1` give `2M+K=6≤8`, `2M=4<16`, and `epsilon(2)≠epsilon(1)`. Establish the last inequality algebraically or from the *proved* Core canonical-dispersion formula; it is a proposed theorem, not numerical verification.

**Proof dependency order.** A07 linearity/contraction → A07 chiral coefficient identity and symbol cancellation → CH16 local identity → chiral DFT collapse (character orthogonality and no alias) → weighted field on budgets → weighted error → ground/one-mode kernel → excited eigenvalue → explicit nonzero ket and concrete dispersion gap. For composite words, use `marginWithExcursion` with the budget of each right suffix, not a projection between factors.

Phase A integrated after user review. Theorems remain unproved.


Phase A finish evidence: `note/webllm/ch16/phaseA-ch16_cycle_a_be1da0fd.md`.


## Local Phase B development checkpoint

Phase A independently reviewed and accepted. Complete proof work is preserved
in [the quota checkpoint](../../../../note/ch16_quota_checkpoint_2026-10-13.md)
and its candidate archive. Accepted staging statements remain unproved; the
local candidate results and dependency-blocked bodies are distinguished there.
Phase B runner acceptance and Phase C remain incomplete.


Phase B finish evidence: `note/webllm/ch16/phaseB-ch16_cycle_b_f9a97a9d.md`.


## Accepted Phase B and reviewed promotion plan

A07 support acceptance `46cab18` and CH16 acceptance `3af7420` passed the
existing runner's fresh checks and CI, then merged and pushed. A fresh combined
verifier audits all 48 declarations with only standard axioms. Root independently
reviewed the six A07 proof bodies; `/root/same_ccr` independently reviewed all
thirteen CH16 bodies (its earlier authorship was A07 only).

Independent reviewer `/root/characters` approved the exact import/path migration:
both import Bosonize lines expand to the 25 current Core imports, and CH16's
staging A07 import becomes Bosonize.Core.A07FiniteNormalOrdering. No other
source bytes, definitions, theorem headers or proof bodies change. Only the two
interface records migrate, with import/context hashes updated; all 25 prior Core
complete-source hashes and unrelated interface records stay unchanged.

Predicted promoted source SHA-256, checked after actual promotion: `1056266f85e56868e20ef4769b8a58cfe88533845bd97db91440d6161d500996`.
The initial companion-link review found one old three-level checkpoint link;
it is corrected to the four-level promoted path. The unsupported numerical
history phrase was removed, and mathematical delimiters match the existing
Markdown conventions. Final independent pedagogy review and actual promoted
compilation/axiom/CI/runner evidence follow before declaring Phase C complete.


## Browser proof disposition and local verification

Adopted the preparation's finite-sum additivity, pair-contraction case split and
field/chiral rewrite. Adapted scalar compatibility to the actual scalar-action
normalization, and constructed the full positive Fin/Icc bijection and branch/sign
enumeration for the gradient. The dual-square proof follows the suggested scalar
coefficient argument, without a commutative operator algebra.

The spatial-collapse implementation proves coefficient orthogonality before
operator evaluation, rejects nonzero aliases by typed integer divisibility, and
retains both opposite flags at the same finite mode. Ground and eigenvector
proofs use actual budget membership and rightmost-suffix current identities.
The concrete gap uses exact denominator clearing and the polynomial consequence
(z−1)^4=0, rather than an unverified sine or floating-point argument.

Rejected every historical candidate/stub build as proof-completion evidence,
global CCR substitutions, intermediate budget projections, numerical dispersion
verification, and full multiword-kernel/analytic conclusions outside the frozen
contracts. The local proof clusters were freshly integrated and audited before
acceptance; no definitions or statements were weakened.


Independent final pedagogical reviewer `/root/characters` returned PASS for all
five documents after the link and historical-prose corrections. Both complete
reference prefixes are preserved, declaration mappings and predicted promoted
hashes are checked, the mathematics matches the proved contracts, and scope
limitations are explicit. No required findings remain. This review precedes the
runner's promoted compiler/axiom/CI acceptance and does not replace those gates.
