# Ch16FieldHamiltonian: Phase B complete; Phase C preparation

The accepted Phase B batch proves all thirteen CH16 contracts. The fresh
combined verifier passed all 48 A07/CH16 declarations with no target warnings,
placeholders or recovery axioms, and only `propext`, `Classical.choice` and
`Quot.sound`. This batch was accepted at `3af7420`. Phase C promotion, source hash recording,
independent pedagogical review and final Core validation remain pending at
this notebook's preparation time. Those gates must be recorded
from actual results before a completion claim.

Future source: [Core CH16](../../../../Bosonize/Core/Ch16FieldHamiltonian.lean).
Pedagogical mapping: [Chapter 16 constructive realization](../../../../notes/md/ch16_field_Hamiltonian.md#constructive-realization-in-lean).
A07's finite normal-ordering symbols supply the field construction; this module
has the exact 12 data declarations and thirteen proof contracts listed below.
The source namespace remains `Bosonize.Ch16` during promotion.

## Declaration mapping and proof evidence

| Declaration | Chapter topic | Actual checked construction |
| --- | --- | --- |
| `field_chiral_identity` | 16.2 chiral separation | A07's ordered coefficient identity and linear normal evaluation give twice the sum of chiral squares. |
| `chiral_spatial_collapse_on_budget` | 16.2 spatial collapse | Integer-to-residue character bridge, orthogonality and no-alias divisibility retain both opposite-sign ordered pairs; finite positive-mode reindexing yields twice the weighted chiral density sum. |
| `field_weighted_on_budget` | 16.3 weighted energy | Apply the two branch collapses to the same input and combine their factor two with the dual-square factor two. |
| `field_weighted_after_excursion` | 16.3 right-suffix budget | Apply the weighted theorem at K+excursion with both translated species margins. |
| `error_weighted_on_budget` | 16.4 weighted error | Subtract the reference-weight Sugawara sum and distribute the finite coefficients. |
| `ground_error_zero` | 16.4 ground kernel | Actual admissible ground membership and annihilation by every rightmost lowering current kill the weighted error terms. |
| `excited_ket_mem_budget` | 16.4 actual excitation | A05's current budget map sends ground budget zero to momentum m; coordinate-space monotonicity gives budget K when m≤K. |
| `excited_ket_nonzero` | 16.4 non-vacuity | Restricted signed CCR on ground zero budget, ground lowering zero and m≠0 contradict a zero excited ket. |
| `single_mode_error_eigenvector` | 16.4 single-excitation eigenvalue | Ground-suffix CCR and cross-species commutation produce two delta selectors; isolate momentum m in each weighted finite sum. |
| `first_mode_error_zero` | 16.4 reference mode | Specialize the single-excitation eigenvalue to m=1 and g0=epsilon(1). |
| `error_nonzero_witness` | 16.4 nonzero error action | Combine the proved nonzero ket, nonzero weight difference and eigenvalue 4*m*(epsilon−reference). |
| `concrete_dispersion_gap` | 16.4 algebraic gap | Primitive root z of order 16 has z≠0,1; equality of epsilon2 and epsilon1 implies (z−1)^4=0 by exact field algebra. |
| `concrete_excited_error_witness` | 16.4 explicit witness | h8/M2/K2, zero charges and distinct Fin2 species satisfy admissibility, margins and the proved algebraic gap. |

Normal ordering is linear evaluation of ordered quadratic symbols, not a map
on arbitrary already-evaluated operators. Fin M labels represent m=i+1 and
therefore only positive momenta. No intermediate budget projection is inserted.
The contraction theorem is restricted to the appropriate joint input budget;
the eigenvector proof applies signed CCR to the right ground suffix, not globally.
The Fourier collapse is in fact derived as an ambient ordered-symbol identity;
the approved theorem retains its original budget and margin hypotheses.

The no-alias bound is 2M<2h. The two ordered cross pairings each contribute 2h,
producing 2*(2h); the dual-square decomposition supplies another factor two,
giving exactly 4*weightedEnergy. The reference weight is epsilon1. The proved
kernel result covers the ground and a single first-mode excitation. Arbitrary
products of reference-mode creators, the full kernel classification, the sine
formula, dispersion positivity, analytic/Taylor estimates and RG conclusions
remain outside the proved contract scope.

## Phase C evidence to complete

The candidate lecture preserves the entire current reference note as an exact
prefix and appends the constructive explanation; it does not replace historical
proof proposals. Its source and companion links use the planned Core locations.
The companion links here use the future `docs/companion/Bosonize/Core/` depth.
Independent review must verify preservation, hypotheses, signs, normalization,
status and the scope distinction for arbitrary reference-mode words.

Record actual accepted Phase B and promotion hashes, import migration and scoped
lock deltas, post-promotion compiler/axiom output, reviewer identity/verdict,
final CI and runner completion before replacing these pending status labels.
No proposed import or frozen-interface change is silently accepted by this prose.

## Historical Phase A and quota checkpoint record

The following notebook text is retained as historical evidence. Its unproved
and proposed-theorem labels describe the earlier accepted Phase A and quota
checkpoint, superseded by the freshly verified Phase B candidate status above.

# Bosonize/Core/Ch16FieldHamiltonian.lean

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

Predicted promoted source SHA-256, checked after actual promotion: `54e045da25fcc31e8e18bce5b81b1318adef6955e38ca357e3b7b6c21887e787`.
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


Phase C finish evidence: `note/webllm/ch16/phaseC-ch16_cycle_c_004f44cb.md`.
