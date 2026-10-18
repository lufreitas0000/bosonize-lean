# V1-S3 formal duality and state transport — Phase B checkpoint

## Current Phase B checkpoint — 2026-10-18

**Subsequent authorization:** the user approved the reviewed four-header
coefficientwise-phase correction and continued development. The exact amended
source has SHA-256 `1574eb8b3e555cbbde324d0f68ac5f04b30cff363859bb2dfa514a3bda85e200`;
only the four reviewed statement records were amended in the scoped lock.
See [the amendment receipt](../../plans/v1-s3/interface-amendment-2026-10-18.md).
The earlier obstruction and pending-decision checkpoint below is historical;
the remaining seven proofs now proceed against the corrected interface.

**Phase B remains incomplete: 7 placeholders, with a confirmed false vertex
contract blocking acceptance.** The resumed batch completed 16 contracts:
representation/kernel/series transport, joint functionals and state-family
corollaries, Klein reflections, both field transformations and degree-zero
vertex transport. The canonical module compiles, and strict locks against
HEAD preserve 1215 statements, 1240 frozen commands and 37 Core sources.
All 87 declarations received a fresh axiom/dependency closure audit: 80 have
only standard axioms or none; seven contain `sorryAx`, matching the remaining
placeholders. Independent native proof review passed the new proof batches.
Existing lint/deprecation warnings remain; no Phase B/C acceptance is claimed.

At coefficient 1, the accepted Weyl D equality compares multiset cardinalities
1 and 2 because scalar Cauchy convolution retains zero-scaled entries.
An independent compiler-checked negation has only standard axioms. A concrete,
independently reviewed four-header correction uses coefficientwise phase
mapping; it has not changed the canonical statements or locks. A specific user
decision is pending under the sprint's interface/lock preservation instruction.

Exact source hashes, evidence, remaining contracts and the next decomposition
are in [the Phase B checkpoint](../../plans/v1-s3/phase-b-checkpoint-2026-10-18.md).
The earlier quota pause ended after recovery; the consumed wakeup is paused.
The Hamiltonian limitation below remains in force. S4 has not been started.

## Historical Phase A record

**Status at the historical Phase A snapshot: independently reviewed PASS; not yet locked or proved.** This is
the actual additive Lean interface drafted against promoted S2. It is not a
finite-CAR construction and does not establish physical interacting-state
duality. Do not promote or describe this sprint as complete from this file.

## Accepted dependencies and current source identities

- S2: `Bosonize/Core/V1S2FormalVertices.lean`, SHA-256
  `17cab3f91f38bc218b18cd7a2fe9e2ec8abf13d487096c3c2fca3fdd5c107020`.
- S2 companion: SHA-256
  `b3d92931358c386da96c75c5f450565f4012b0e9118fadc5e7930f341965a0c5`.
- A08 oscillator free algebra/state: `Bosonize/Core/A08OscillatorStates.lean`.
- CH13 finite-sea Klein convention and gauge adapter: `Bosonize/Core/Ch13KleinFactors.lean`.
- S1 ordered Wick dependency: `Bosonize/Core/V1S1OrderedWick.lean`.

The S2 coefficient syntax is `ChargeWord × OscSyntax`; the former acts on
finitely supported charge vectors by a bijection and source amplitude, the
latter is finite-word `MonoidAlgebra` syntax evaluated into A08's free
algebra. Its `vertexSeriesMul` has finite Cauchy sums of multiset coefficients.
The S2 joint carrier is `ChargeVec ⊗[ℂ] OscPoly`; its parameter-indexed
functional is represented by `jointCoeffFunctional` and
`jointSeriesFunctional`. There is no parameter-dependent quotient kernel in
this carrier, so S3 does not posit quotient descent. The map on syntax is
parameter-independent; parameter indexing enters through the source and target
representations at `P` and `P*`.

## Conventions and intended target

`P*=(c,-s)` is distinct from algebraic adjoint and scalar conjugation. The
oscillator map fixes L creators/annihilators and negates R creators/annihilators.
The charge permutation is `(N_R,N_L) ↦ (N_R,-N_L)`. Charge-word amplitudes are
evaluated at the reflected source. Klein words are the S2 `canonicalKleinD/S`
gauge-adapted versions; the bare `kleinD/S` formulas cannot be substituted in
their place. The proposed vertex phase is the constant series with coefficient
`canonicalRoot(2h)^x` at degree zero. Adjoints reverse charge shifts/source
evaluation and reverse oscillator words through S2's dagger.

The intended oscillator intertwining is
`Dosc ∘ bogoliubovMap(P,c,-s) = bogoliubovMap(P*,c,s) ∘ Dosc`,
with the S2/A08 substitutions checked on each of the four generators. The
expected field identities are `D(X_D(P,x))=-X_S(P*,x)` and
`D(X_S(P,x))=-X_D(P*,x)`. Consequently the coefficientwise exponential
interchanges with the adjoint while fixing `Complex.I` as a scalar under the
complex-linear map. Products remain in their original order.

## Phase A source and validation

Candidate source: `BosonizeStubs/V1S3FormalDuality.lean`.
Current SHA-256: `881107e4ea38703f7d36fd63d37709acd9fd33c842520c781b55116c55493f72`.

The actual linear map on the accepted joint vector carrier is
`jointReflectionLinear`: it reflects the charge basis and applies right-mode
polynomial parity. On a monomial multi-index `k`, the factor is
`(-1)^(rightOscillatorDegree k)`; the vacuum multi-index has factor one. The
coefficient-level map is `dualCoeff`, parameter-indexed as `D_P`; representation
transport is contracted by `represented_action_intertwining_contract`. The
oscillator algebra hom is `oscillatorDualityAlgHom`, and
`oscillatorDuality_syntax_compatibility_contract` states that its free-algebra
action is encoded by the S2 finite-word syntax map. This is a common coefficient
map represented at `P` and `P*`, not a quotient descent claim.

Direct elaboration and `lake build BosonizeStubs.V1S3FormalDuality` succeed.
Expected Phase A placeholder warnings remain. The data-only audit
`docs/plans/v1-s3/phase-a-audit.lean` compiles; all reported dependencies for
the data definitions are among `propext`, `Classical.choice`, and `Quot.sound`.
Its checks confirm the nonzero squeeze gains `1/4` and `4`, the zero-squeeze
parameter is fixed, a nonzero left charge is moved, and the `M=0` parity is
trivial. This audit does not prove any S3 theorem contract. The L=4 source-phase check `chargePhase 4 1 1 = Complex.I` passes, independently
exhibiting a nontrivial position phase. The candidate now states ordered
vertex/adjoint transport with the explicit `phase(x) * conj(phase(y))` ratio;
it makes no unphased same-orientation correlator claim. A direct canonical
degree-zero action contract is included, and the audit reduces the canonical reflected D action on the `(0,0)` basis vector
to `i` times the `(1,1)` basis vector, and the simplified bare-shift reflection
to `-i` times that vector. These are direct charge-word computations; no
oscillator action or placeholder theorem is used. The theorem proofs, full fresh
declaration/dependency axiom audit, placeholder/warning-free build, scoped lock,
and promotion remain outstanding.

## Independent review record

Reviewer `/root/v1s3_interface_review` issued two `REVISE` verdicts while the
interface was being completed. Findings included missing interface contracts,
a general-basis right-oscillator parity factor, malformed syntax compatibility,
a bare normal-factor tautology, and an incorrect unphased same-orientation
correlator claim. The parity and syntax statements were corrected, all missing
contracts were added, the tautology was replaced by self-adjointness, and the
false correlator identity was removed in favor of factor-ordered vertex/adjoint
transport with the position-phase ratio.

The source snapshot
`881107e4ea38703f7d36fd63d37709acd9fd33c842520c781b55116c55493f72`, companion
snapshot `deef466c9c5d2e317d915300297de7d768f31e78038796853231978b0a31ce34`
(as then reviewed), and audit snapshot
`9451bc5c3bde9c94a8a7d46c4c8187015bfa7c92c11a377dbb67ca356fd1c533` received
independent **PASS**. The reviewer confirmed the ordered correlator phase
orientation and no remaining same-orientation false identity. The concrete
L=4 audit witnesses establish canonical reflected D action `+i` and simplified
bare-shift reflection `-i` on the same charge basis vector. Reviewer identity,
reviewed hashes, findings, resolutions, and verdict are also recorded in
`docs/plans/v1-s3/phase-a-review.md`.

This file is the post-review status update; its exact current hash is recorded
in the review log after the documentation check. The reviewed companion snapshot
was the prior text version identified above. This is Phase A interface acceptance only. Proofs, full fresh proof/dependency
axiom audits, strict lock verification, and promotion remain separate gates.
The Hamiltonian application remains outside the accepted S2 algebra: its
oscillator, charge/zero-mode, and chemical-potential correction terms still
need an algebra-valued definition and a covariance proof. No finite-CAR or
physical interacting-ground-state conclusion follows.
