# V1-S2 charge words and formal vertices — accepted companion

Status: **Phase C complete; source promoted and frozen.** All 39 theorem contracts are proved. Source SHA-256: `17cab3f91f38bc218b18cd7a2fe9e2ec8abf13d487096c3c2fca3fdd5c107020`. Fresh audit of 119 declarations, zero-warning build, strict/Core locks, nonvacuity checks and independent final proof/package review PASS. Historical progress counts below describe their saved snapshots. No S3 work.

The detailed candidate mathematical interface, source hashes, convention
derivations, conditional correlator proof, normal-ordering audit, and checks
are in [`phase-a-review-packet.md`](../../../plans/v1-s2/phase-a-review-packet.md).
The current Phase B proof inventory, dead ends, validation gates, and resume
instructions are in [`phase-b-checkpoint.md`](../../../plans/v1-s2/phase-b-checkpoint.md);
a concise initialization prompt is in
[`follow-up-agent-prompt.md`](../../../plans/v1-s2/follow-up-agent-prompt.md).
The packet was independently reviewed as a mathematical specification. S1 is separately accepted by its promoted Core implementation and review receipt.

## Source reconciliation

- A08 uses a free algebra and the pullback
  `omegaP = omega0 ∘ bogoliubovMap(c,-s)`. Dressed fields use the forward
  substitution with `s`; applying it again would be wrong.
- A08 has contextual CCR descent and polynomial creation/annihilation
  representations. The candidate uses finite-word `MonoidAlgebra` syntax with
  an explicit conjugate/reverse/swap dagger and an evaluator into A08's free
  algebra. Operator identities are required only after polynomial
  representation; no literal CCR equality is asserted in free syntax.
- CH13's `phaseExponent` includes the finite-sea offset `h+N`; the simplified
  two-shift convention is connected to it by the explicit diagonal gauge in
  the review packet.
- Charge phase scalars act on the source before shifts. In `K†(x)K(y)` the
  inverse shift restores the original source before the adjoint phase is
  evaluated, yielding the positive Section 20.2 SC exponent.
- Section 20.2 and Appendix A08 currently agree on the positive SC exponent.
  No correction is indicated by the other snapshot's negative-sign report.
- Weyl, dressed-normal, and bare-normal vertices have distinct scalar
  prefactors. Neither normal-order convention is the principal theorem.

## Dependency and gate record

S1 is accepted and promoted in `Bosonize/Core/V1S1OrderedWick.lean` and
`Bosonize/Core/V1S1PairingCombinatorics.lean`; its companion records the
independent review, hashes, audits, and Phase C promotion. S2 imports the
accepted ordered-Wick and moment interface directly and does not copy its
proofs. The exact S2 Phase A interface passed review and was scoped-locked.
All 39 theorem contracts are proved and independently reviewed. Phase C moved the source byte-identically to Core; independent migration and
pedagogical reviews and all local validation gates pass. No S3 work is part of this sprint.

## Independent specification review

Reviewer `/root/v1_s2_spec_review` returned **PASS** on the mathematical
specification, including the explicit CH13 gauge, charge/source ordering,
finite-word syntax/evaluator carrier, conditional correlator derivation, and
normal-order factors. The reviewed packet hash is
`1208796d6addc30f951d4a4555b12b1dcfef338791b58cdbef5d9107fd8e92b1`; the
reviewer also checked that the three planning/review input hashes recorded in
that version match the files. The companion snapshot presented to the reviewer
had SHA-256
`af352a168267546ef23ed623d8cab9769b2a144c001f50711177bea17a519dc9`.
This is review of a natural-language specification only: it does not accept S1,
review S2 Lean declarations, or constitute Lean/build/lock evidence.


## Actual Lean Phase A interface review

The first actual-source review returned REVISE on SHA-256
`a9982c2acc277d2e7d61ef663d498f179a0ca5cf0d3a0b898e2c238241f4711c`.
It found that ordered lists made the adjoint product law false as literal list
equality, the carrier description disagreed with the implementation, the joint
functional was not tied to the tensor carrier, and the canonical gauge was not
connected to the vertices. The implementation was revised to multiset-valued
coefficients, a tensor-carrier matrix functional, canonical charge-selection
contracts, and finite-word syntax documentation. A second review found the
bare L-shift gauge ratio was conflated with the Klein sign and requested
charge-adjoint/composition and syntax-evaluator/dagger laws. Those corrections
are reflected in the final reviewed interface below.

The second actual-source review returned **REVISE** on Lean SHA-256
`dd9e2327d8c36c732ff88438061bcf88f328ce635f4399272e287327b15a33e1`, packet
`3702ac59bff6b45d5edbbb4bdfdf2c10f052a3f94dc7fb7c0d2192ee17936459`, and
companion `ec4c5911fbb3e6f3aa914fcb252c246c954d5cae8257f9f42a16f73b24696c59`.
Reviewer `/root/v1_s2_spec_review` found (1) the L-shift gauge contract stated
the combined Klein coefficient as the bare gauge ratio, (2) no charge action
adjoint/composition bridge to the formal adjoint, and (3) missing monoid
algebra evaluator and dagger laws. The gauge ratio is now corrected to
`(-1)^(N_L-1)` with a separate combined-sign contract. Charge pairing,
composition/action, tensor-factor, evaluator homomorphism, and dagger
anti-involution contracts have been added. These are still theorem placeholders
in Phase A and require a fresh independent review before locking.

The third actual-source review returned **REVISE** on Lean SHA-256
`d923d9b8003271a1386ca1a44556b5f43e35d869ed691be41498bfc9bd2ef6a4` and
identified the missing joint-carrier adjoint bridge. The fourth reviewed
candidate adds a basis-defined pairing on the actual tensor product, its
simple-tensor factorization contract, represented-action adjoint contract,
and joint-functional matrix-coefficient contract.

The fourth actual-source review by `/root/v1_s2_spec_review` returned
**PASS** on these exact hashes:

- Lean: `984132893e986956592cf291bba2ed4ff3ddfc8ba61b748f298814068d046bd7`
- packet: `3702ac59bff6b45d5edbbb4bdfdf2c10f052a3f94dc7fb7c0d2192ee17936459`
- companion: `e22f130ffbf2974edefd7eab1a34c166697bff6d82a774c8713d752c1b53f376`

The reviewer confirmed that the pairing is basis-defined on the tensor
carrier, factors to A08's monomial-norm pairing on simple tensors, and makes
the represented coefficient dagger a proof-relevant adjoint contract. This
PASS reviews the interface only; it does not certify subsequent proof bodies.
The scoped lock was committed in `0610d1495ebc4e95dec323c27faf22966e55e9d2`.
Phase B has proved `chargeWord_comp_action_contract`,
`oscSyntaxEval_one_contract`, `oscSyntaxEval_mul_contract`,
`jointCoeffFunctional_product_contract`, `chargeGauge_unitary_contract`, and
`source_phase_product_contract`. That earlier staging build succeeded with 26
placeholder warnings, and strict scoped-lock verification passes. The earlier
data-only audit covered 81 data declarations with standard axioms only; a
fresh final theorem/dependency axiom audit remains outstanding.


## Scheduled Phase B resumption — 2026-10-17

The charge singleton/linear-induction route, explicit syntax dagger laws,
represented oscillator and tensor adjoint bridges, all gauge/charge-selection
contracts, coefficient-action composition and multiset series-adjoint reversal
are now proved. All proof changes were confined to approved theorem bodies.
The strict lock and 36-file Core guard pass; the staging build has exactly eight
remaining placeholder warnings. Fresh axiom inspection of all 31 completed
theorems contains only the three permitted standard axioms. The independent
review is PASS for this partial package, not the eight outstanding contracts.
The detailed inventory, failed search routes and next proof dependencies are
in the current checkpoint. The commutator, field/exponential adjoints, variance,
Weyl correlator and both normal-ordering statements remain open. No Phase C,
S3, continuum, finite-CAR identification or publication acceptance is claimed.


## Field/variance proof batch after the first 18-proof checkpoint

The same-channel contraction symmetry, represented polynomial commutator,
field Hermiticity, inverse-pullback exponential-coefficient adjoint and exact
difference variance have now passed sandboxed compilation/axiom/target-warning
gates and independent review. The exact five-proof receipt is
[`phase-b-field-review-2026-10-17.json`](../../../plans/v1-s2/phase-b-field-review-2026-10-17.json).
A fresh staging build has three placeholder warnings; all 36 completed theorem
closures have standard axioms only. The main correlator and both prefactor
contracts remain open. Historical partial-package counts above describe their
recorded snapshots; the current checkpoint contains the complete live inventory.


## Weyl-correlator proof — October 18, 2026

The exact coefficientwise formal Weyl correlator now has a complete proof,
including canonical source-charge selection, represented coefficient adjoints,
contextual finite Cauchy/binomial algebra, the S1 even/odd moment calculation,
variance `4*g_J*D1`, and both `L^-1` factors. Its current source passed the
sandboxed statement/compiler/target-warning/axiom gate and independent review.
Receipt: [`phase-b-weyl-review-2026-10-18.json`](../../../plans/v1-s2/phase-b-weyl-review-2026-10-18.json).
All 37 completed theorem closures use only standard axioms. The staging build
still has two normal-prefactor placeholder warnings; neither Phase B nor
Phase C is complete. The theorem remains a formal coefficient identity, with
no finite-CAR, analytic or continuum identification.


## Final normal-prefactor proofs and Phase B acceptance — October 18, 2026

The dressed and bare contracts extract their defined scalar Cauchy multipliers. Local coefficient bilinearity is extended by multiset induction, a curried additive functional and an explicit finite reindexing bijection. This argument preserves oscillator word order and never assumes multiplicativity of the state. Both complete bodies passed the sandboxed statement/compiler/warning/axiom gate and independent review. The final source retains every locked definition, header, import and option.

[Final Phase B evidence](../../../plans/v1-s2/phase-b-validation.md); [independent review](../../../plans/v1-s2/phase-b-normal-review-2026-10-18.json). All 39 theorem closures and 80 data/type declarations have only standard axioms. The proof does not separately establish a creator/annihilator factorization or BCH identity; those remain reference interpretation beyond the locked normal-multiplier contracts.


## Promoted declaration and pedagogy mapping

The [promoted module](../../../../Bosonize/Core/V1S2FormalVertices.lean) keeps
namespace `Bosonize.V1S2` and imports only accepted S1. It contains 39 theorem
contracts and 80 data/type declarations, all covered by the fresh aggregator
axiom audit. The source SHA-256 is
`17cab3f91f38bc218b18cd7a2fe9e2ec8abf13d487096c3c2fca3fdd5c107020`.

| Mathematical content | Declaration anchors | Pedagogical location |
| --- | --- | --- |
| Tensor basis pairing and factorization | `jointPairing_basis_contract`, `jointPairing_tmul_factor_contract` | Chapter 20 S2 carrier and weighted pairing |
| Charge action, composition and adjoint | `chargeWordAction_basis_contract`, `chargeWord_comp_action_contract`, `chargeWord_adjoint_pairing_contract` | S2 charge bijections/source amplitudes |
| Syntax evaluator and dagger | `oscSyntax_roundtrip_freeAlgebra_contract`, `oscSyntaxEval_mul_contract`, `oscSyntaxDagger_involutive_contract`, `oscSyntaxDagger_mul_contract` | S2 finite-word syntax |
| Represented adjoint and matrix functional | `jointCoeffAction_adjoint_pairing_contract`, `jointCoeffFunctional_is_matrix_coefficient_contract`, `jointCoeffFunctional_product_contract`, `jointCoeffFunctional_adjoint_contract` | S2 inverse pullback and pairing |
| Gauge and source phase | `chargeGauge_unitary_contract`, both `gauge_adapter_*_contract`, both `canonical_charge_selection_*_contract` | S2 CH13 gauge and restored-source phase |
| Same-channel field algebra and variance | `same_channel_commutator_contract`, `represented_same_channel_commutator_contract`, `field_adjoint_on_polynomials_contract`, `difference_variance_contract` | S2 cancellation and variance |
| Series/exponential adjoints | `oscillatorExp_adjoint_coefficient_contract`, `oscillator_syntax_dagger_inverse_pullback_represents_adjoint_contract`, `vertexSeriesAdjoint_reverses_product_contract` | S2 coefficientwise construction |
| Gaussian Weyl correlator | `coefficientwise_weyl_correlator_contract` | Chapter 20 (20.8)–(20.9), S2 even/odd coefficients |
| Defined normal multipliers | `dressed_normal_prefactor_contract`, `bare_normal_prefactor_contract` | S2 twofold scalar Cauchy factors |

The corresponding note is [Chapter 20](../../../../notes/md/ch20_CDW.md).
All 17 pre-existing display equations and original reference targets were
preserved; only three stale status passages were revised, with an added S2
realization section. The external author supplied the draft; supervisor
corrections fixed links, inverse pullback, source-charge ordering, the two
vertex normalizations, and S3 boundaries before independent review.

## Phase C migration evidence

The source was moved from `BosonizeStubs/` to `Bosonize/Core/` without changing
any byte. Its import, namespace, definitions, statements and proof bodies are
identical to the final reviewed Phase B source. The strict manifest changes
only the S2 path key, retaining all 39 theorem and 85 command records exactly.
The Core manifest adds only the S2 source hash; all 36 earlier hashes remain
unchanged. Core and staging aggregators route downstream imports through
`Bosonize`. Historical manifests and review receipts remain intact.

Local `make ci` passes 69 guard tests, both library builds and 18 verifier
tests. The promoted aggregator audit covers all 119 S2 declarations with only
`propext`, `Classical.choice`, `Quot.sound`. No source placeholders or compiler
warnings remain. The deliberate `Fixture.value` sorryAx in CI is a verifier
rejection test, not an accepted dependency. Nonvacuity checks establish the
squeezed gains 1/9 and 9 and a nonzero degree-zero coefficient 1/4 for every
mode cutoff at circumference two. No GitHub CI, push, publication, finite-CAR
identification, analytic evaluation, or S3 completion is claimed.


## Final acceptance — October 18, 2026

Independent actual migration, pedagogical and reference-preservation reviews
all returned PASS, with no actionable findings. Exact reviewed source/note
hashes and provider provenance are in the [Phase C receipt](../../../plans/v1-s2/phase-c-review-2026-10-18.json).
The complete [validation record](../../../plans/v1-s2/validation.md),
[aggregator axiom audit](../../../plans/v1-s2/axiom-audit.txt) and
[local CI output](../../../plans/v1-s2/ci-output.txt) establish S2 acceptance.
S3 remains outside this sprint. The corresponding pedagogical note retains
all reference formulas and makes the normal-multiplier/BCH boundary explicit.
