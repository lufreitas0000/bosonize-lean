# V1-S2 charge words and formal vertices — Phase A companion

Status: **S1 accepted; S2 Phase A interface reviewed and locked; Phase B in progress.** The interface baseline is `0610d1495ebc4e95dec323c27faf22966e55e9d2`. This resumption proved 23 additional contracts: 36 S2 theorem declarations are now complete, with three placeholders remaining (the Weyl correlator and two normal-ordering results). Current source SHA-256: `37e52dd7486b0cb0d6a74e53f386f7d03941f1b7043cd24b9af63f45c109afc9`. Independent review covers all 23 changed proofs through the two exact partial-package receipts linked in the current checkpoint. S2 is not proof-complete; no Phase C or S3 work has started.

The detailed candidate mathematical interface, source hashes, convention
derivations, conditional correlator proof, normal-ordering audit, and checks
are in [`phase-a-review-packet.md`](../plans/v1-s2/phase-a-review-packet.md).
The current Phase B proof inventory, dead ends, validation gates, and resume
instructions are in [`phase-b-checkpoint.md`](../plans/v1-s2/phase-b-checkpoint.md);
a concise initialization prompt is in
[`follow-up-agent-prompt.md`](../plans/v1-s2/follow-up-agent-prompt.md).
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
Phase B is incomplete; theorem contracts remain placeholders. No S3 work is
part of this sprint.

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
[`phase-b-field-review-2026-10-17.json`](../plans/v1-s2/phase-b-field-review-2026-10-17.json).
A fresh staging build has three placeholder warnings; all 36 completed theorem
closures have standard axioms only. The main correlator and both prefactor
contracts remain open. Historical partial-package counts above describe their
recorded snapshots; the current checkpoint contains the complete live inventory.
