# V1-S2 Phase B checkpoint — 2026-10-17

## Status

S1 is accepted and promoted. S2 has a reviewed and scoped-locked Phase A
interface (`0610d1495ebc4e95dec323c27faf22966e55e9d2`) and is partway through
Phase B. It is **not proof-complete** and has not entered Phase C. No S3 work
has started.

Current S2 staging source:

- `BosonizeStubs/V1S2FormalVertices.lean`
- SHA-256: `f3056b313db9d90f10d238be1a0555460026173e979ae82a195fdc81ec8a6a07`
- 26 `sorry` theorem contracts remain.

The exact Phase A interface review was PASS by `/root/v1_s2_spec_review` on
Lean SHA-256 `984132893e986956592cf291bba2ed4ff3ddfc8ba61b748f298814068d046bd7`,
packet SHA-256 `3702ac59bff6b45d5edbbb4bdfdf2c10f052a3f94dc7fb7c0d2192ee17936459`,
and companion SHA-256 `e22f130ffbf2974edefd7eab1a34c166697bff6d82a774c8713d752c1b53f376`.
That PASS covers the interface, not the Phase B proof bodies. The reviewer
later returned a proof-design diagnosis for
`chargeWord_adjoint_pairing_contract` against source SHA-256
`f3056b313db9d90f10d238be1a0555460026173e979ae82a195fdc81ec8a6a07`; it is
not a proof verdict.

## Reused S1 interface

S2 imports `Bosonize.Core.V1S1OrderedWick`. Its accepted implementation and
companion are recorded in the S1 Phase C evidence. S2 reuses
`OscLinearForm`, `linearElement`, `contraction`, `wordElement`, `wordForms`,
`orderedPairingSum`, `omegaP_pull_through`, `omegaP_ordered_wick`,
`omegaP_odd_word_zero`, `omegaP_single_odd_moment`, `omegaP_single_even_moment`,
`dressedGeneratorForm`, and `dressedForm`.
S2 does not copy S1 proofs or treat a proposed theorem as proved merely
because the interface elaborates.

## Phase B proofs completed so far

These six contracts have proof bodies and compile:

- `chargeWord_comp_action_contract`
- `oscSyntaxEval_one_contract`
- `oscSyntaxEval_mul_contract`
- `jointCoeffFunctional_product_contract`
- `chargeGauge_unitary_contract`
- `source_phase_product_contract`

The current 26 placeholders are:

```text
jointPairing_tmul_factor_contract
chargeWord_adjoint_pairing_contract
oscSyntax_roundtrip_freeAlgebra_contract
oscSyntaxDagger_involutive_contract
oscSyntaxDagger_mul_contract
jointCoeffAction_mul_contract
jointCoeffAction_adjoint_pairing_contract
jointCoeffFunctional_is_matrix_coefficient_contract
jointCoeffFunctional_adjoint_contract
coefficientwise_weyl_correlator_contract
dressed_normal_prefactor_contract
bare_normal_prefactor_contract
gauge_adapter_right_contract
gauge_adapter_left_contract
gauge_adapter_left_klein_contract
charge_selection_D_contract
charge_selection_S_contract
canonical_charge_selection_D_contract
canonical_charge_selection_S_contract
same_channel_commutator_contract
represented_same_channel_commutator_contract
field_adjoint_on_polynomials_contract
oscillatorExp_adjoint_coefficient_contract
oscillator_syntax_dagger_inverse_pullback_represents_adjoint_contract
vertexSeriesAdjoint_reverses_product_contract
difference_variance_contract
```

The main coefficientwise correlator is therefore still only a contract. Its
normalization and derivation are documented in the reviewed packet, but they
are not Lean results yet.

## Dead ends and useful diagnostics

1. **Charge-word adjoint via a direct support-union sum.** A direct proof from
   the definition of `chargePairing` gets trapped in finite-support bookkeeping:
   the pairing sums over a union of supports, and action reindexes source
   coefficients through a charge equivalence. The authorized reviewer
   `/root/v1_s2_spec_review` confirmed the identity is mathematically correct
   and recommended a basis-first proof: establish a singleton pairing lemma;
   prove the action/adjoint identity for two singleton vectors by splitting on
   `f.target N = M`; then extend by `Finsupp.induction_linear` in each vector.
   To simplify additivity and scalar steps, first rewrite the union-support
   pairing as a sum over the first vector's support, or define a helper with
   that finite domain. No such proof has yet been integrated.

2. **Oscillator syntax dagger involution by blind `ext`/`simp`.** The attempt
   did not close the goal because coefficient reindexing through word reversal,
   generator swap, and finite support was left implicit. It was reverted to
   the reviewed placeholder. Resume with explicit lemmas for `wordDagger`
   involution and its induced equivalence on `List` support, then prove the
   `Finsupp` coefficient map by extensionality and reindexing. Do not treat
   this failed tactic attempt as evidence the theorem is false.

3. **Charge-action composition by an unsuitable induction alternative.** An
   initial induction pattern failed to match `Finsupp`; this was resolved by
   `Finsupp.induction_linear`, explicit use of the action additivity contracts,
   and a singleton case. The working proof is now in the source.

4. **Bogoliubov direction.** A08's functional uses the inverse pullback
   `bogoliubovMap c (-s)`, while S2 fields are forward dressed forms. Applying
   the substitution twice is a known invalid route; the current definitions
   keep those roles separate. Preserve this direction when proving the
   represented adjoint and variance contracts.

## Validation and current gates

At this checkpoint:

- `lake build BosonizeStubs` succeeds, with 26 expected placeholder warnings.
- `python3 scripts/guards/stub_lock.py --check --strict` passes: 1,153
  statements and 1,211 frozen commands.
- `python3 scripts/guards/core_lock.py` verifies all 36 complete Core files.
- The earlier Phase A data-only audit covered 81 data declarations and
  reported only standard axioms. A fresh audit of completed theorem and
  dependency declarations remains outstanding.
- Zero-warning and zero-placeholder checks, all required nonvacuity checks,
  independent review of the completed proof package, integration/CI, Phase C
  promotion, and pedagogical synchronization remain open.
- Commits: `0610d14` (reviewed S2 interface lock), `2dd8ea8` (initial Phase B
  proofs and status checkpoint).

The immediate resume target is Phase B against the existing strict lock. Begin
with the charge pairing singleton/helper route and the syntax dagger laws;
then discharge the charge/gauge and represented adjoint dependencies, same-
channel commutator and difference variance, coefficientwise Weyl theorem, and
the two normal-ordering prefactor theorems. Do not loosen statements, alter
physical conventions, add axioms, promote an incomplete file, or start S3.
