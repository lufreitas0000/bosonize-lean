# V1-S2 Phase B checkpoint — scheduled resumption of 2026-10-17

## Current status

S1 is accepted and promoted. S2 remains **Phase B in progress** under the
unchanged reviewed interface lock from
`0610d1495ebc4e95dec323c27faf22966e55e9d2`. No Phase C promotion or S3 work
has started. This resumption began at `083df9dbd7148a5c71ef09cce5a46558825a3907`.

- Source: `BosonizeStubs/V1S2FormalVertices.lean`
- SHA-256: `37e52dd7486b0cb0d6a74e53f386f7d03941f1b7043cd24b9af63f45c109afc9`
- Previous checkpoint source: `f3056b313db9d90f10d238be1a0555460026173e979ae82a195fdc81ec8a6a07`
- **23 newly proved contracts, 36 completed S2 theorem declarations total,
  and three unchanged placeholder contracts remain.**
- First 18-proof checkpoint commit: `c2da192b29e068f9ac40e0958c77d2d81e604adb`.
- Exact independent review receipts:
  [`phase-b-proof-review-2026-10-17.json`](phase-b-proof-review-2026-10-17.json)
  and [`phase-b-field-review-2026-10-17.json`](phase-b-field-review-2026-10-17.json).

## Proofs completed during this resumption

- `jointPairing_tmul_factor_contract`
- `chargeWord_adjoint_pairing_contract`
- `oscSyntax_roundtrip_freeAlgebra_contract`
- `oscSyntaxDagger_involutive_contract`
- `oscSyntaxDagger_mul_contract`
- `jointCoeffAction_mul_contract`
- `jointCoeffAction_adjoint_pairing_contract`
- `jointCoeffFunctional_is_matrix_coefficient_contract`
- `jointCoeffFunctional_adjoint_contract`
- `gauge_adapter_right_contract`
- `gauge_adapter_left_contract`
- `gauge_adapter_left_klein_contract`
- `charge_selection_D_contract`
- `charge_selection_S_contract`
- `canonical_charge_selection_D_contract`
- `canonical_charge_selection_S_contract`
- `same_channel_commutator_contract`
- `represented_same_channel_commutator_contract`
- `field_adjoint_on_polynomials_contract`
- `oscillatorExp_adjoint_coefficient_contract`
- `oscillator_syntax_dagger_inverse_pullback_represents_adjoint_contract`
- `vertexSeriesAdjoint_reverses_product_contract`
- `difference_variance_contract`

Each proof passed the sandboxed `agentctl.theorem.submit_proof` gate,
statement/context and forbidden-token scans, target warning checks and
transitive axiom inspection. Independent review passed the first 18 proofs
at source `a639ded883ef762f34063a0a1425dc2cbdab4059d7be4026ce4d6e2c83e5dc03`
and the following five-proof delta at source
`b54f7fdbe407d44455cf22eed03b9a85f6cc02d1bdd3ccacd85a67a15fcd2ce9`.
The current hash differs only by removal of spaces from four blank lines;
all nonblank source lines remain byte-identical. The exact cleanup hash chain
is recorded in the five-proof receipt. Review coverage
includes every changed body. These are partial-package verdicts; they do not
accept the remaining three stubs.

The six principal contracts from the earlier checkpoint and its seven proved
auxiliary declarations are retained, accounting for 36 completed declarations.
Accepted S1 declarations are imported and reused; no S1/Core source was edited.

## Remaining contracts

- `coefficientwise_weyl_correlator_contract`
- `dressed_normal_prefactor_contract`
- `bare_normal_prefactor_contract`

The main Weyl correlator and both normal-ordering results remain unproved.
Formal vertices have not been identified with finite CAR fields.

## Proof routes and dead ends

1. **Charge adjoint — resolved:** reduce the union-support pairing to a sum
   over either operand, prove singleton pairing, induct linearly and use the
   explicit source coefficient at `w.target.symm N`. This replaces the failed
   direct union-support reindexing attempt.
2. **Dagger and evaluator — resolved:** explicit word-dagger involution,
   `Finsupp.sum_sum_index`, `MonoidAlgebra.induction_linear`, and the universal
   evaluator homomorphism. Wrong induction alternatives and blind `ext`/`simp`
   attempts were discarded.
3. **Gauge and charge selection — resolved:** normalize quadratic integer
   finite differences before `omega`. Use complex group-with-zero zpower laws.
   Inverse shifts restore the source before the adjoint phase is evaluated;
   canonical gauge factors cancel by unit modulus.
4. **Tensor pairing and adjoint — resolved:** enlarge only to the product
   of the charge/monomial supports, factor the resulting finite sum and use
   the current `TensorProduct.inductionOn`. The later syntax-adjoint contract
   is derived locally where a forward reference would otherwise be required.
5. **Series adjoint — resolved:** `Multiset.bind_map_comm` and reflection of
   the finite Cauchy index preserve multiplicities while reversing products.
6. **Fields and commutators — resolved:** supply a local finite instance for
   the two orientations, prove explicit `qForm` and bare field coefficients,
   extend coefficient sums to the finite generator universe, and evaluate
   the existing S1 contraction kernel. Three external commutator attempts
   failed (output exhaustion or nonexistent helper names); an independent
   diagnosis led to this explicit route. Receipts `55929dc16b`, `a3eb3c8b99`.
   For represented commutation, reduce each generator commutator to the
   antisymmetric contraction scalar using A08 CCR, then collect scalar
   multiples with `congrArg` and finite sums. Rewriting `smul_sub` directly
   at the final goal failed; the diagnosed congruence route compiled.
7. **Field/exponential adjoints — resolved:** conjugate field coefficients,
   reindex the creator/annihilator swap and use A08's accepted word-adjoint
   theorem. Root conjugation is proved for every `L`, including `L = 0`,
   as required by the field contract. Preserve the inverse Bogoliubov
   pullback. Extend Hermiticity through powers and the real factorial scalar;
   do not apply the forward substitution twice. Remove actual linter causes
   instead of suppressing warnings.
8. **Variance — resolved:** compute the finite symbolic variance, establish
   the exact exponential/root cosine identity, and reindex `Fin M` to
   `Finset.Icc 1 M`. The resulting coefficient is exactly `4*g_J*D1`.
   Explicitly reduce the constructed `Fin.val` before `omega` in the
   surjectivity proof and push the real-sum cast before distributing scalars.
   This proof includes the `M = 0` case through empty sums.
9. **Weyl correlator — open:** external attempt `69d4c6ba99` failed at the
   expanded coefficientwise Cauchy sum. Blind unfolding of the vertices
   does not supply the binomial/moment argument and is not proof evidence.
   An auxiliary Gaussian-coefficient lemma has compiled in scratch with
   standard axioms only, using accepted S1 even/odd moments and the proved
   variance. It is not an imported staging declaration; reuse its body as
   a local helper, not as a nonexistent library name. The main missing bridge must respect
   represented/contextual same-channel commutation and operator order.

## Fresh validation and remaining gates

- Strict statement/context lock: **PASS**, 1,153 statements and 1,211 frozen
  commands. No lock baseline was regenerated.
- Complete-source Core guard: **PASS**, all 36 existing Core files.
- `lake build BosonizeStubs`: **PASS**, exactly three S2 placeholder warnings
  and no other warnings. Existing Core tactic suggestions are informational.
- Fresh `#print axioms` for **all 36 completed S2 theorem declarations**:
  only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` in their
  transitive closures. The three remaining stubs are not included as proofs.
- Strict/Core manifest SHA-256 respectively:
  `7ab7800ef7fa313ed34b7aac48a08c3c5a7a1e2bda29783edeaf3a85a9539cd1`,
  `cbe522f531b1bb0b0ac6950527b01ca2bfff32976a833c4898b68584f7c280af`.
- S1 ordered-Wick and pairing-combinatorics source SHA-256 respectively:
  `f26d52cb29008f7d39030157368b7b9131bf14a4db173e97ef404062220852a9`,
  `33fefe1fafbdde6c544925a641ac8cdec496ce571f3036558500a53ddb0ddeff`.
- Full Phase B acceptance (zero placeholders/warnings, full closure and
  nonvacuity audits, final review), CI/integration, Phase C promotion and
  pedagogical review remain open. No push/publication has occurred.
- Pre-existing unrelated tracked/untracked changes were not edited or staged.

## Exact next action

Prove the formal Cauchy/binomial reduction of the ordered exponential product
using the accepted adjoint, commutator, charge-selection and variance results.
Apply accepted S1 single-form moments coefficientwise, including odd vanishing,
even factorial cancellation and the two normalization factors. Then prove
both scalar-convolution normal-ordering prefactors. Preserve the locked
interface, S1/Core sources and finite/formal boundaries. Obtain independent
review of actual new proofs and fresh strict lock/build/axiom/warning/placeholder
and nonvacuity evidence before entering the authorized Phase C gates. No S3.

Scratch Gaussian-coefficient source SHA-256: `56c535cdac18e7a94527c8a827c658044b33e3e1b562f1acbb0ad18d8936f9d6`.

## Independently reviewed dependency-order repair — 2026-10-18

The three remaining correlator/prefactor contracts originally preceded the
charge, field, commutator and variance results needed in their proofs. Lean
cannot use forward references. The three unchanged open declarations were
moved after those prerequisites, inside the same namespace and without
crossing a non-theorem command. The existing authoritative guard verified
identical statements and non-theorem context hashes; no lock amendment or
regeneration was needed. An independent PASS covers the exact reordered
source. The receipt is
[`phase-b-dependency-order-review-2026-10-18.json`](phase-b-dependency-order-review-2026-10-18.json).
The source chain is: proof-reviewed `b54f7fd...5fcd2ce9`, blank-line cleanup
`0d684a41...fe0c233`, and reviewed declaration reorder
`37e52dd7...109afc9`. Recompute the full hashes from the receipts.

The separate scratch `ContextualBinomial.lean` now compiles a generic additive
functional binomial theorem under explicit two-sided contextual commutation,
using a local `RingCon` quotient and `Commute.add_pow`. Its axiom closure is
standard only. It is not imported into staging; inline the checked proof as a
local helper if using that route. This does not yet supply the actual field
contextual-CCR or coefficientwise syntax/charge/Cauchy bridges.
