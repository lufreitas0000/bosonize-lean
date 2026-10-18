# V1-S2 Phase B checkpoint — resumed 2026-10-17 at 23:18 (America/Fortaleza)

## Current status

S1 remains accepted and promoted. S2 is **Phase B in progress**, with the
reviewed interface lock from `0610d1495ebc4e95dec323c27faf22966e55e9d2` intact.
This resumption began at HEAD `083df9dbd7148a5c71ef09cce5a46558825a3907`.
No Phase C promotion or S3 work has started.

- Source: `BosonizeStubs/V1S2FormalVertices.lean`
- Current SHA-256: `a639ded883ef762f34063a0a1425dc2cbdab4059d7be4026ce4d6e2c83e5dc03`
- Previous source SHA-256: `f3056b313db9d90f10d238be1a0555460026173e979ae82a195fdc81ec8a6a07`
- **18 newly completed contracts; 31 completed theorem declarations total;
  eight unchanged placeholder contracts remain.**
- Exact partial-package review and validation receipt:
  [`phase-b-proof-review-2026-10-17.json`](phase-b-proof-review-2026-10-17.json).

## Newly proved during this resumption

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
- `oscillator_syntax_dagger_inverse_pullback_represents_adjoint_contract`
- `vertexSeriesAdjoint_reverses_product_contract`

Each new body passed the `agentctl.theorem.submit_proof` gate: statement/context
preservation, forbidden-token scan, sandboxed compilation, and transitive target
axiom inspection. An independent `api-fast` reviewer returned **PASS** for this
actual partial package on the exact current source hash. Earlier, an independent
`api-pro` review passed the first eight proofs at source
`d5c40f8045b266fb17231af7c976258a5291e65187184323352a75c2bc564a5f`.
Neither verdict accepts the remaining stubs or certifies the full correlator.

The previously completed six principal contracts remain proved:
`chargeWord_comp_action_contract`, `oscSyntaxEval_one_contract`,
`oscSyntaxEval_mul_contract`, `jointCoeffFunctional_product_contract`,
`chargeGauge_unitary_contract`, and `source_phase_product_contract`.
Seven earlier auxiliary theorem declarations also remain proved, accounting
for the total of 31. S1 declarations are imported from Core and reused;
no S1/Core source was edited.

## Remaining contracts

- `coefficientwise_weyl_correlator_contract`
- `dressed_normal_prefactor_contract`
- `bare_normal_prefactor_contract`
- `same_channel_commutator_contract`
- `represented_same_channel_commutator_contract`
- `field_adjoint_on_polynomials_contract`
- `oscillatorExp_adjoint_coefficient_contract`
- `difference_variance_contract`

The Weyl correlator and both normal-ordering results are still unproved.
The formal vertices have not been identified with finite CAR fields.

## Proof routes and bounded dead ends

1. **Charge adjoint: resolved.** Rewrite the union-support pairing as a sum
   over either operand's support. Establish singleton evaluation, induct
   linearly in the first vector, and use the explicit coefficient formula
   `(action w v) N = v (w.target.symm N) * w.amplitude (w.target.symm N)`.
   This avoids the failed direct support-union reindexing route.
2. **Syntax dagger: resolved.** Prove word-dagger involution explicitly, then
   flatten the nested `Finsupp.sum`. For multiplication use
   `MonoidAlgebra.induction_linear`, explicit add/single laws, word reversal,
   and complex coefficient conjugation. Blind `ext`/`simp` and the wrong
   monoid-algebra induction principle failed.
3. **Gauge and charge phases: resolved.** Normalize integer quadratic finite
   differences before `omega`; use the group-with-zero zpower lemmas on
   complex numbers. In charge selection, the inverse shift restores the
   source before the adjoint phase is evaluated. Canonical gauge factors
   cancel by their unit-modulus identities; no multiplicativity of the
   oscillator functional is inferred.
4. **Joint carrier: resolved.** Enlarge the first tensor coordinate support
   only to the product of charge and monomial supports; factor that finite
   sum. Extend adjoint identities with the nondeprecated
   `TensorProduct.inductionOn`. Since the syntax-adjoint theorem occurs
   later in the locked file, the joint-adjoint body contains its local
   derivation from A08's accepted word-adjoint result; there is no forward
   reference or new top-level helper.
5. **Series adjoint: resolved.** Use multiset `bind_map_comm` and explicit
   reflection of the Cauchy index; preserve multiplicities and reverse
   charge and oscillator products.
6. **Same-channel commutator: still open.** Three external attempts produced
   either an output-budget exhaustion or references to nonexistent names
   (`Bosonize.V1S1.same_channel_commutator`, then
   `Bosonize.same_channel_commutator`). All failed the compiler gate; no
   candidate was integrated. Receipts: `55929dc16b`, `a3eb3c8b99`.
   A targeted independent diagnosis was requested. Do not retry those
   nonexistent declarations or treat a contract as an accepted theorem.
7. **Field Hermiticity: still open.** Explicit `qForm` and bare field
   coefficient calculations have been checked in scratch. The current
   candidate reduces polynomial adjointness to conjugate coefficients and
   a creator/annihilator-swap reindexing of a finite sum. Its local
   exponent-normalization step is not yet accepted. Preserve full scratch
   candidate/diagnostics for independent diagnosis; do not integrate it
   with an unclosed goal. The root-conjugation argument must also cover
   `L = 0`, since this contract has no positivity hypothesis on `L`.

## Fresh validation and gates

- `python3 scripts/guards/stub_lock.py --check --strict`: **PASS**, 1,153
  statements and 1,211 frozen commands. The manifest was not regenerated.
- `python3 scripts/guards/core_lock.py`: **PASS**, all 36 frozen Core sources.
- `lake build BosonizeStubs`: **PASS**, exactly eight placeholder warnings
  in S2 and no additional warnings. Informational tactic suggestions in
  existing Core dependencies are not warnings or new source changes.
- Fresh `#print axioms` for **all 31 completed S2 theorem declarations**:
  only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` in
  these completed theorem closures. The eight stubs remain unproved.
- Strict/core manifest SHA-256 respectively:
  `7ab7800ef7fa313ed34b7aac48a08c3c5a7a1e2bda29783edeaf3a85a9539cd1`,
  `cbe522f531b1bb0b0ac6950527b01ca2bfff32976a833c4898b68584f7c280af`.
- S1 ordered-Wick and pairing-combinatorics source hashes respectively:
  `f26d52cb29008f7d39030157368b7b9131bf14a4db173e97ef404062220852a9`,
  `33fefe1fafbdde6c544925a641ac8cdec496ce571f3036558500a53ddb0ddeff`.
- Full Phase B zero-placeholder/zero-warning acceptance, full theorem closure
  and nonvacuity audits, final proof-package review, CI/integration, Phase C
  promotion, and pedagogical synchronization remain open.
- Unrelated tracked and untracked changes present at resumption were not
  edited or staged. No push/publication is part of this checkpoint.

## Exact next action

Read the targeted diagnosis and archived scratch evidence. Finish the
Hermitian coefficient/field adjoint proof and the explicit finite-mode
contraction computation. Then establish represented same-channel commutation,
inverse-pullback exponential adjoints, the difference variance (including the
finite-index/Dirichlet cosine identity), coefficientwise Weyl correlator from
S1 moments, and both scalar-convolution normal-ordering prefactors. Preserve
the exact locked statements, all S1/Core sources, rightmost-first charge
ordering, and inverse Bogoliubov pullback. Obtain independent review of every
new actual proof batch and pass all Phase B gates before Phase C.
