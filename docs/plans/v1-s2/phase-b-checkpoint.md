# V1-S2 current checkpoint — Phase C complete

All 39 contracts are proved, independently reviewed, promoted and frozen.
All 119 declarations audit with standard axioms only; zero warnings/placeholders.
Strict/Core guards, both builds, local CI, nonvacuity, actual migration and
pedagogical reviews PASS. Source SHA-256:
`17cab3f91f38bc218b18cd7a2fe9e2ec8abf13d487096c3c2fca3fdd5c107020`. See [final validation](validation.md),
[Core companion](../../companion/Bosonize/Core/V1S2FormalVertices.md),
[final B review](phase-b-normal-review-2026-10-18.json) and
[C review](phase-c-review-2026-10-18.json). No S2 gate remains open; S3 has not
started. No push/publication/GitHub CI is claimed. The one-time continuation
automation was consumed and deleted.

The following saved checkpoint is historical; its two remaining contracts, quota stop and Phase C gates have now been resolved. It preserves the proof inventory, dead ends and prior evidence.

# V1-S2 Phase B checkpoint — scheduled resumption, October 17–18, 2026

## Current status and source identity

**Phase B remains in progress.** This resumption proved **24 additional
contracts**, including the coefficientwise Weyl correlator. S2 now has
**37 completed theorem declarations and two unchanged placeholder contracts**.
S1 remains promoted; no Phase C promotion or S3 work has started.

- Current source: `BosonizeStubs/V1S2FormalVertices.lean`
- Current SHA-256: `3e0b72ac30fb213d36ac91e54ffee297dee39910dfe5734f54aa52bd2d472a02`
- Starting HEAD: `083df9dbd7148a5c71ef09cce5a46558825a3907`
- Starting source SHA-256: `f3056b313db9d90f10d238be1a0555460026173e979ae82a195fdc81ec8a6a07`
- Reviewed interface-lock baseline: `0610d1495ebc4e95dec323c27faf22966e55e9d2`
- Recorded commits before the final Weyl checkpoint:
  `c2da192b29e068f9ac40e0958c77d2d81e604adb` (18 proofs),
  `65f6b989f69e5bddaf40f583fb2ee6fe602ca06a` (five field/variance proofs),
  `80393ee` (reviewed theorem-order repair), and
  `3a1448d1f2695f078b88ee758b3ac3de2f8f3090` (Weyl proof and exact independent review).
  A following documentation-only commit records this final checkpoint.

## Completed during this resumption

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
- `coefficientwise_weyl_correlator_contract`

The six principal contracts and seven auxiliary declarations from the earlier
checkpoint remain proved, accounting for the total of 37. Each new proof
passed `agentctl.theorem.submit_proof`: statement/context preservation,
forbidden-token scanning, sandboxed compilation, target warning checks and
transitive standard-axiom inspection. Accepted S1 declarations are reused
through the existing Core import, without edits to S1/Core.

## Exact independent review chain

- First 18-proof partial package: **PASS**, source
  `a639ded883ef762f34063a0a1425dc2cbdab4059d7be4026ce4d6e2c83e5dc03`.
  Receipt: [`phase-b-proof-review-2026-10-17.json`](phase-b-proof-review-2026-10-17.json).
- Next five field/variance proofs: **PASS**, reviewed source
  `b54f7fdbe407d44455cf22eed03b9a85f6cc02d1bdd3ccacd85a67a15fcd2ce9`.
  Four otherwise blank lines were then trimmed, producing source
  `0d684a41e006bec922df38e0245a998d2d206ddfcdeacc44eb1f759e9fe0c233`;
  all nonblank lines stayed byte-identical. Receipt and cleanup chain:
  [`phase-b-field-review-2026-10-17.json`](phase-b-field-review-2026-10-17.json).
- Dependency-order repair: **PASS**, exact source
  `37e52dd7486b0cb0d6a74e53f386f7d03941f1b7043cd24b9af63f45c109afc9`.
  The three correlator/prefactor declarations originally preceded their
  required charge/field/variance theorems; Lean cannot use forward references.
  Only these three unchanged open declarations moved after their prerequisites,
  within the same namespace and across no non-theorem command. The existing
  strict lock passed unchanged: no manifest regeneration/amendment occurred.
  Receipt: [`phase-b-dependency-order-review-2026-10-18.json`](phase-b-dependency-order-review-2026-10-18.json).
- Weyl-correlator proof: **PASS** on the current exact source hash above.
  Receipt: [`phase-b-weyl-review-2026-10-18.json`](phase-b-weyl-review-2026-10-18.json).
  This covers its local contextual-CCR, quotient-binomial, exponential-adjoint,
  Gaussian-moment, charge and multiset Cauchy helpers. It is not a verdict on
  the two remaining normal-ordering stubs or whole Phase B/C completion.

## Remaining contracts

- `dressed_normal_prefactor_contract`
- `bare_normal_prefactor_contract`

The Weyl formal-series theorem is now proved. Both dressed/bare prefactor
contracts remain unproved. No formal vertex is identified with a finite CAR
field; no analytic convergence, `t = 1` substitution or continuum claim is made.

## Proof design, failures and resolutions

1. **Charge adjoint:** the direct union-support/reindexing route failed.
   Restrict the pairing sum to either support, prove singleton evaluation,
   induct linearly and use the coefficient at the inverse target.
2. **Syntax/evaluator:** replace blind `ext`/`simp` and the wrong induction
   alternatives with explicit word-dagger involution, nested `Finsupp.sum`
   flattening, `MonoidAlgebra.induction_linear` and the evaluator homomorphism.
3. **Gauge/charge phases:** normalize integer quadratic finite differences
   before `omega`; use complex group-with-zero zpower laws. Inverse shifts
   restore the source before the adjoint phase. Canonical gauges cancel by
   unit modulus, without multiplicativity of the oscillator functional.
4. **Tensor bridge:** enlarge only to the charge/monomial support product,
   factor the finite sum, and extend adjoints using the current
   `TensorProduct.inductionOn`. Forward-reference problems in an earlier
   joint-adjoint body were handled by a local A08 derivation.
5. **Field algebra:** three external commutator attempts failed (output
   exhaustion or nonexistent helper names); independent diagnosis led to
   an explicit local finite orientation instance, `qForm`/bare field
   coefficients, finite-generator kernel sums and A08 CCR. Represented
   commutators collect antisymmetric contraction scalars through `congrArg`;
   direct `smul_sub` matching failed at the final collection step.
6. **Adjoints/variance:** root conjugation also covers `L = 0`, as required
   by the field contract. Preserve the inverse Bogoliubov pullback.
   Extend Hermiticity through powers and real factorial scalars. The variance
   uses the exact root/exponential cosine identity and a `Fin M` to `Icc 1 M`
   bijection, including empty sums at `M = 0`, and yields exactly `4*g_J*D1`.
7. **Weyl proof:** three external attempts at whole-expression unfolding
   failed; a targeted independent diagnosis identified the missing actual
   Cauchy/binomial bridge. The successful local proof uses contextual CCR
   inside arbitrary left/right contexts, a local `RingCon` quotient and an
   **additive** descended functional to justify a binomial identity, without
   asserting literal free-algebra CCR or multiplicativity of `omegaP`.
   Represented adjoint contracts evaluate dagger-exponential coefficients;
   S1 even/odd moments plus variance give the Gaussian coefficient; canonical
   charge restoration and finite multiset Cauchy evaluation supply the phase
   and both normalization factors. Local generic quotient helpers must use
   `A : Type`, not an unbound `Type*` universe in this non-polymorphic theorem.
8. **Lean transparency:** aggressive unfolding of `vertexCoeff` and
   `FormalSeries` inside rewriting produced cached-instance/type mismatches.
   Typed singleton facts, `congrArg`/`calc` equalities and local explicit
   carriers resolved these without changing data, imports or global options.
9. **Normal prefactors:** the pure scalar finite Cauchy-shuffle identity
   has now compiled in scratch with standard axioms only. The remaining
   bridge is the joint functional's scalar bilinearity and multiset expansion,
   then instantiation with the two multiplier series. No partial normal proof
   was integrated into the staging stubs.

## Fresh validation

- `python3 scripts/guards/stub_lock.py --check --strict`: **PASS**, 1,153
  theorem statements and 1,211 frozen non-theorem commands.
- `python3 scripts/guards/core_lock.py`: **PASS**, all 36 frozen Core sources.
- `lake build BosonizeStubs`: **PASS**, exactly two placeholder warnings
  (the normal prefactors), no other warnings. Existing tactic suggestions
  in Core/staging are informational and are not linter suppression.
- Fresh `#print axioms` for **all 37 completed S2 theorem declarations**:
  only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` in these closures.
- Strict/Core manifest SHA-256 respectively:
  `7ab7800ef7fa313ed34b7aac48a08c3c5a7a1e2bda29783edeaf3a85a9539cd1`,
  `cbe522f531b1bb0b0ac6950527b01ca2bfff32976a833c4898b68584f7c280af`.
- S1 ordered-Wick/pairing-combinatorics source SHA-256 respectively:
  `f26d52cb29008f7d39030157368b7b9131bf14a4db173e97ef404062220852a9`,
  `33fefe1fafbdde6c544925a641ac8cdec496ce571f3036558500a53ddb0ddeff`.
- Independent review covers every integrated proof change. Full Phase B still
  requires both prefactors, zero placeholders/warnings, final theorem/closure
  and nonvacuity audits, and final package review. CI/integration, Phase C
  promotion and pedagogical review remain open. No push/publication occurred.
- Unrelated pre-existing tracked/untracked changes were not edited or staged.

## Evidence archive and exact next action

The private, resumable evidence directory is:
`/home/lucas/Projects/.agentctl/sprints/v1-s2-resume-20261017-2318/`.
Its `INDEX.md` distinguishes proved scratch helpers from failed drafts, and
preserves exact API receipts, prompts/replies, compiler diagnostics, complete
source candidates, independent reviews and validation logs. Useful standalone
checked helpers include `Gaussian.lean`, `ContextualBinomial.lean`,
`ContextualCCR.lean`, `OscillatorCoefficient.lean`, `OscillatorCauchy.lean`,
`ChargeCoefficient.lean`, `SeriesCoefficient.lean` and **`ScalarShuffle.lean`**.
These are not additional imported staging declarations.

Before new proof work, verify checkout/HEAD/hash, strict/Core locks, unrelated
changes and live allowance. For the two normal prefactors:

1. Let `S z a = (ChargeWord.scale z a.1, a.2)` and prove locally that
   `jointCoeffFunctional hp N (vertexCoeffMul (S z a) (S w b))`
   equals `z*w` times the unscaled product functional. Use its existing
   charge-expectation/oscillator-product law; do not assume multiplicativity.
2. Extend to multiset coefficients by additivity and finite bind/map sums.
3. Expand the two scalar-scaled series into a triple finite sum. Apply the
   checked `scalar_cauchy_shuffle` to reindex it into the scalar convolution
   of the original correlator with the product of the two multiplier series.
4. Instantiate with `dressedNormalMultiplier`, then `bareNormalMultiplier`,
   and substitute the now-proved `coefficientwise_weyl_correlator_contract`.
   Keep statements/data/imports/headers and all S1/Core sources frozen.
5. Independently review actual new bodies; run the complete Phase B audits.
   Only then enter authorized Phase C promotion and pedagogical review. No S3.

## Allowance checkpoint

At the final reading, the shared five-hour allowance had **8%** remaining
and weekly allowance **70%** remaining. New proof work stopped below the
formalizer guard of 10%/5%, respectively. Recheck live before resuming.
The limiting reset is **2026-10-18 04:18:13 America/Fortaleza**. No reset credit
was spent and no new automatic quota-resumption schedule was created.

Checked scratch scalar-shuffle source SHA-256: `3ce69cd99bfc33cff9d613443f6d133a96b0a194b116377dda3c179e0a01fa16`.
