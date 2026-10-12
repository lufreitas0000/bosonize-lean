# CH14 / A05 integrated Phase B independent review — PASS

Reviewer: `/root/ch14_review`. Exact reviewed sources:

- `BosonizeStubs/A05FiniteExponentials.lean`: SHA-256 `57d36818adb50f3f981c14191e786efce2d9d1eed872313110f9dd00a392aee5`.
- `BosonizeStubs/Ch14Mandelstam.lean`: SHA-256 `ef78dbd4c20ca8b853ae44b123ef9f69932442e4f2b005ea32eca4fe6a4dac83`.

## Independence and covered proofs

This reviewer independently inspected the thirteen generic A05 proofs, twelve CH14 phase/holonomy proofs, and four actual nilpotency proofs (29 author-distinct proofs). The reviewer authored the other eight CH14 criterion, projection/adjoint, occupation/ground-expansion and residual proofs during Phase B; those eight were independently reviewed by the root orchestrator and are explicitly excluded from this reviewer's self-certification. The root reported their author-distinct PASS before this final review. All 37 proofs are included in the fresh compiler/axiom checks regardless of authorship.

## Mathematical review

The generic polynomial uses its actual complex-module endomorphism. Intertwining respects source/target types. Cutoff independence factors higher powers through the supplied zero power. Inverse proofs bridge actual rational factorial coefficients to the library nilpotent exponential and use actual power-zero premises; injectivity, surjectivity and nonzero preservation follow from both inverse directions. Adjoint compatibility conjugates real factorial coefficients. The filtration theorem iterates the explicit lowering contract to the zero bottom, with the whole actual module as top.

The root's ambient compressed lowering proof correctly includes vectors outside the budget: its exceptional top is the whole ambient module, and the first application projects into budget K before lowering. Subsequent levels are the actual signed species budgets; the coordinate projector preserves every smaller grade, and each strictly positive mode lowers excitation by at least one. The K=0 and bottom branches use the proved negative-budget theorem. No R2 or charge-admissibility assumption is needed for nonnegative excitation and strict lowering. No replacement carrier or unproved grading premise appears.

Raising nilpotency follows from actual self-adjoint coordinate projections, W+ adjoint equal to minus W-, and the star of the proved lowering power. Cancellation uses the unit (-1)^(K+1), which remains valid even when the endomorphism ring is trivial. Subtype nilpotency is transferred through pointwise projection fixedness and an actual power-action induction, rather than inferred from finite dimension.

The twelve phase proofs retain canonical-root character hypotheses, complex conjugation, positive mode weights, raising minus sign and integer lifts. Zero-mode unitarity uses the actual unit-modulus scalar in both orders. Klein-ground reproduction retains the source phase and pairMargin. Physical and candidate winding retain exactly the external species holonomy. These statements do not establish unconditional finite field–vertex equality; full ground agreement, cyclicity and common residual recurrences remain explicit hypotheses of the accepted conditional criterion.

## Fresh independent validation

Independent direct source checks with `-DwarningAsError=true` passed both modules, with zero warnings, errors and placeholders. Fresh audits cover all 57 declarations: 37 complete theorems and 20 complete data/instance declarations. Every dependency is among `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. Machine-readable declaration lists and exact source provenance are in `note/ch14_phase_b_independent_audit_2026-10-12.json`.

Native Lean MCP diagnostics completed for both actual staging files with success, empty diagnostics, no partial result, no timeout and no failed dependencies. A native goal query at CH14 line 315 showed the actual compressed power-zero goal turning into the three precisely typed filtration obligations (bottom, top, lowering). This confirms native goal access alongside compiler verification, not a replacement for the latter.

The integrated Phase B proofs pass independent review with no unresolved mathematical findings. Phase C may proceed after the orchestrator's strict guards/build checks and complementary documentation gates. Existing Core remains immutable; migration import substitution must receive its own scoped check.
