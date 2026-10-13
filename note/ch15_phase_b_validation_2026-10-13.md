# A06/CH15 local Phase B proof review — 2026-10-13

Scope: only the reviewed 16 A06 and seven CH15 obligations; no Phase C,
Core promotion, pedagogical synchronization, or CH16. Original packet baseline:
`cbee7697a3d0866c18bb89f466967e4ff089205e`.

## A06 browser proof disposition

Adopted selectively from iteration 3, then freshly recompiled: character
conjugation, integer periodic lift, forward-difference addition/scalar/zero-sum,
cross-species field commutation, Dirichlet diagonal, skew-kernel difference
zero-sum, admissible nonzero ground, and the concrete two-branch witness.

Adapted: character shift with explicit `Int.cast_one`; true adjoint via the
conjugate-linear equivalence and installed `star_div₀`, complex conjugation of I,
and natural casts; the exact difference body after proving its shift dependency;
Dirichlet spatial sum with a separately typed natural absolute-value bound and
integer divisibility equality.

Adapted tensor architecture: occupation-ket span induction, nonnegative species
energies bounded by total excitation, single-species CCR, and a proved linear
insertion map transporting both ordered current products. A transparent local
eta-expanded equality instance matches the captured A05 context; scalar span
induction uses explicit rewrites rather than recursive scalar simp.

Replaced the browser same-branch automation with an explicit four-pair operator
bilinearity identity before current substitutions, diagonal/off-diagonal scalar
normalization, `sum_eq_single` diagonal collapse, and a residue-character bridge
for integer representative differences. Kept -m, rightmost-first order, original
uniform margin, orientation, x-y and all normalizations.

Rejected: whole failed browser candidates as completed proofs, guessed adjoint
helpers, unqualified `star_I`, opaque instance replacements, direct representative
subtraction without the residue bridge, and the misplaced no-alias equality
inside an inequality proof. Historical recovery `sorryAx` never counts as evidence.

Fresh A06 gate: `make lock-check` and `make verify-b
TARGETS="BosonizeStubs/A06ChiralFields.lean"` passed. All 29 named declarations
(16 proofs and 13 data) have only standard axioms; no placeholders or warnings.
Independent final source review by `/root/characters` passed frozen fidelity,
mathematical signs, margins, tensor transport, normalization and nonzero witnesses.

A06 runner acceptance: candidate `b2030868a8b64a305bda64e9bfb410b0d4ae38b7`, finish `35b7f93`; CI passed and commits merged/pushed. CH15 candidate `6cba91cd580abc52d44c714663df5509ad6f354e`, finish `93c14d8`; CI passed and commits merged/pushed. Both acceptances used the existing runner from the clean primary, with packet identity read programmatically from each active manifest.

## CH15 construction and review

New CH15 packet baseline after accepted A06:
`23958251d2d20c4fb5148f8b9ffcba7ca8a82b2b`.
Adjoints use the actual semilinear map's add/sub laws. Self and mixed brackets
use explicit four-term bilinearity, reverse cross commutation, and both chiral
identities on the same budget input. Their coefficients are respectively zero,
zero and exactly `2 * skewKernel`. The forward difference subtracts the mixed
identity at y from the identity at y+1 without changing operator order.

The zero-mode proof directly sums the action-valued commutator difference to
zero, sums the assumed Dirichlet expression to `c • groundKet`, and contradicts
this with c nonzero and A05's genuine nonzero ground ket. All frozen assumptions
remain, including those stronger than this periodic obstruction requires.
No source-level hypothesis cleanup, new top-level helpers, or imports were needed.

Fresh candidate `make lock-check` and `make verify-b
TARGETS="BosonizeStubs/Ch15DualFields.lean"` passed: the dependency A06 has 29
and CH15 has nine freshly audited declarations, all standard axioms only.
Independent final integrated review by `/root/characters` passes all seven
proof bodies, frozen fidelity, signs, shared inputs, margins, difference
orientation and nonzero-ground contradiction.


## Final primary-checkout verification

Fresh combined `make verify-b TARGETS="BosonizeStubs/A06ChiralFields.lean
BosonizeStubs/Ch15DualFields.lean"` passed on accepted finish `93c14d8`.
A06: 16/16 proofs and 13 data declarations; CH15: 7/7 proofs and two data
declarations. All 38 declarations are freshly compiled and axiom audited using
Lean `v4.35.0-rc4`; Mathlib revision
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6` is unchanged. Every reported axiom
is one of `propext`, `Classical.choice`, `Quot.sound`. No target warnings,
placeholders, recovery axioms, or linter suppression remain.

`make ci` passed: 69 guard tests, strict interface and Core verification,
Core build (3408 jobs), staging build (3411 jobs), and 14 Web-LLM verifier
regression tests. The deliberate `Fixture.value` sorryAx message in the
regression-test output is a negative test fixture; it is not a target axiom.
The existing Ch13 ring tactic suggestion is informational, not a new warning.

`make lean-status 15` reports Phase B finished and Phase C not started.
`docs/webllm/chapters/ch15.json` records `B_complete`, 23 theorem contracts,
and no pending modules. The saved cycle B is finished with `phase_complete=true`.
The runner's Phase A label says not started in this runner because reviewed
Phase A was integrated through the earlier artifact workflow; this does not
replace that separate accepted/reviewed Phase A evidence.

Original source notes, all 23 Core sources, both lock manifests, toolchain,
Lake configuration/manifest and both aggregators are byte-identical to the
original `cbee7697a3d0866c18bb89f466967e4ff089205e` baseline. The strict locks
still verify 816 statements and 657 frozen commands. Supplementary documentation
is committed separately after both runner acceptances; no packet baseline was
changed during proof acceptance.

Stopped at Phase B. No promotion, source-note synchronization or CH16 work ran.

## Saved final compiler/axiom output

```text
[stub_lock] Verification PASSED: 816 statement(s) and 657 frozen command(s) verified.
[core_lock] Verified 23 complete Core source file(s).
ℹ [3403/3408] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Build completed successfully (3408 jobs).
'Bosonize.A06.lattice_character_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.lattice_character_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.integer_lift_periodic' depends on axioms: [propext, Quot.sound]
'Bosonize.A06.forward_diff_add' depends on axioms: [propext, Quot.sound]
'Bosonize.A06.forward_diff_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.forward_diff_sum_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.chiral_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.chiral_forward_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.joint_signed_current_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.chiral_cross_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.chiral_same_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.dirichlet_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.dirichlet_spatial_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.skew_kernel_diff_sum_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.admissible_ground_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.concrete_two_branch_parameters' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.Orientation' does not depend on any axioms
'Bosonize.A06.orientationSign' does not depend on any axioms
'Bosonize.A06.Branches' does not depend on any axioms
'Bosonize.A06.speciesOf' does not depend on any axioms
'Bosonize.A06.marginAt' depends on axioms: [propext]
'Bosonize.A06.branchMargins' depends on axioms: [propext]
'Bosonize.A06.latticeCharacter' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.skewKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.dirichletKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.opForwardDiff' depends on axioms: [propext, Quot.sound]
'Bosonize.A06.integerLift' depends on axioms: [propext, Quot.sound]
'Bosonize.A06.chiralField' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A06.chiralDifferenceExpansion' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: BosonizeStubs/A06ChiralFields.lean, 29 freshly audited declarations
'Bosonize.Ch15.phi_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.theta_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.phi_self_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.theta_self_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.mixed_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.mixed_forward_diff_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.zero_mode_obstruction_on_ground' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.phiField' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.thetaField' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: BosonizeStubs/Ch15DualFields.lean, 9 freshly audited declarations
```

## Saved final CI output

```text
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.703s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 816 statement(s) and 657 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 23 complete Core source file(s).
== Building Bosonize (Core) ==
ℹ [3403/3408] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Build completed successfully (3408 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3403/3411] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3408/3411] Built BosonizeStubs.A06ChiralFields (10s)
✔ [3409/3411] Built BosonizeStubs.Ch15DualFields (3.0s)
✔ [3410/3411] Built BosonizeStubs (2.4s)
Build completed successfully (3411 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
........[core_lock] Verified 23 complete Core source file(s).
[core_lock] Verified 23 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 14 tests in 16.893s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmpkw75mpcb/candidate.md; human evidence/prose review still required
CI OK
```

## Saved final workflow output

```text
CH15: /home/lucas/Projects/Lean/bosonize-lean
Phase A: not started in this runner
Phase B: finished
  Files: /home/lucas/Projects/.packets/bosonize-lean/ch15
Phase C: not started in this runner
```
