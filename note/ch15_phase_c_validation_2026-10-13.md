# CH15/A06 Phase C completion — 2026-10-13

Phase C is complete. The existing runner accepted the independently reviewed
five-file Markdown candidate, promoted both modules, migrated the scoped locks,
ran CI and promoted/aggregator axiom audits, merged and pushed finish
`4f526ec138daa0c248a0c583f3b504995960a8ef`. The accepted document candidate is
`23183e7a6f085f2420347d3899f690fae630a54a`.

## Proved and frozen scope

A06 has 16 proved contracts and 13 data declarations; CH15 has seven proved
contracts and two data declarations. Fresh post-promotion audits cover all 38
declarations, with no target warnings/placeholders and only propext,
Classical.choice and Quot.sound. Both modules are accessible through import
Bosonize, as the runner's saved aggregator audit confirms.

The exact import migration expands A06's import Bosonize to the 23 pre-existing
Core imports and changes CH15's A06 import to its Core path. All other source
bytes, definition/statement/proof bodies and theorem-header hashes are preserved.
Only the two selected interface records move with reviewed import/context hashes;
all unrelated records and 23 prior complete Core hashes remain unchanged.
Core now contains 25 modules and 816 proved statement interfaces. Both guards
pass 816 statements, 679 frozen commands and 25 Core hashes. The increase of
22 commands comes solely from expanding one aggregator import to 23 imports.
Toolchain/Lake configuration and dependency manifest remain unchanged.

[Machine-readable preservation evidence](ch15_phase_c_preservation_2026-10-13.json)
records exact promoted hashes, header/non-import preservation and reference-note
prefix hashes. The two promoted hashes are also in the complete-source lock.

## Pedagogical synchronization and independent review

The chapter and appendix retain their complete original reference texts as exact
byte prefixes (6836 and 9599 bytes). Their new mathematical realization sections
explain the finite occupation carrier, actual total-energy joint budget,
qualified current/field actions and margins, orientation and kernel signs,
actual adjoints, periodic differences, and genuine nonzero-ground obstruction.
Canonical-root sine interpretation is distinguished from the arbitrary-root
character theorem. Shared CH16 squares/Hamiltonians/error witnesses and analytic
claims remain preserved but explicitly unformalized.

Independent agent `/root/characters` approved both the exact promotion plan and
all five pedagogical/document artifacts with no required changes. The companion
maps cover every 16+7 declaration and use the promoted source paths and correct
Core-directory link depth. Root reviewed the mathematical prose and validated
195 fragments with strict KaTeX 0.16.22, zero failures. Current status/index edits
only record the accepted completion and do not expand the mathematics.

## Workflow failures resolved before final completion

The first transaction built both promoted modules but correctly withheld
acceptance when two exporter tests read the removed staging A06 path. Reviewed
repair `5b84fab` resolves exactly one staging/Core source, rejects missing or
ambiguous layouts, and preserves frozen inventory/source hash gates. The saved
Phase B API export is historical after promotion. All six exporter tests passed
in both pre- and post-promotion layouts. A fresh packet at `d925947` included
that repair; its acceptance CI passed all 15 Web-LLM tests.

The final primary checkout exposed an absent empty staging directory that the
transaction retained after moving both sources. Tracking BosonizeStubs/.gitkeep
preserves Lake's valid empty staging glob on fresh Git checkouts. No Lean,
toolchain, Lake configuration or lock changes were needed. After this packaging
fix, primary CI passed both builds, 69 guard tests and 15 Web-LLM tests; the
fresh promoted audit passed all 38 declarations. The regression fixture's
intentional sorryAx output is not a target axiom. The old Ch13 ring suggestion
is informational rather than a new compiler warning.

## Final primary compiler and axiom evidence

```text
[core_lock] Verified 25 complete Core source file(s).
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
'Bosonize.Ch15.phi_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.theta_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.phi_self_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.theta_self_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.mixed_commutator_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.mixed_forward_diff_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.zero_mode_obstruction_on_ground' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.phiField' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch15.thetaField' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: 38 freshly built data/theorem declarations
```

## Final primary CI evidence

```text
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.681s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 816 statement(s) and 679 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 25 complete Core source file(s).
== Building Bosonize (Core) ==
ℹ [3403/3410] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Build completed successfully (3410 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3403/3411] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3410/3411] Built BosonizeStubs (2.2s)
Build completed successfully (3411 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
.........[core_lock] Verified 25 complete Core source file(s).
[core_lock] Verified 25 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 15 tests in 17.389s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmpzircglo1/candidate.md; human evidence/prose review still required
CI OK
```

## Saved workflow status

```text
CH15: /home/lucas/Projects/Lean/bosonize-lean
Phase A: not started in this runner
Phase B: finished
  Files: /home/lucas/Projects/.packets/bosonize-lean/ch15
Phase C: finished
  Files: /home/lucas/Projects/.packets/bosonize-lean/ch15
```

Machine layout: docs/webllm/chapters/ch15.json has C_complete, 23 contracts and
no pending modules. Saved cycle C is finished at the accepted promotion commit.
The Phase A runner label reflects its separate earlier artifact integration;
its reviewed baseline evidence is unchanged. The runner's historical Phase C
review artifact records pre-acceptance status and is superseded by this record.
CH16 was not started. No new development beyond the completed A06/CH15 cycle ran.
