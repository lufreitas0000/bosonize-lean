# CH16/A07 A–B–C completion — 2026-10-13

The authorized cycle is complete. Phase A independently reviewed and accepted
19 contracts and 29 data declarations at b56b47c. All six A07 proofs were accepted
and pushed at 46cab18; all thirteen CH16 proofs at 3af7420. The reviewed five-file
Phase C artifact was accepted as 8efc6d5 and exact promotion merged/pushed at
5fbb9bf. This note records fresh final primary-checkout checks rather than merely
relying on a prior candidate or stub build. CH17 has not started.

## Proved scope and proof review

A07FiniteNormalOrdering provides six proofs and 17 data declarations. Its ordered
quadratic coefficient symbols, genuine normal/raw pair evaluation, linearity,
restricted contraction, exact gradient representation and dual-square coefficient
identity are proved. Ch16FieldHamiltonian provides thirteen proofs and 12 data
for the field/chiral identity, exact finite character collapse, factor-four energy,
excursion form, weighted error, ground annihilation, actual excited membership
and nonzeroness, single-mode error eigenvalue, first-mode zero and concrete
algebraic dispersion-gap/nonzero-error witnesses.

The current carrier is finite multispecies occupation Fock space, with ambient
endomorphisms and an actual shared total-excitation budget. No intermediate
projection or global scalar CCR is postulated. The field collapse is derived
as a stronger ordered-symbol identity, while the approved theorem retains its
sufficient budget/margin hypotheses. The eigenvector CCR is applied on the actual
right ground suffix. The first-mode kernel result concerns one excitation;
arbitrary creator-word kernels and full kernel classification remain unproved.
No general positivity, sine equivalence, Taylor estimate, analytic limit or RG
conclusion is claimed by this cycle.

Independent review: root reviewed all six A07 bodies and the spatial-collapse
construction; /root/same_ccr independently reviewed all thirteen CH16 bodies,
explicitly distinguishing its earlier A07 authorship. /root/characters independently
reviewed Phase A, exact promotion and final pedagogical artifacts. Author rechecks
were not counted as independent reviews of their own proof work.

## Exact promotion and preservation

Both import Bosonize lines expand to the 25 prior Core imports; CH16's staging
A07 import becomes its Core path. Every non-import source byte, all mathematical
definitions, theorem headers and proof bodies are unchanged. Only the two
selected interface records move with import/context hashes updated. All unrelated
records and 25 prior complete Core files/hashes remain unchanged. Toolchain,
Lake configuration and dependency manifest are identical to the accepted baseline.

The project now freezes 27 Core modules and 835 proved statement interfaces.
Guards verify 835 statements, 767 frozen commands and 27 Core source hashes.
The 48-command increase from 719 follows the two single aggregator imports becoming
25 imports each. [Machine preservation evidence](ch16_phase_c_preservation_2026-10-13.json)
records exact source hashes, preserved header/data hashes and original note prefixes.

## Pedagogical synchronization

The chapter and shared A06 reference notes retain their complete original byte
prefixes (8965 and 14430 bytes). Added mathematical sections explain the actual
normal-ordering carrier and order, exact finite gradients, no-alias Fourier
pairings, the two factors of two, weighted error, ground and single-mode results,
and genuine algebraic nonzero witness. Earlier proof strategies and broader
reference material remain visible with clear scope/status distinctions.

A07FiniteNormalOrdering supports A06's normal-ordering section; it does not
implement the separately numbered A07 interactions appendix. Companions map all
six plus thirteen declarations and resolve links at their promoted Core depth.
Independent pedagogical review found one stale checkpoint link, corrected and
re-reviewed; an unsupported historical numerical-proof phrase was removed.
Final verdict PASS. Strict KaTeX 0.16.22 validates 248 mathematical fragments
with zero failures. Status updates after acceptance do not change the mathematics.

## Fresh final evidence

Primary make ci passed both Core/staging builds, 69 guard tests and 15 verifier
regression tests. The fresh promoted audit passed all 48 proof/data declarations
with only propext, Classical.choice and Quot.sound, no target warnings,
placeholders or sorryAx. The runner also passed fresh Core-aggregator access
and axiom checks during promotion. The regression fixture's intentional sorryAx
output is a negative test, not a target dependency; the existing Ch13 ring
suggestion is informational. No diagnostic suppression or forbidden tactic was
introduced. Both guards are verified again against the final committed reference.

The saved chapter layout is C_complete with 19 contracts and no pending modules.
The external cycle reports A, B, C finished. The earlier quota checkpoint and
candidate archive are retained as historical development evidence, superseded
by this completion record. No reset credits were used.

### Final promoted axiom output

```text
[core_lock] Verified 27 complete Core source file(s).
ℹ [3403/3410] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Build completed successfully (3410 jobs).
'Bosonize.A07.normal_evaluation_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.normal_evaluation_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.normal_pair_contraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.contraction_on_joint_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.chiral_gradient_representation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.dual_square_chiral_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.Letter' does not depend on any axioms
'Bosonize.A07.QuadraticSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.orientation' does not depend on any axioms
'Bosonize.A07.natMode' does not depend on any axioms
'Bosonize.A07.phaseSign' does not depend on any axioms
'Bosonize.A07.signedMode' does not depend on any axioms
'Bosonize.A07.current' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.rawPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.normalPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.rawEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.normalEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.squareSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.gradientCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.chiralCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.phiCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.thetaCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07.dualSquareSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.field_chiral_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.chiral_spatial_collapse_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.field_weighted_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.field_weighted_after_excursion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.error_weighted_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.ground_error_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.excited_ket_mem_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.excited_ket_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.single_mode_error_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.first_mode_error_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.error_nonzero_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.concrete_dispersion_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.concrete_excited_error_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.marginWithExcursion' depends on axioms: [propext]
'Bosonize.Ch16.chiralSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.localFieldEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.fieldHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.epsilon' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.referenceWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.sugawara' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.weightedEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.weightedError' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.errorOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.excitedKet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch16.standardBranches' depends on axioms: [propext]
PASS: 48 freshly built data/theorem declarations
```

### Final primary CI output

```text
./scripts/ci.sh
== Testing the statement-freeze guard ==
.....................................................................
----------------------------------------------------------------------
Ran 69 tests in 1.739s

OK
== Checking frozen chapter definitions and statements ==
[stub_lock] Verification PASSED: 835 statement(s) and 767 frozen command(s) verified.
== Checking complete frozen Core sources ==
[core_lock] Verified 27 complete Core source file(s).
== Building Bosonize (Core) ==
ℹ [3403/3412] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3409/3412] Built Bosonize.Core.A07FiniteNormalOrdering (3.9s)
✔ [3410/3412] Built Bosonize.Core.Ch16FieldHamiltonian (8.0s)
✔ [3411/3412] Built Bosonize (2.7s)
Build completed successfully (3412 jobs).
== Building BosonizeStubs (Staging) ==
ℹ [3403/3413] Replayed Bosonize.Core.Ch13KleinFactors
info: Bosonize/Core/Ch13KleinFactors.lean:228:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
✔ [3412/3413] Built BosonizeStubs (2.9s)
Build completed successfully (3413 jobs).
== Testing the Web-LLM artifact/proof verifiers and axiom audit ==
.........[core_lock] Verified 27 complete Core source file(s).
[core_lock] Verified 27 complete Core source file(s).
......
----------------------------------------------------------------------
Ran 15 tests in 18.499s

OK
'Fixture.value' depends on axioms: [sorryAx]
PASS Markdown structure: /tmp/tmp49dqvtj5/candidate.md; human evidence/prose review still required
CI OK
```

### Final workflow output

```text
CH16: /home/lucas/Projects/Lean/bosonize-lean
Phase A: finished
  Files: /home/lucas/Projects/.packets/bosonize-lean/ch16
Phase B: finished
  Files: /home/lucas/Projects/.packets/bosonize-lean/ch16
Phase C: finished
  Files: /home/lucas/Projects/.packets/bosonize-lean/ch16
```
