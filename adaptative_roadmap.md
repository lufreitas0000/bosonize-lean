# Adaptive roadmap and Kanban pipeline

Updated: 2026-10-10. This is the overall project pipeline; it does not replace the A–B–C process inside each chapter. Follow the [formalizer skill](.agents/skills/formalizer/SKILL.md), [chapter drafting](.agents/workflows/start_chapter.md), [interface lock](.agents/workflows/lock_stub.md), and [promotion](.agents/workflows/freeze_chapter.md) procedures.

## Baseline and mathematical scope

Chapters 1–9, CH06Ext, A01/A03, finite-CAR A02 and the density-kinematics portion of A04 are proved and frozen in Core (579 theorems across fourteen modules). The 21 chapter notes, A01–A10, and proof suggestions have a reconciled source baseline described in [the completion ledger](note/notes_review_completion_2026-10-09.md). Source-checking completion is not a Lean proof of later chapters or a guarantee that proof development will discover no further errors.

Use exact finite-dimensional, polynomial, and explicitly specified algebraic constructions. Keep the finite CAR model separate from the uncompressed CCR/charge model and its coefficientwise series vertices. No analytic limit or formal substitution t=1 is implicit. Numerical-margin-only finite Mattis–Mandelstam equality remains a research candidate; the approved Chapter 14 target is the conditional cyclic-span criterion. Compactification, thermodynamic gaps, and new non-Abelian or refermionization programs belong to an optional research backlog with their own reviewed scope.

## Kanban board and work in progress

The board is a Markdown status table, maintained in this file. A card is a chapter, a supporting lemma package, or a dedicated issue sprint. Record owner, dependencies, current phase, evidence/commit, next action, and blockers. A board is coordination documentation; it does not implement an autonomous scheduler or authorize agents to create tasks or contact other threads.

| Column | Entry and exit rule | Work-in-progress policy |
| --- | --- | --- |
| Backlog | Named goal, source references and dependencies; no promise that its original claim is true. | Ordered by dependency and impact. |
| Ready | Dependencies available; scope, carrier, target and acceptance criteria agreed. | Keep a small queue; start only authorized work. |
| Active A/B/C | Execute one chapter's current phase and record its exact gate. | One primary chapter at a time; independent read-only/helper subtasks may run within authorized scope. |
| Review | Concrete signatures/correction ready for independent agent review; unresolved ambiguity goes to the human. | Record reviewer identity, exact source hash, findings/resolution and pass/revise/escalate verdict. |
| Blocked / issue sprint | Explain the exact obstruction, affected files, checkpoint and resume condition. | Halt affected implementation; continue independent authorized work. |
| Done | Completed artifact and passing evidence committed; phase completion is distinguished from chapter completion. | A chapter is Done only after Phase C. |

Current board snapshot:

| Card | State | Phase | Dependencies / evidence | Next action |
| --- | --- | --- | --- | --- |
| CH01 — Lattice/band | Done | C complete | Frozen Core; direct compile and 20-lemma axiom audit passed. | Reuse positive Nyquist and existing band projection. |
| CH02 — Umbral operators | Done | C complete | Frozen Core; direct compile and 32-lemma axiom audit passed. | Reuse bundled periodic shifts/differences. |
| DOC — Source/suggestion reconciliation | Done | Documentation checkpoint | [Completion ledger](note/notes_review_completion_2026-10-09.md). | Reopen a specific card if compiler or proof evidence reveals an error. |
| CH03/A01 — Fourier | Done | C complete | Approved interface `73add90`; Phase B `40ff996`; 61 lemmas promoted into Core, fresh warning-free compile, 113-lemma Core axiom audit, native MCP diagnostics/goals, 69 guard tests and both builds passed; [A01 notebook](docs/companion/Bosonize/Core/A01FourierCharacters.md), [CH03 notebook](docs/companion/Bosonize/Core/Ch03Fourier.md). | Reuse frozen characters, normalization and Fourier transport; use the promotion commit as the next lock baseline. |
| CH04/A02 — Finite CAR and Fock carrier | Done | C complete | Initial interface `7a2da78`; reviewed cleanup `ddf9548`; 69 lemmas promoted into Core; fresh warning-free compile, 182-lemma Core axiom audit, native MCP diagnostics/goals, 69 guard tests, both guards and both builds passed. [A02 notebook](docs/companion/Bosonize/Core/A02CARHilbert.md), [CH04 notebook](docs/companion/Bosonize/Core/Ch04CARFock.md). | Reuse frozen basis/CAR/adjoints, number/parity and bilinears; use the promotion checkpoint as the current lock baseline. |
| CH05 — Lattice fermions | Done | C complete | Phase B `0abdb37`; 35 proved lemmas promoted and completely frozen; unchanged source bytes, fresh warning-free compilation, Core axiom audit and CI passed; [CH05 notebook](docs/companion/Bosonize/Core/Ch05Fermions.md). | Reuse Fourier CAR/inversion, parity, integer energies and sea witnesses; use the promotion checkpoint as the baseline. |
| CH06 — Local CAR net | Done | C complete | 54 proved lemmas promoted and completely frozen; only CH05 dependency import/context changed; locality and ordered matrix-unit/fullness proofs, native MCP checks and 271-lemma Core audit passed; [CH06 notebook](docs/companion/Bosonize/Core/Ch06LocalNet.md). | Reuse finite graded local net and global endomorphism algebra; review the new CH07/A03 Phase A interface. |
| CH06Ext — Boundary holonomy and transport | Done | C complete; frozen | 72 theorem proofs and 29 data declarations; corrected interface at `1a562b7`, Core source hash and [notebook](docs/companion/Bosonize/Core/Ch06Ext.md). | Reuse twisted fields/transport and the same-sea energy bridge in later chapters; review A03/CH07 next. |
| CH07/A03 — Sea and budgets | Done | C complete; frozen | 114 theorem proofs and 45 data declarations promoted to Core; interface `20ed09b`, Phase B `2b3186f`, imported through Bosonize. [A03 notebook](docs/companion/Bosonize/Core/A03EnergyBudgets.md), [CH07 notebook](docs/companion/Bosonize/Core/Ch07VacuumBudget.md). | Review CH08 Phase A: weighted oscillator constructions, grading and explicit finite-slice projection remainders; defer A04 to CH09–CH12. |
| CH08 — Algebraic boson Fock layer | Done | C complete; frozen | 62 proved theorem targets/43 data declarations; fresh standard-axiom audits, zero warnings/placeholders, 69 guard tests and both builds passed. Core now has 519 proved theorems in twelve modules. [Formal notebook](docs/companion/Bosonize/Core/Ch08Boson.md), [constructive lecture](notes/md/ch08_boson.md); independent pedagogical review passes. | Next scoped sprint: CH09 and the relevant A04 density support; prove the actual twisted-fermion density dictionary and admissible current margins before comparison with CH08. |
| CH09/A04 — Density kinematics | Done | C complete; frozen | 60 theorem proofs/21 data declarations; interface `e78c2d9`, proofs `918d145`; complete standard-axiom audits, zero warnings/placeholders, native MCP, 69 guard tests and both builds pass. [CH09 companion](docs/companion/Bosonize/Core/Ch09DensityModes.md), [A04 companion](docs/companion/Bosonize/Core/A04DensityKinematics.md); both complementary lecture updates independently reviewed. Core has 579 proved theorems in fourteen modules. | Next: CH10 restricted current relations with A04 edge action and verified right-suffix margins; then CH11 partitions/Gram/completeness and CH12 Sugawara. |
| CH10/A04 — Restricted current action | Done | C complete; frozen | 37 complete theorem proofs and six definitions; fresh standard-axiom Core audit, warning-free builds, 69 guard tests and independent pedagogical review PASS. Core now has 616 proved theorems in sixteen modules. [Review](note/ch10_phase_a_review_2026-10-10.md). | Reuse frozen restricted current action and right-suffix margins in CH11/CH12. |
| CH11/A04 — Partition counting and Haldane completeness | Done | C complete; frozen | 61 proved targets/15 complete data; interfaces `c788bb3`, proofs `0ae13df`, reviewed recurrence cleanup `ed3ad48`. Fresh 76-declaration standard-axiom audit, zero warnings/placeholders, both builds, 69 guard tests and independent lecture review PASS. [Validation](note/ch11_phase_c_validation_2026-10-11.md). | Reuse the explicit inverse and actual-density partition/budget bases. |
| CH12/A04 — Sugawara energy equivalence | Done | C complete; frozen | 26 complete proofs/5 data declarations, interface `f631d5b`, proofs `3019689`; fresh standard-axiom audits, warning-free builds and independent lecture review. Core now has 703 proved statements in nineteen modules. [Companion](docs/companion/Bosonize/Core/Ch12Sugawara.md). | Next: CH13 with relevant A05 typed Klein/sector support, preserving species twists and exact source/target budgets. |
| CH13/A05 — Joint species and Klein maps | Done | C complete; frozen | 53 complete theorem proofs,42 data constants; fresh standard-axiom audits, warning-free CI and independently reviewed lectures;21 Core modules/756 proved statements. [Review](note/ch13_phase_a_review_2026-10-11.md). | Next CH14/A05 conditional field support; preserve explicit twists, source/target budgets and residuals. |
| CH14/A05 — Conditional field criterion and finite exponentials | Done | C complete; frozen | 37 proofs and 20 data declarations; actual phase nilpotency, typed adjoints, holonomy, full ground expansion and cyclic comparison criterion. Independent lecture review passes. | Keep unconditional physical field–vertex comparison outside the verified claim. |
| CH15/A06 — Dual fields and lattice kernels | Done | C complete; frozen | 23 proved contracts and 15 data declarations; exact source/import migration, independent pedagogical review, fresh standard-axiom audits and CI pass. All 23 prior Core sources remain unchanged; Core now has 25 modules and 816 statements. [Validation](note/ch15_phase_c_validation_2026-10-13.md). | Reuse the frozen finite kernels and qualified actions; CH16/A07 completed its separately authorized A–B–C cycle; see the next card. |
| CH16/A07 — Normal ordering and field energy | Done | C complete; frozen | 19 proofs and 29 data declarations; exact symbol/Fourier collapse, factor-four energy, qualified errors and nonzero single-excitation witnesses. Independent reviews, fresh standard-axiom audits and CI pass; prior 25 Core sources unchanged. [Validation](note/ch16_phase_c_validation_2026-10-13.md). | Reuse the frozen finite results; CH17 remains unstarted and requires a separately authorized scope. |
| CH17–CH19/A07–A08 — Interactions, Bogoliubov, states | Backlog | A not started | Exact sea-Wick Q correction; pairing model; weighted polynomial state. | Review finite-action and uncompressed-state interfaces separately. |
| CH20–CH21/A09–A10 — Formal vertices, duality, spin, leakage, SW | Backlog | A not started | Constructed states, charge maps, projection residuals and coefficient calculus. | Implement exact algebraic targets; keep analytic interpretations separate. |

A support appendix is read and implemented as needed alongside its dependent chapter; implementing every appendix before Fourier is unnecessary. Dates are review points, not promises about proof-search duration. Limit a sprint by an explicit goal and stopping condition; reassess at each completed chapter or issue resolution.

Revisiting unusual or redundant assumptions is a healthy, expected part of proof development. Check necessity, satisfiability and downstream use; propose concrete corrections when evidence supports them. Independently review exact active-staging interface corrections, preserve unrelated lock records, and repeat compiler and axiom checks. Ask the human for substantive ambiguity; existing Core remains immutable.

## The chapter A–B–C cycle

The user adopted the [automatic pipeline](.agents/skills/formalizer/references/pipeline.md) on 2026-10-09. Chapter development advances through A–B–C without routine confirmation. Another agent reviews Phase A and staging-interface amendments; the human decides only substantive ambiguity. Explicit phase-only/stop requests override the default. This changes the review/transition policy, not the mathematical validation criteria or chapter scope, and does not implement a background scheduler.

**Phase A — Draft, document and independently review.** Construct complete data and one-sorry theorem stubs, reconcile current sources/APIs, mirror the exact notebook, and validate elaboration/data axioms/preservation. A different agent reviews carriers, hypotheses, signs, margins, witnesses, compression and downstream contracts. Resolve deterministic findings, re-review changes, and record the final source hash, reviewer and verdict.

**Gate A→B.** A passing independent review plus Phase A evidence authorizes a scoped lock and committed baseline under the user's standing policy. Verify guards against that commit and proceed to proof work. A guard match is syntax preservation, not a mathematical review. Do not lock unrelated drafts or overwrite unexplained drift.

**Phase B — Prove and troubleshoot.** Replace reviewed proof bodies and preserve the locked interface. New helpers or unambiguous interface corrections need an exact diff and independent review before scoped baseline amendment. After three failures on an unchanged goal, get another agent's decomposition/diagnosis before trying a materially different approach. Ask the human only when a mathematical or scope choice remains ambiguous; report technical blockers without pretending completion.

**Gate B→C and Phase C — Audit, promote and freeze.** Require complete proofs, zero warnings/placeholders, fresh axiom audits and passing guards/builds, then promote and freeze in Core. Proceed automatically within authorized scope, with source/notebook coherence and standard-axiom evidence. Migrate reviewed sources/notebooks/aggregators, preserve old Core hashes, run CI and audit through Core. Update the corresponding pedagogical chapter/appendix note using [pedagogical-sync](.agents/skills/pedagogical-sync/SKILL.md), retaining reference theory and adding the actual verified constructive explanation in natural mathematical language. Require independent review of the note, then commit and verify the code, companion and pedagogical checkpoint. Never silently rewrite existing Core or start an unauthorized next chapter.

## Discovery triage: local repair or dedicated issue sprint

A local tactic/API mistake, small proof decomposition, or clarification confined to one unlocked chapter stays on that chapter's card. Fix it, verify it, and update its notebook. If a local correction changes a locked interface, halt the dependent proof and use the existing interface-review gate even if it does not need a sprint.

Open a **dedicated issue sprint** when evidence shows a shared mathematical or interface issue affecting multiple notes/files or downstream contracts: a counterexample to a reused theorem, incompatible carrier/adjoint conventions, insufficient shared margin, missing state existence, or a main statement whose strategy fails because essential mathematics is absent. Routine tactic failures and timeouts do not demonstrate such an issue.

1. **Halt affected work and checkpoint.** Preserve completed proofs, capture the failing goal/counterexample, source versions, current locks and Git status. Do not keep proving downstream statements that rely on the disputed result or repair Core by weakening it.
2. **Create an issue card and note.** Use `note/issue_<id>_<topic>.md` with the suspected false/missing contract, exact evidence, affected chapters/appendices/suggestions/companions, dependency impact, alternative repairs, proposed lemmas and resume conditions. No issue file is created for a merely hypothetical problem.
3. **Run the focused sprint.** Validate the smallest witness or obstruction and prepare exact correction alternatives with explicit hypotheses and downstream impact. Apply source-determined, unambiguous corrections within authorized scope and independently review them. If the correction requires choosing between mathematical/physical interpretations, keep alternatives in the issue proposal and ask the user before adopting either as the source baseline. Independent authorized work may continue outside the affected dependency closure.
4. **Review interface impact.** A note correction does not by itself authorize changing a locked Lean statement. Record the exact proposed interface migration and obtain independent review under the pipeline; unresolved mathematical/scope ambiguity requires the user's decision. Preserve old evidence. A correction involving immutable Core needs a separately reviewed superseding/versioned design, never an overwritten hash.
5. **Verify and close.** Check links and source consistency, elaborate revised definitions, check nonvacuity and the relevant witnesses, run affected builds/guards, and commit the correction. Resolve any changed frozen interface through its approved baseline procedure. Mark the issue resolved with evidence and record which downstream cards are ready again.
6. **Resume the right phase.** Resume B if statements stayed identical; return the affected chapter to A review if interfaces changed. Do not promote an incomplete chapter just to close the sprint.

If no supported repair exists, retain a research/blocked card, remove the unsupported claim from the unconditional implementation queue, and propose the precise narrower result. Clearly distinguish a changed theorem/model from a proof of the original target.

Issue/card template:

```text
ID / owner / status / chapter phase:
Target and current source references:
Dependencies and affected files:
Evidence / counterexample / compiler goal:
Local or cross-chapter classification and reason:
Proposed correction and helper lemmas:
Review or lock impact:
Acceptance checks and resume condition:
Checkpoint / resolution commit:
Next action:
```

## Fourier completion checkpoint

The user approved Phase C for both A01 and CH03 on 2026-10-09. Their 61 lemmas are now in Core, exposed through `import Bosonize`. All 113 Core lemmas pass a fresh standard-axiom audit; the two promoted sources compile with warnings treated as errors. Both guards, 69 regression tests and both library builds pass. CH01/CH02 complete-source hashes are unchanged. A01's lock entry moves unchanged; CH03's only command change is its A01 import path, with the dependent context hashes updated. Use the committed promotion checkpoint for subsequent committed-baseline checks; retain `73add90` as historical interface evidence.

## Completed sprint: CH04 and finite-CAR A02 support

**Status:** Phase A was reviewed and the user authorized Phase B on 2026-10-09. Initial locking committed the exact two interfaces at `7a2da78`, preserving every previous lock entry. All 69 lemmas are now proved and standard-axiom audited; strict guards and CI pass. Both modules compile without warnings. The user approved removing redundant `[Fintype ι]` instances from 14 count/sign theorem headers; that exact cleanup and only its affected lock records are now applied and revalidated. This local cleanup leaves definitions, proof bodies and mathematical conclusions unchanged. The user subsequently authorized Phase C. Both modules are now promoted and frozen in Core; the fresh audit covers all 182 Core lemmas, and warning-as-error compilation, native MCP diagnostics/goals, guards, 69 tests and both builds pass. A02 moves unchanged; CH04 changes only its A02 import path and dependent lock context hashes. Use the committed promotion checkpoint for current baseline checks. One formalizer performed the proof work; no additional agents were used. The numbered plan below records the original design and implemented proof order.

**Read and reconcile:** [CH04](notes/md/ch04_CAR_Fock_space.md), [A02](notes/appendices/a02_car_hilbert_and_normal_ordering.md), the [source audit](docs/audit/reference_notes_lean_audit.md), and the source completion ledger. Check actual installed Mathlib signatures before freezing anything. The numbered plan below is the historical design; the linked notebooks contain the current proved and frozen sources.

1. **A02 finite Hilbert infrastructure.** Draft `BosonizeStubs/A02CARHilbert.lean` with a finite linearly ordered mode type `ι`, occupation configurations `Finset ι`, `EuclideanSpace ℂ (Finset ι)`, and its canonical orthonormal basis. Provide coordinate/basis transport and extensionality contracts. Use one Euclidean inner product and actual finite-dimensional Hilbert adjoints throughout. Check the empty mode set: its Fock space still has the empty occupation basis vector.
2. **CH04 signs and operators.** Draft `BosonizeStubs/Ch04CARFock.lean`. Define preceding count `(S.filter (· < i)).card`, sign `(-1 : ℂ)^count`, and creation/annihilation by occupation-basis extension. Use `Module.Basis.constr` to construct maps. Draft exact basis action, nonzero-action witnesses, insertion count, additive erasure count, sign square, and distinct-mode sign identities. Fixed ordering is explicit; no truncated natural subtraction is assumed reversible.
3. **Concrete CAR and adjoints.** Draft all three anticommutator identities and actual adjoint compatibility. Package the representation only after these proofs are available in Phase B. Prove map identities by occupation-basis extensionality; split coincident/distinct modes and occupied/empty cases. Establish adjointness on basis pairs and extend via finite sums.
4. **Number, parity and bilinears.** Define mode number, total number and parity as an explicitly ordered product. Draft diagonal occupation action, idempotency, self-adjointness, number commutativity, parity basis action/square/adjoint, and reusable bilinear and number commutators. Keep noncommutative factor order explicit; do not use symmetric swap rules as unconditional simp rewrites.
5. **Phase A acceptance and review.** All definitions and instances must elaborate without placeholders; each proposed theorem has exactly one `:= by sorry`. Create mirrored notebooks with exact sources, assumptions, helper dependencies, witnesses, adopted/rejected suggestions and proof order. Run both existing Core/interface guards and the appropriate staging builds, reporting expected stub warnings separately. Present concrete signatures for approval; establish and commit the reviewed baseline before Phase B. If the current strict guard flags the new unlocked files, record those expected additions rather than weakening the guard or updating the manifest before approval.
6. **Later Phase B/C.** Prove basis actions and sign arithmetic first, then CAR/adjoints, number/parity and bilinears. Require nonvacuous witnesses (e.g. creation on the empty occupation), fresh standard-axiom audit, zero placeholders/warnings and strict lock checks before separately authorized promotion.

**Scope boundary:** A02's polynomial Hermitian forms, normal-symbol carriers, Wick reduction and sea-Wick quartic correction are deferred to their dependent chapters. Do not force the full appendix into this finite-CAR sprint. The drafted file split and names are now concrete in the two notebooks; they are now proved and frozen in Core.

## Current review: parallel CH05 and CH06 Phase A

The user authorized CH05 Phase A and parallel CH06 Phase A on 2026-10-09. One primary formalizer drafted CH05; one delegated formalizer drafted CH06; both used the repository formalizer skill. Drafting in parallel is feasible because CH06's algebra, grading and word definitions can use the proposed position-generator interface without assuming its theorem stubs as definition fields. This does not make future proof work independent: CH05 inverse Fourier, adjoints, CAR and parity contracts must be proved before their CH06 uses.

CH05 proposes a positive-size Fourier layer, with physical half-filling statements explicitly restricted to `L=2*h`, `h>0`. It separates integer bare energy, its sea constant and the shifted Hamiltonian, including the `h=1` zero constant and `h≥2` nonzero witness. CH06 generates local algebras from both creators and annihilators, models parity eigenspaces as submodules, and drafts even-subalgebra/automorphism existence obligations. Graded-word spans support locality. Global fullness explicitly recovers momentum generators before constructing sign-corrected ordered matrix units in the momentum occupation basis.

Both source files and exact notebooks are ready for review; every theorem remains one `:= by sorry`. Fresh builds and native diagnostics show only the 35/54 expected stub warnings; definition axiom audits exclude `sorryAx`. The six Core sources, historical and active manifests, dependency manifest and toolchain are unchanged. Non-strict verification passes all 182 approved statements and 152 commands while identifying the drafts; strict verification rejects exactly these two unlocked files. Full CI is therefore not reported as passing for this Phase A state. Review and approval precede interface locking and Phase B; no proof work or promotion has begun.

## Following dependency order

| Sprint | Implementation direction | Acceptance focus |
| --- | --- | --- |
| CH05 after CH04/A02 | Instantiate modes as `Band (2*h)` with `h > 0`; define position operators using frozen A01 characters/normalization. Expand finite double sums for position CAR, adjointness, inverse transform and total-number invariance. Define bare `H₀`, its sea constant, and the shifted energy separately. | No factor-of-L/sign drift; actual adjoints; occupation-basis spectrum and nonzero vacuum shift preserved. |
| CH06 after CH05 | Generate local star-closed CAR algebras; use `(a ± α(a))/2` for parity projections. Prove isotony/additivity, graded locality by homogeneous words, and global matrix units with fixed operator order and sign correction. | Odd part is a subspace; matrix-unit signs and star closure proved; empty-region algebra identified with scalars. |
| CH07/A03 after energy infrastructure | Completed: integer sector energy, coordinate projections, signed filtered maps and word excursions are proved and frozen. | Ground uniqueness, nonzero ground/one-step witnesses, frozen margins and total-species budgets proved; twist bridge documented. |

Each authorized chapter sprint has its own independent Phase A review and lock, Phase B proofs, and validated automatic Phase C transition. If a shared mathematical contract fails, follow the issue-sprint procedure above before dependent implementation resumes.

## Boundary extension completion and downstream plan

Ch06Ext Phase C is complete after the approved twelve-lemma cleanup. The module is frozen in Core; every earlier Core file remains unchanged. Its chosen twist is retained by fields, transport and zero modes, while proved density/local-algebra and same-sea excitation identities permit specific cancellations. The [boundary issue](note/issue_twisted_boundary_conditions_2026-10-09.md) remains open for source reconciliation and spin-model/vertex obligations.

A03/CH07 Phase C is complete, including signed coordinate budgets, rank/ground witnesses, sector-dependent particle action and word excursions. The checked twist bridge identifies the same-sea linear excitation with CH07’s integer reference energy. The earlier Phase A request produced the CH08 draft, with 43 complete data declarations and 62 unproved theorem signatures. A04 supports CH09–CH12 and is deferred to those chapters. CH08 has now passed independent review. The next chapter-development execution can lock CH08, prove it in Phase B and audit/promote it in Phase C under the standing policy. CH09 with relevant A04 density support is the subsequent roadmap item, requiring scope authorization; the workflow-update task does not launch those proofs or another chapter. CH09–CH12 must prove cancellation for their actual bilinears and margins; CH13/CH14/A05 must retain species twists and explicitly typed source/target sector maps. Later physical observables retain parameters unless a cancellation theorem applies. The A03/CH07 interfaces are now approved and committed at `20ed09b`.

## Current review: CH08 Phase A

The abstract weighted polynomial oscillator target is drafted in [Ch08Boson.lean](Bosonize/Core/Ch08Boson.lean), with expanded comments and an [exact companion notebook](docs/companion/Bosonize/Core/Ch08Boson.md). Native MCP diagnostics/goals work; all data exclude sorryAx and every theorem remains a single sorry. Both libraries and all 69 guard tests pass. Existing locks/Core are unchanged; strict verification intentionally rejects the new unlocked draft. The independent agent review gate precedes locking or proof work; subsequent transitions are automatic for authorized chapter development. See the notebook for carriers, proof order, witnesses, source reconciliation and the later twist-dependent current dictionary.

## Automatic pipeline adoption — 2026-10-09

The user replaced routine human A/B/C confirmations with independent agent review and automatic phase progression for authorized chapter development. The repository skill/workflows/conventions/MCP reference and README now use this policy. Human involvement is reserved for substantive ambiguity; explicit stop/phase-only requests remain binding. The separate CH08 reviewer passed the unchanged draft (source hash and findings in its notebook). This workflow-update task changes no Lean source, chapter lock or Core file. The policy is a procedure for agent execution, not a scheduler.

Validation of this policy update: the skill-creator validator passed. Agent `/root/pipeline_policy_review` forward-tested chapter authorization, explicit Phase A-only stops, failed guards/unrelated drafts, equivalent staging corrections versus ambiguous replacements, repeated tactic failure, and workflow-only requests. It initially requested three corrections (promotion import/context migration, downstream scope, ambiguity-first source adoption); the primary applied them and the reviewer reread the final files with verdict PASS. Agent `/root/ch08_interface_review` separately passed the exact existing CH08 draft. These reviews are procedural/interface evidence, not chapter proofs.

## Phase C pedagogical synchronization — 2026-10-10

The user extended Phase C to update the pedagogical chapter note as well as its companion. The repository-local `pedagogical-sync` skill preserves the original reference material, explains the actual verified mathematical construction and its relation to the abstract theory, retains exact assumptions/parameters and accurately labels unformalized scope. Appendix implementation updates its corresponding appendix section. The companion focuses on the formal Lean document and its evidence; the pedagogical Markdown is a complementary lecture note explaining the Lean file and the mathematics of its constructive approach. A separate agent reviews the pedagogical diff before Phase C is complete. This policy update does not retrospectively rewrite earlier notes or mark CH08 proofs complete.

Validation (2026-10-10): both skill validators pass. Agent `/root/pedagogical_skill_check` forward-tested the new skill on an isolated CH07 copy and returned PASS for skill behavior/integration. The test retained all 8,756 original worktree bytes as an exact prefix, added one mathematical lecture section, kept technical mappings in a companion packet, and checked source/snapshot and links. It covered ambiguous corrections, partial appendices, unproved staging, prior edits and stale indexes. Its candidate pedagogical diff remains a temporary review artifact, not an applied note update or fresh Phase C audit; historical compiler/axiom evidence is labeled accordingly. The primary also verified preservation and links; all eleven existing Core hashes pass. Original note and lock-manifest edits are preserved outside this workflow change.

## CH08 completion — 2026-10-10

The automatic A–B–C sprint is complete. Reviewed interface `8d38c21` and scoped
Mathlib import amendment `b229bbf` preceded proof batches; `0a2cb2a` saved the
61-proof intermediate checkpoint. All 62 theorem targets are now proved and
promoted to Core without changed mathematical interfaces. Fresh audits through
`import Bosonize` cover all 519 Core theorem targets and 43 CH08 data declarations,
using only permitted standard axioms or none. Both guards, 69 regression tests
and both builds pass with zero warnings/placeholders. The exact formal companion
and appended constructive lecture are complementary; independent pedagogical
review confirms original reference preservation and accurate proof scope.

CH09 with the relevant A04 density portion is next. It must define the actual
fermionic density/current operators, retain the chosen twist family, and prove
any cancellation and budget margins used by the comparison. CH08 alone proves no
physical twist independence, analytic completion, or unrestricted bosonization
identity. This sprint does not begin that subsequent chapter.

## CH10/A04 completed continuation — 2026-10-10

Reviewed interface `e2074b4`, complete proofs `7b0f1c1`; [Phase C evidence](note/ch10_phase_c_validation_2026-10-10.md). Thirty-seven new theorem proofs and six data definitions are complete and frozen in Core, with both complementary lectures updated and independently reviewed. Existing fourteen Core modules are unchanged. The one-time continuation automation was deleted after handling its wakeup. CH11/A04 is the exact next item; no work on that chapter has started. Current weekly allowance is 4%, below the adopted 5% threshold; development is paused after this completed checkpoint. No automatic resumption or quota reset is scheduled.

## CH11/A04 active sprint — 2026-10-11

Fresh usage permits development again. Phase A independently approved 61 targets (25 A04 partition combinatorics and 36 CH11 density-state completeness) and 15 complete data declarations. The explicit occupation/partition inverse, R1 count and actual right-remainder R2 Gram contracts are locked. See [independent review](note/ch11_phase_a_review_2026-10-11.md). Phase B supplies proofs next; none of these targets is yet promoted or proved. CH12 remains outside this sprint. Existing sixteen Core modules are unchanged.

## CH11/A04 completion — 2026-10-11

The automatic A–B–C sprint is complete. All 61 theorem targets and 15 data declarations are proved/audited; the two modules are frozen in Core. The independently reviewed geometric and Hall-recurrence cleanups remove redundant premises. Fresh Core-aggregator audits, both warning-free builds, both guards, 69 guard tests and native MCP diagnostics pass. All 34 pedagogical notes pass strict KaTeX parsing (3,137 math fragments). Both complementary lectures preserve the reference theory and pass independent review. Existing sixteen Core sources remain byte-identical; Core now contains 677 proved targets across eighteen modules. See [validation](note/ch11_phase_c_validation_2026-10-11.md).

Next is CH12 with the remaining A04 Sugawara support: define the finite normal-ordered energy sum, prove its action on the actual partition basis, use lowering annihilation to remove modes above the budget cutoff, and extend equality to the whole budget. Preserve R2 and the existing same-sea ground-energy shift; absolute twist-dependent sector energies require their own dictionary. No CH12 source has been drafted in this sprint. Earlier allowance/pending-development paragraphs are historical checkpoints superseded by this completion.

## Whole-project continuation authorization — 2026-10-11

The user's active goal now authorizes sequential A–B–C development of the remaining chapters and supporting appendices, with quality and complete proof verification taking precedence over speed. A chapter completion is an intermediate checkpoint. CH12 is now in Phase A drafting after completed CH11. Every next item retains independent interface/pedagogical review and all freeze, axiom, guard and warning-free build requirements. Substantive mathematical ambiguity still requires the human decision.

The user also explicitly authorizes sleep/scheduled quota resumption. The formalizer usage policy now permits a supported thread wakeup after the limiting reported reset, followed by fresh usage and authoritative checkout/checkpoint verification. Thresholds remain less than 10% five-hour or less than 5% weekly; reset/paid credits are never spent automatically. Agent `/root/ch11_gram_probe` independently reviewed the exact policy diff with PASS, and the skill validator passes. Existing eighteen Core modules and frozen interfaces remain unchanged. Latest quota snapshot at this policy checkpoint: 16% five-hour and 87% weekly remaining; no wakeup has yet been arranged. Earlier no-automatic-resumption checkpoints are superseded by this explicit goal authorization.

## CH12 quota checkpoint — 2026-10-11

CH12 Phase A is drafted and independently reviewed. The live five-hour remainder reached 9% (weekly 86%), so the pipeline stops before locking/Phase B. Preserve the reviewed source hash and all 26 unproved obligations; no CH12 theorem is promoted. [Exact checkpoint and resume action](note/quota_checkpoint_2026-10-11_ch12.md). The supported thread wakeup `resume-bosonize-after-quota-reset` is ACTIVE for 15:14 Fortaleza, guarded against resuming before 18:14 UTC and against unrecovered usage. The full project goal remains active; no reset credits are spent.

## CH12 reset resumption — 2026-10-11

Fresh usage after 18:14 UTC permits development (98% five-hour, 85% weekly remaining). The exact reviewed Phase A source and all five complete data declarations pass fresh checks. Only CH12 is added to the reviewed interface manifest; all eighteen Core modules remain unchanged. The consumed wakeup is deleted. Phase B supplies the 26 proofs next; historical quota paragraphs above record the earlier wait.

## CH12 Phase C completion — 2026-10-11

The finite Sugawara sum, stable budget cutoff, multiplicity/partition action, whole-budget energy equivalence, signed two-budget commutators, same-sea physical energy dictionary and actual nonzero witnesses are proved. All 31 declarations have fresh standard-axiom Core audits. Nineteen Core modules retain complete-source hashes; old eighteen are unchanged. Both companion and complementary CH12/A04 lecture updates pass independent review. Full CI passes 69 tests and both libraries without warnings. Next authorized item is CH13/A05; no infinite-band vertex identity is inferred.

## CH13/A05 reviewed Phase A — 2026-10-11

Independent review passes the exact actual multispecies draft: A05 28 and CH13 25 unproved contracts, 42 complete audited data constants. Local explicit lexical-order projections preserve the ordinary CH07 carrier. Total excitation, actual CAR product/Gram/basis obligations, finite normalized kernels, typed inverse/isometry/four-budget squares and nonzero single/double paths are explicit. Same-species zero-transfer is the number-shift law rather than current intertwining; physical field ground coefficients retain species twists. Only these reviewed staging entries are locked. Existing nineteen Core files stay frozen. Phase B is complete: all 53 proofs and42 data declarations pass fresh standard-axiom closure; zero warnings/placeholders. The four unused-instance omissions have separate independent review; no new Core promotion.

## CH13 Phase B quota boundary — 2026-10-11

16/53 proofs complete and standard-axiom audited;37 remain in staging. Usage9% five-hour/71% weekly; development pauses. [Exact checkpoint](note/quota_checkpoint_2026-10-11_ch13.md). Supported one-time heartbeat resumes after20:15 Fortaleza with fresh usage verification. No reset credits used or incomplete Core promotion.

## CH13/A05 complete Phase B — 2026-10-11

53 complete proofs and42 data declarations pass fresh standard-axiom audits, warning-as-error compilation, native diagnostics and strict guards. Independent proof review and scoped migration plan are recorded. Phase C promotion/companion migration/complementary CH13 andA05 lecture synchronization remain next; no incomplete Core promotion. Historical quota checkpoints above are superseded by this resumed proof completion.

## CH13/A05 Phase C completion and quota checkpoint — 2026-10-11

All53proofs/42data pass fresh standard-axiom closure; Core migration freezes21modules/756proved statements, old19unchanged. Both complementary lectures preserve reference content and pass independent review. Full CI/KaTeX checks pass. [Validation](note/ch13_phase_c_validation_2026-10-11.md). Usage9%five-hour/56%weekly: pause beforeCH14/A05 PhaseA. Supported continuation01:16FortalezaOctober12 after04:15:20UTCreset requires freshquota. Whole-project goal remainsunfinished; noreset creditsused.

## CH14/A05 reviewed Phase A — 2026-10-12

Fresh quota permits resumption at the clean CH13 checkpoint. Independently reviewed 37 theorem obligations (A05 13, CH14 24) and 20 complete data declarations are frozen. The interface covers generic finite Taylor algebra and bounded filtration nilpotency, actual compressed/subtype phase nilpotency, typed adjoints, explicit source holonomy, full projected CAR ground expansion, exact projection residuals and the conditional cyclic comparison criterion. No unconditional numerical-margin field–vertex identity is included. Phase B is next. Existing 21 Core modules remain immutable.

## CH14/A05 complete Phase B — 2026-10-12

All 37 proofs and 20 data declarations pass fresh standard-axiom audits and warning-free compilation. Actual ambient and subtype phase nilpotency is proved, alongside true adjoint reversal, holonomy, complete retained ground-vector expansion, exact projection excursions and conditional cyclic uniqueness. No unconditional field dictionary is asserted. Independent final review and exact migration plan are recorded; Phase C is next.

## CH13/A05 verification and CH14 checkpoint synchronization — 2026-10-13

CH13 and multispecies A05 remain fully completed and frozen: 53 theorem proofs and 42 data declarations, independent final proof and lecture reviews. Their original Core hashes are unchanged. The later CH14/finite-exponential A05 checkpoint now completes Phase C with 37 proofs and 20 data declarations, the reviewed migration and unchanged independently reviewed lectures. Fresh current-checkout builds, Core-aggregator axiom audit and full CI are recorded in note/ch14_phase_c_validation_2026-10-13.md. The project now freezes 23 Core modules and 793 proved statements. CH15/A06 is the next development item; no new chapter implementation is part of this synchronization check.

<!-- lean-cycle CH15 -->
## Automated CH15 checkpoint

CH15: **C_complete**. 23 contracts; 0 pending proof modules. Current machine record: `docs/webllm/chapters/ch15.json`.

<!-- /lean-cycle CH15 -->

<!-- lean-cycle CH16 -->
## Automated CH16 checkpoint

CH16: **C_complete**. 19 contracts; 0 pending proof modules. Current machine record: `docs/webllm/chapters/ch16.json`.

<!-- /lean-cycle CH16 -->


## Historical CH16 local checkpoint — 2026-10-13

Phase A independently reviewed and accepted (19 contracts,29 data); ten local
proofs compiled with standard axioms, three further bodies dependency-blocked.
No Phase B batch accepted or Phase C promotion. Quota guard stopped new work
below10% remaining; [resumption record](note/ch16_quota_checkpoint_2026-10-13.md).
CH17 remains outside the authorized scope.


The historical quota checkpoint is superseded by completed CH16/A07 Phase C. All 19 contracts are proved and frozen; Core now has 27 modules and 835 statements. See the final validation above.

<!-- lean-cycle CH17 -->
## Automated CH17 checkpoint

CH17: **B_complete**. 37 contracts; 0 pending proof modules. Current machine record: `docs/webllm/chapters/ch17.json`.

<!-- /lean-cycle CH17 -->
