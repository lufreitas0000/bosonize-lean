# Adaptive roadmap and Kanban pipeline

Updated: 2026-10-09. This is the overall project pipeline; it does not replace the A–B–C process inside each chapter. Follow the [formalizer skill](.agents/skills/formalizer/SKILL.md), [chapter drafting](.agents/workflows/start_chapter.md), [interface lock](.agents/workflows/lock_stub.md), and [promotion](.agents/workflows/freeze_chapter.md) procedures.

## Baseline and mathematical scope

Chapters 1–6, A01 and finite-CAR A02 are proved and frozen in Core (271 lemmas across eight modules). The 21 chapter notes, A01–A10, and proof suggestions have a reconciled source baseline described in [the completion ledger](note/notes_review_completion_2026-10-09.md). Source-checking completion is not a Lean proof of later chapters or a guarantee that proof development will discover no further errors.

Use exact finite-dimensional, polynomial, and explicitly specified algebraic constructions. Keep the finite CAR model separate from the uncompressed CCR/charge model and its coefficientwise series vertices. No analytic limit or formal substitution t=1 is implicit. Numerical-margin-only finite Mattis–Mandelstam equality remains a research candidate; the approved Chapter 14 target is the conditional cyclic-span criterion. Compactification, thermodynamic gaps, and new non-Abelian or refermionization programs belong to an optional research backlog with their own reviewed scope.

## Kanban board and work in progress

The board is a Markdown status table, maintained in this file. A card is a chapter, a supporting lemma package, or a dedicated issue sprint. Record owner, dependencies, current phase, evidence/commit, next action, and blockers. A board is coordination documentation; it does not implement an autonomous scheduler or authorize agents to create tasks or contact other threads.

| Column | Entry and exit rule | Work-in-progress policy |
| --- | --- | --- |
| Backlog | Named goal, source references and dependencies; no promise that its original claim is true. | Ordered by dependency and impact. |
| Ready | Dependencies available; scope, carrier, target and acceptance criteria agreed. | Keep a small queue; start only authorized work. |
| Active A/B/C | Execute one chapter's current phase and record its exact gate. | One primary chapter at a time; independent read-only/helper subtasks may run within authorized scope. |
| Review | Concrete signatures, correction proposal, or promotion diff ready for human review. | Approval already given in the session remains valid for that scope. |
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
| CH07/A03 — Sea and budgets | Review | A draft complete; unlocked | Frozen CH01/CH04/CH05; 45 complete data declarations and 114 unproved stubs; both builds, native MCP, definition axiom audit and 69 guard tests pass; committed-baseline strict guard rejects only these two separately unapproved drafts; local lock additions remain uncommitted. [A03 notebook](docs/companion/BosonizeStubs/A03EnergyBudgets.md), [CH07 notebook](docs/companion/BosonizeStubs/Ch07VacuumBudget.md). | Review signed coordinate budgets, rank/ground witnesses, sector-dependent particle action, actual word excursions and total-species energy; approve interfaces before locking and Phase B. |
| CH08–CH12/A04 — Oscillators, currents, completeness, Sugawara | Backlog | A not started | CAR/budget infrastructure and exact edge formulas. | Prove grading, direct nonzero norms and useful right-suffix margins. |
| CH13–CH16/A05–A06 — Klein maps, conditional field criterion, fields | Backlog | A not started | Completeness and typed transitions. | Keep universal finite dictionary out of the unconditional interface. |
| CH17–CH19/A07–A08 — Interactions, Bogoliubov, states | Backlog | A not started | Exact sea-Wick Q correction; pairing model; weighted polynomial state. | Review finite-action and uncompressed-state interfaces separately. |
| CH20–CH21/A09–A10 — Formal vertices, duality, spin, leakage, SW | Backlog | A not started | Constructed states, charge maps, projection residuals and coefficient calculus. | Implement exact algebraic targets; keep analytic interpretations separate. |

A support appendix is read and implemented as needed alongside its dependent chapter; implementing every appendix before Fourier is unnecessary. Dates are review points, not promises about proof-search duration. Limit a sprint by an explicit goal and stopping condition; reassess at each completed chapter or issue resolution.

Revisiting unusual or redundant assumptions is a healthy, expected part of proof development. Check necessity, satisfiability and downstream use; propose concrete corrections when evidence supports them. Review changes to frozen interfaces explicitly, preserve unrelated lock records, and repeat compiler and axiom checks after an approved correction.

## The chapter A–B–C cycle

**Phase A — Draft and document.** Read the current source, relevant appendices, suggestions and corrections. Check actual Mathlib APIs and instances. Define data completely in staging, with exactly one `:= by sorry` per theorem stub. Record carriers, source/target maps, hypotheses, nonvacuity, dependency lemmas, adopted/rejected suggestions and the exact source snapshot in the companion notebook. Build the draft, distinguish expected sorry diagnostics from other warnings, and present the concrete interface for review. Phase A stops before proof work or freezing unless already authorized.

**Gate A→B.** Human review approves definitions and statements, followed by the approved strict interface lock and a committed baseline. A passing guard certifies unchanged syntax, not truth. Never regenerate the baseline to hide drift or infer approval from a build.

**Phase B — Prove.** Change only approved proof bodies, use the compiler and available Lean tools, and preserve frozen data/interfaces. Run strict guards before and after batches. Update proof evidence and remaining placeholders in the notebook. New top-level helpers, assumptions, imports or source changes receive a concrete interface proposal and the existing review procedure before extending the lock. Stop retrying the same unresolved goal after three unsuccessful tactic attempts and report the missing mathematical step; that alone does not trigger a cross-chapter sprint.

**Gate B→C and Phase C — Audit, promote and freeze.** Require complete proofs, no warnings or placeholders, fresh axiom audits limited to `propext`, `Classical.choice`, `Quot.sound`, exact source/notebook coherence, and passing guards/builds. After authorized promotion, preserve declarations/namespaces while migrating paths, notebooks and aggregators; freeze the complete Core source. Commit and verify against that checkpoint. Existing Core is never silently rewritten to solve a downstream problem.

## Discovery triage: local repair or dedicated issue sprint

A local tactic/API mistake, small proof decomposition, or clarification confined to one unlocked chapter stays on that chapter's card. Fix it, verify it, and update its notebook. If a local correction changes a locked interface, halt the dependent proof and use the existing interface-review gate even if it does not need a sprint.

Open a **dedicated issue sprint** when evidence shows a shared mathematical or interface issue affecting multiple notes/files or downstream contracts: a counterexample to a reused theorem, incompatible carrier/adjoint conventions, insufficient shared margin, missing state existence, or a main statement whose strategy fails because essential mathematics is absent. Routine tactic failures and timeouts do not demonstrate such an issue.

1. **Halt affected work and checkpoint.** Preserve completed proofs, capture the failing goal/counterexample, source versions, current locks and Git status. Do not keep proving downstream statements that rely on the disputed result or repair Core by weakening it.
2. **Create an issue card and note.** Use `note/issue_<id>_<topic>.md` with the suspected false/missing contract, exact evidence, affected chapters/appendices/suggestions/companions, dependency impact, alternative repairs, proposed lemmas and resume conditions. No issue file is created for a merely hypothetical problem.
3. **Run the focused sprint.** Validate the smallest witness or obstruction, choose a useful correction with explicit hypotheses, and update every affected Markdown statement/proof suggestion. Complete reviewable corrections before requesting approval. Independent authorized work may continue outside the affected dependency closure.
4. **Review interface impact.** A note correction does not authorize changing a locked Lean statement. Present the exact proposed interface migration and obtain the required approval; preserve old evidence. A correction involving immutable Core needs a separately reviewed superseding/versioned design, never an overwritten hash.
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
| CH07/A03 after energy infrastructure | Work over integer relative charge and energy; prove sorted occupation rank formula and energy nonnegativity. Define budget coordinate spans/projections, admissible ground kets, grading and word excursions. | Empty/full sectors, nonzero ground witnesses, projection remainders, and right-to-left composition margins handled explicitly. |

Each sprint has its own Phase A review and lock, Phase B proofs, and Phase C authorization. If a shared mathematical contract fails, follow the issue-sprint procedure above before dependent implementation resumes.

## Boundary extension completion and downstream plan

Ch06Ext Phase C is complete after the approved twelve-lemma cleanup. The module is frozen in Core; every earlier Core file remains unchanged. Its chosen twist is retained by fields, transport and zero modes, while proved density/local-algebra and same-sea excitation identities permit specific cancellations. The [boundary issue](note/issue_twisted_boundary_conditions_2026-10-09.md) remains open for source reconciliation and spin-model/vertex obligations.

Next review A03/CH07 signed coordinate budgets, rank/ground witnesses, sector-dependent particle action and word excursions against the proved energy bridge. Approve their interfaces before Phase B. CH09–CH12 must prove cancellation for their actual bilinears and margins; CH13/CH14/A05 must retain species twists and explicitly typed source/target sector maps. Later physical observables retain parameters unless a cancellation theorem applies. Local A03/CH07 lock additions remain separate work.
