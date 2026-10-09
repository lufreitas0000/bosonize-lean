# Adaptive roadmap and Kanban pipeline

Updated: 2026-10-09. This is the overall project pipeline; it does not replace the A–B–C process inside each chapter. Follow the [formalizer skill](.agents/skills/formalizer/SKILL.md), [chapter drafting](.agents/workflows/start_chapter.md), [interface lock](.agents/workflows/lock_stub.md), and [promotion](.agents/workflows/freeze_chapter.md) procedures.

## Baseline and mathematical scope

Chapters 1–2 are proved and frozen in Core. The 21 chapter notes, A01–A10, and proof suggestions have a reconciled source baseline described in [the completion ledger](note/notes_review_completion_2026-10-09.md). Source-checking completion is not a Lean proof of later chapters or a guarantee that proof development will discover no further errors.

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
| CH03/A01 — Fourier | Ready | A next | CH01/CH02; root/sign contracts and Euclidean transport specified. | Draft complete definitions and one-sorry statements; mirror notebook for review. |
| CH04–CH07/A02–A03 — CAR and budgets | Backlog | A not started | CH03 normalization, occupation signs, finite Hilbert carrier, support budgets. | Refine exact interfaces after CH03 promotion. |
| CH08–CH12/A04 — Oscillators, currents, completeness, Sugawara | Backlog | A not started | CAR/budget infrastructure and exact edge formulas. | Prove grading, direct nonzero norms and useful right-suffix margins. |
| CH13–CH16/A05–A06 — Klein maps, conditional field criterion, fields | Backlog | A not started | Completeness and typed transitions. | Keep universal finite dictionary out of the unconditional interface. |
| CH17–CH19/A07–A08 — Interactions, Bogoliubov, states | Backlog | A not started | Exact sea-Wick Q correction; pairing model; weighted polynomial state. | Review finite-action and uncompressed-state interfaces separately. |
| CH20–CH21/A09–A10 — Formal vertices, duality, spin, leakage, SW | Backlog | A not started | Constructed states, charge maps, projection residuals and coefficient calculus. | Implement exact algebraic targets; keep analytic interpretations separate. |

A support appendix is read and implemented as needed alongside its dependent chapter; implementing every appendix before Fourier is unnecessary. Dates are review points, not promises about proof-search duration. Limit a sprint by an explicit goal and stopping condition; reassess at each completed chapter or issue resolution.

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

## Immediate next sprint: A01 and Chapter 3

Read A01 and the revised external Fourier guide. Derive the band/residue equivalence from frozen Chapter 1; prove representative independence and sign/character bridges. Reuse the installed complex `ZMod.dft` where it matches the kernels. Keep S/T unscaled and source/target types distinct, then transport to Euclidean carriers and isolate the single normalization scalar 1/√L. Stub the inverse, adjoint/isometry and existing Chapter 2 difference eigenvalues, including L=1 and the positive Nyquist convention. Draft U as a linear map before bundling an isometry equivalence whose proof fields are available only after Phase B.

Deliverable: a compiled Phase A staging draft plus its exact companion notebook and a reviewable dependency/proof plan. This roadmap establishes readiness; it does not itself start that draft, lock its statements, or authorize Phase B.
