---
name: start-chapter
description: >-
  Begin Lean 4 chapter formalization in Phase A, drafting stub signatures and mirrored
  companion notebooks before advancing through independently reviewed Phase B and Phase C.
---

# Start Chapter (`/start-chapter`)

Begins chapter development with Phase A, then advances through independently reviewed Phase B/C under the automatic pipeline unless the user explicitly requests Phase A only.

When the user invokes `/start-chapter <Chapter Number>` (e.g., `/start-chapter 1`), execute the following steps:

1. **Read Source Material and Strategies:** Locate and read the corresponding Markdown notes in `notes/md/` (e.g., `notes/md/ch01_preliminaries.md`) and cross-reference with `notes/md/TOC.md` and chapter-relevant `notes/appendices/`. Scrutinize both the mathematical statements and the embedded *Lean 4 Proof Strategies* and auxiliary lemmas directly under each definition, lemma, and theorem. Use the relevant sections of `../formalizer/references/proof_design.md` to assess carriers, domains, operator order, margins, and existence obligations. Report false or underspecified claims and propose repairs; do not copy incomplete definitions or change assumptions silently to make proofs succeed. If the chapter already has a lock, check it and preserve its approved interface rather than redrafting it.
2. **Draft Signatures:** Create a new Lean file in the staging library `<Project>Stubs/` (e.g., `<Project>Stubs/Ch01LatticeBand.lean`). Translate the mathematical definitions and claims into Lean 4 `def`, `abbrev`, and `theorem` signatures. Ensure all `def` and `abbrev` blocks are complete, and all `theorem` or `lemma` signatures terminate with exactly `:= by sorry`.
3. **Generate Lab Notebook:** Create a mirrored Markdown documentation file at `docs/companion/<Project>Stubs/` (e.g., `docs/companion/<Project>Stubs/Ch01LatticeBand.md`). Document your design rationale, the specific Mathlib structures you chose, and how you formalized any physical margin constraints or edge cases. Identify source versions, relevant appendices/corrections, and mathematical design decisions. Include proposed helper dependencies, useful local hypotheses, witness obligations, and unresolved mathematical issues. Distinguish an elaborated definition or witness stub from a proved result. Keep the source snapshot synchronized with approved names and statements.
4. **Independent Review, Commit, and Transition:** Follow [the pipeline policy](../formalizer/references/pipeline.md). Delegate mathematical/interface review to another agent (via `agentctl` / human browser packet; note Google Jules retired Nov 10, 2026), resolve deterministic findings, and re-review the affected final source. Record identity, source hash, verdict, and validation evidence in the notebook. Commit the reviewed draft atomically: `git commit -m "feat(<chapter>): draft <chapter> signatures and companion notebook"`. After a passing review, establish the scoped committed lock with [lock-stub](../lock-stub/SKILL.md), then proceed through Phase B and [freeze-chapter](../freeze-chapter/SKILL.md) automatically. Ask the user only for substantive ambiguity. Honor an explicit instruction to stop after Phase A or perform review only.
