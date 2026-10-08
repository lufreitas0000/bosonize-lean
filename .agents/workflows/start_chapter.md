# /start_chapter

**Description:** Initiates Phase A (Draft & Document) for a new chapter in the Bosonize-Lean project.

**Instructions for the Agent:**
When the user invokes `/start_chapter <Chapter Number>` (e.g., `/start_chapter 1`), execute the following steps:

1. **Read Source Material and Suggestions:** Locate and read the corresponding Markdown notes in `notes/md/` (e.g., `notes/md/ch01_lattice_band_geometry.md`) and cross-reference with `notes/md/TOC.md`. Read chapter-relevant files in `docs/stub_suggestion/` and inspect `docs/proof_suggestion/` for potential interface requirements. Critically evaluate suggestions against the mathematical notes, explicit hypotheses, and compiler; do not copy incomplete definitions or change assumptions to make suggested proofs succeed. If the chapter already has a lock, check it and preserve its approved interface rather than redrafting it.
2. **Draft Signatures:** Create a new Lean file in `BosonizeStubs/` (e.g., `BosonizeStubs/Ch01LatticeBand.lean`). Translate the mathematical definitions and claims into Lean 4 `def`, `abbrev`, and `theorem` signatures. Ensure all `def` and `abbrev` blocks are complete, and all `theorem` or `lemma` signatures terminate with exactly `:= by sorry`.
3. **Generate Lab Notebook:** Create a mirrored Markdown documentation file at `docs/companion/BosonizeStubs/` (e.g., `docs/companion/BosonizeStubs/Ch01LatticeBand.md`). Document your design rationale, the specific Mathlib structures you chose, and how you formalized any physical margin constraints or edge cases. Identify the suggestion files considered and explain which parts were adopted, adapted, or rejected. Keep the source snapshot synchronized with approved names and statements.
4. **Stop and Prompt:** Present a summary of the generated lab notebook and the drafted Lean stubs to the user for Human-in-the-Loop (HITL) review. Await the user's approval or iteration requests before proceeding.
