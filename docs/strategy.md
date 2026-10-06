# Bosonize-Lean: Development Strategy and Roadmap

## 1. Architectural Philosophy
This project merges Research and Test-Driven Development (TDD). To optimize modularity within a cumulative dependency graph, we strictly separate the *Interface* (the theorem signatures) from the *Implementation* (the proof bodies). Once a chapter's signatures are proven and the file is locked into `Core/`, it becomes a read-only mathematical foundation. Upstream chapters are never modified to fix downstream problems.

## 2. The 3-Step Execution Loop
The development loop is localized, fast, and relies entirely on the Lean 4 compiler via MCP:
*   **Phase A: Draft & Notebook Review.** The LLM reads the Markdown notes and translates the definitions and claims into Lean 4 signatures inside `BosonizeStubs/ChNN.lean`. Concurrently, it writes its design rationale and structural choices to `docs/companion/BosonizeStubs/ChNN.md`. The human researcher reads this mirrored notebook to quickly audit the physical accuracy of the definitions and margin constraints. Iteration occurs here. Once approved, the signatures are locked.
*   **Phase B: Interactive Proof Search (`Refine@k`).** Operating within VS Code/WSL, the agent attacks the `sorry` stubs. It explicitly reads the proof sketches from the source Markdown notes to inform its high-level strategy. It uses `lean-lsp-mcp` tools (`lean_goal`, `lean_loogle`) to map the human strategy to specific Mathlib tactics, reading diagnostic errors to self-correct.
*   **Phase C: Audit & Freeze.** The chapter is built (`lake build`). If the file is free of `sorry` tokens and non-standard axioms, it is migrated to `Bosonize/Core/` and frozen.

## 3. Roadmap
*   **Phase 1: Foundations.** Chapters 1 through 8.
*   **Phase 2: The Density Sector.** Chapters 9 through 12.
*   **Phase 3+: Dictionary and Interactions.** Chapters 13 and beyond.
