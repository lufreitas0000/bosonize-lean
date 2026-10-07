# Bosonize-Lean: Development Strategy and Roadmap

## 1. Architectural Philosophy
This project merges Research and Test-Driven Development (TDD). To optimize modularity within a cumulative dependency graph, we strictly separate the **Interface** (the theorem signatures) from the **Implementation** (the proof bodies). Once a chapter's signatures are proven and the file is locked into `Bosonize/Core/`, it becomes a read-only mathematical foundation. Upstream chapters are never modified to fix downstream problems.

## 2. The 3-Step Execution Loop
The development loop is localized, fast, and relies entirely on the Lean 4 compiler via the Model Context Protocol (MCP).

### Phase A: Staging and the Mirrored Lab Notebook
Drafting the companion documentation simultaneously with the Lean definitions is the optimal approach for a Human-in-the-Loop (HITL) workflow. Before moving to the permanent core library, all draft Lean files live in the `BosonizeStubs/` directory.

When the agent translates Chapter $N$, it generates `BosonizeStubs/ChNN.lean` containing the definitions and the `sorry`-stubbed theorem signatures. Concurrently, it generates a mirrored markdown file at `docs/companion/BosonizeStubs/ChNN.md`. This companion file acts as a lab notebook, containing the agent's design rationale, choices of Mathlib structures, and the exact Lean signatures. The human researcher reads this mirrored notebook to audit the physical accuracy of the definitions and margin constraints, iterates with the agent on the definitions, and once satisfied, locks the stub. Only after Phase B is completed successfully does the file migrate to `Bosonize/Core/`.

### Phase B: Interactive Proof Search and Sketch Integration
Operating within VS Code/WSL, the agent attacks the `sorry` stubs. The agent must explicitly read the proof sketches from the source Markdown notes to inform its high-level strategy. The notes bridge the gap between high-level mathematical intuition and formal tactics. If the note dictates a strategy (e.g., "proceed by induction on the partition length and commute the annihilation mode"), the agent translates this semantic strategy into specific Mathlib tactics (`induction`, `rw`, `ring`). The proof sketch narrows the LLM's vast search space down to a specific mathematical path.

### Phase C: Audit and Freeze
The chapter is built using `lake build`. If the file is free of `sorry` tokens and non-standard axioms, it is migrated to `Bosonize/Core/` and frozen.

## 3. Infrastructure and Tooling

### The MCP and Lean LSP Infrastructure
The Model Context Protocol (MCP) acts as a universal bridge connecting the LLM agent to the Lean compiler.
*   **The Architecture:** The local environment runs a Python-based MCP server (`lean-lsp-mcp`) which communicates with the Google Antigravity client via standard input/output (`stdio`).
*   **The Connection:** Internally, `lean-lsp-mcp` executes `lake serve` within the project root to spin up the exact same Lean Language Server that powers the VS Code extension.
*   **The Interaction:** When the agent requests a tool like `lean_goal`, the request travels from Antigravity to the MCP server via JSON-RPC, which translates it into an LSP request to the Lean compiler, retrieves the tactic state, and returns it to the agent seamlessly without manual file parsing.

### The Retrieval Hierarchy (MCP vs. Loogle)
Loogle is not an alternative to MCP; it is exposed as a tool *within* MCP. The agent must follow a strict, cascading order of tool execution to prevent hallucination and respect rate limits:
1.  **State Inspection (`lean_goal` & `lean_diagnostic_messages`):** Always execute these first to extract the exact compiler state and identify any errors.
2.  **Local Project Search (`lean_local_search`):** Search the local `Bosonize` repository first using underlying `ripgrep` functionality to find auxiliary lemmas previously defined in the project.
3.  **Syntactic Mathlib Search (`lean_loogle`):** If the lemma is standard but the exact name is unknown, construct a syntactic type signature query (e.g., `?a * ?b = ?b * ?a`) to search the Mathlib index.
4.  **Semantic Mathlib Search (`lean_leansearch` / `lean_finder`):** If the syntactic structure is unknown, fallback to querying the library using natural language descriptions.

## 4. Agent Configuration Tree
The orchestrator relies on a structured `.agents` directory to define global rules, slash commands, and the primary persona:

```text
.agents/
├── mcp_config.json                 # Configures the lean-lsp-mcp server and paths
├── rules/
│   └── lean_conventions.md         # Global constraints (e.g., no unbounded operators, no limits)
├── workflows/
│   ├── start_chapter.md            # Slash command to trigger Phase A
│   └── lock_stub.md                # Slash command to hash and lock signatures
└── skills/
    └── formalizer/
        └── SKILL.md                # The primary agent persona and operational loop
```



