# Bosonize-Lean: Development Strategy and Roadmap

## 1. Architectural Philosophy
This project merges Research and Test-Driven Development (TDD). To optimize modularity within a cumulative dependency graph, we strictly separate the **Interface** (the theorem signatures) from the **Implementation** (the proof bodies). Once a chapter's signatures are proven and the file is locked into `Bosonize/Core/`, it becomes a read-only mathematical foundation. Upstream chapters are never modified to fix downstream problems.

## 2. The 3-Step Execution Loop
The development loop uses the installed Lean 4 compiler. MCP supplies interactive diagnostics and search when available; direct compiler diagnostics and local source searches provide the fallback described in the [formalizer skill](../.agents/skills/formalizer/SKILL.md).

### Phase A: Staging and the Mirrored Lab Notebook
Drafting the companion documentation simultaneously with the Lean definitions is the optimal approach for a Human-in-the-Loop (HITL) workflow. Before moving to the permanent core library, all draft Lean files live in the `BosonizeStubs/` directory.

When the agent translates Chapter $N$, it generates `BosonizeStubs/ChNN.lean` containing the definitions and the `sorry`-stubbed theorem signatures. Concurrently, it generates a mirrored markdown file at `docs/companion/BosonizeStubs/ChNN.md`. This companion file acts as a lab notebook, containing the agent's design rationale, choices of Mathlib structures, and the exact Lean signatures. The human researcher reads this mirrored notebook to audit the physical accuracy of the definitions and margin constraints, iterates with the agent on the definitions, and once satisfied, locks the stub. Only after Phase B is completed successfully does the file migrate to `Bosonize/Core/`.

### Phase B: Interactive Proof Search and Sketch Integration
The agent reads the chapter's proof sketches, relevant appendices, and suggestions, then checks their mathematical contracts before proving the approved `sorry` stubs. Source prose is not proof: operator domains, commutator order, projection remainders, and local margins must support the proposed argument. Use the relevant sections of [Proof design](../.agents/skills/formalizer/references/proof_design.md) and record adopted, adapted, or rejected suggestions in the notebook. A useful induction or reindexing plan can guide tactics; a failed plan does not justify changing a frozen statement.

### Phase C: Audit and Freeze
After Phase C authorization, build the chapter with zero warnings, require no placeholders, and audit freshly built theorem dependencies for only the permitted standard axioms. Resolve warnings at their cause rather than suppressing linters. Then promote the approved chapter to `Bosonize/Core/` and freeze it.

The promotion procedure is recorded in `.agents/workflows/freeze_chapter.md`. The definition/statement baseline follows the chapter's new path without changing its hashes. A separate `docs/spec/core_locks.json` manifest records the complete Core source hash, including proof bodies. CI runs both `stub_lock.py` and `core_lock.py`; the latter permits no changes to existing Core sources. The mirrored notebook moves to `docs/companion/Bosonize/Core/`, and the Core aggregator exposes the verified chapter to subsequent work.

## 3. Infrastructure and Tooling

### The MCP and Lean LSP Infrastructure
The Model Context Protocol (MCP) acts as a universal bridge connecting the LLM agent to the Lean compiler.
*   **The Architecture:** The configured Python-based MCP server (`lean-lsp-mcp`) communicates with its client via standard input/output (`stdio`) when exposed to that client.
*   **The Connection:** Internally, `lean-lsp-mcp` executes `lake serve` within the project root to spin up the exact same Lean Language Server that powers the VS Code extension.
*   **The Interaction:** When an available tool such as `lean_goal` is requested, the MCP server translates the request into an LSP request to the Lean compiler and returns the result. Configuration alone does not establish that the tools are exposed or working in the current chat; report actual MCP/LSP evidence separately from direct compiler checks.

### The Retrieval Hierarchy (MCP vs. Loogle)
When available through MCP, use Loogle as part of the retrieval hierarchy. Inspect the exact goal/errors, search existing project results, then use syntactic and semantic library searches as needed:
1.  **State Inspection (`lean_goal` & `lean_diagnostic_messages`):** Inspect these first when exposed to extract the exact compiler state and identify errors.
2.  **Local Project Search (`lean_local_search`):** Search the local `Bosonize` repository first using underlying `ripgrep` functionality to find auxiliary lemmas previously defined in the project.
3.  **Syntactic Mathlib Search (`lean_loogle`):** If the lemma is standard but the exact name is unknown, construct a syntactic type signature query (e.g., `?a * ?b = ?b * ?a`) to search the Mathlib index.
4.  **Semantic Mathlib Search:** If syntactic search is insufficient, use the semantic search/finder actually exposed by the server.

For unavailable tools, continue with `lake env lean`, scratch `#check`/`#print` declarations, and `rg` in project/installed Mathlib sources. The formalizer skill specifies the fallback and the three-attempt rule for an unchanged goal. Preserve completed proofs and record unresolved goals; do not inject placeholders into completed work.

## 4. Agent Configuration Tree
The orchestrator relies on a structured `.agents` directory to define global rules, slash commands, and the primary persona:

```text
.agents/
├── mcp_config.json                 # Configures the lean-lsp-mcp server and paths
├── rules/
│   └── lean_conventions.md         # Exact algebraic scope and global constraints
├── workflows/
│   ├── start_chapter.md            # Slash command to trigger Phase A
│   ├── lock_stub.md                # Slash command to hash and lock signatures
│   └── freeze_chapter.md           # Phase C audit and Core promotion
└── skills/
    └── formalizer/
        ├── SKILL.md                # Metadata, phase rules, retrieval, and proof checks
        └── references/
            └── proof_design.md     # Topic-specific mathematical contracts
```

