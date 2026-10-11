# Bosonize-Lean — Strategy v2

**Status:** draft for approval · **Date:** 2026-10-06
**Supersedes:** the colour-team roster (Yellow/Blue/Red/Purple) and the six-agent roster of the external cheat-sheet.
**Scope:** how agents, tools, scripts and documentation fit together to formalize `../lean-bosonization-notes` into Lean 4 + Mathlib, one chapter per Lean entry file, driven from Google Antigravity on VS Code + WSL2.

**Legend** — ✔ verified against a primary source on 2026-10-06 (source named) · ⚠ unverified or an estimate: test before relying · 🔧 to be built.

Sources used: `lean-lsp-mcp` README and `docs/tools.md` (github.com/oOo0oOo/lean-lsp-mcp); Choir paper (arXiv 2609.31903), Choir README, ProbMethodCombinatorics README; `leanprover/comparator` README and the Lean Language Reference chapter "Validating a Lean Proof"; Antigravity configuration conventions (`AGENTS.md`, `.agents/{rules,skills,workflows,mcp_config.json}`).

---

## 1. Corrections to the external material

| # | External claim | What is actually true | Consequence for us |
|---|---|---|---|
| 1 | Agents configured via `.agents.yaml` | No such file in the Antigravity conventions found. Roles belong in `.agents/skills/<name>/SKILL.md`, rules in `.agents/rules/`, slash commands in `.agents/workflows/`. | Roles are skills. No YAML orchestration file. |
| 2 | Tools are called `diagnostic_messages`, `goal_state` | ✔ Real names carry a `lean_` prefix: `lean_diagnostic_messages`, `lean_goal`, `lean_term_goal`, `lean_hover_info`, `lean_multi_attempt`, `lean_run_code`, `lean_code_actions`, `lean_file_outline`, `lean_local_search`, `lean_loogle`, `lean_leansearch`, `lean_leanfinder`, `lean_state_search`, `lean_hammer_premise`, `lean_build`, `lean_verify`, `lean_minimal_hypotheses`, `lean_profile_proof`. | All skills and rules use the real names. |
| 3 | Hybrid RAG = Moogle + Loogle | ✔ `lean-lsp-mcp` does not expose Moogle. Its semantic tools are LeanSearch and Lean Finder; goal-based tools are State Search and Hammer Premise. | Hybrid RAG = local search + Loogle + LeanSearch + Lean Finder (+ goal-based tools). Section 5. |
| 4 | `LEAN_REPL=true` is a switch | ✔ It also requires the `repl` package in `lakefile.toml` at a revision matching the Lean toolchain, plus `lake build repl`. Without it the server silently falls back to the LSP path. | One-time human step. Section 5.5. |
| 5 | Put env vars in a project `.env` | ⚠ MCP servers receive env from the client config. | Set them in the `env` block of `.agents/mcp_config.json`, or as CLI flags (`--loogle-local`, `--repl`, `--lean-project-path`), which also survive a `wsl.exe` hop. |
| 6 | External search is a free-for-all | ✔ Most external tools are limited to 3 requests per 30 s each. | Retrieval is budgeted and cached. Section 5.6. |
| 7 | The three bridge scripts can be deleted | ✔ Correct: `lean_repl_bridge.py`, `loogle_query.py`, `lsp_log_parser.py` are replaced by MCP tools. They were never written here. | Not built. Section 9. |
| 8 | (analysis missed) | ✔ `lean_verify` returns the axioms a theorem uses (flags `sorryAx`) and scans for `unsafe` / `implemented_by` / `debug` options. `lean_minimal_hypotheses` re-elaborates with each hypothesis removed and reports which are load-bearing. | Two cheap anti-vacuity probes. Section 4. |
| 9 | Dump-folder protocol, agents wait on `lock.tmp` | LLMs cannot be trusted to honour a file lock by convention. | A script owns locking and numbering. Section 6.1. |
| 10 | Scribe is an agent | Its job is deterministic compilation of logs. | Script. Section 7. |
| 11 | Lake enforces the Core/Stubs/Continuum dependency direction | One Lake package does not enforce it. | `import_direction.py` guard (built). |
| 12 | Cheat-sheet worked example (`cancel_add_sub` tactic, a `ring` warning, a "Gemini 3.8 Pro" model name); BEq+ benchmark figures | ⚠ None verified. | Not used as a basis for any decision. |
| 13 | Choir `create-task` / `worker submit` are part of the design | See Section 8: real, but pre-alpha and built for distributed contributors. | Independent of Choir; borrow ideas only. |

---

## 2. Design principles

1. **Separate by failure mode, not by job title.** An agent boundary is worth its hand-off cost only where it buys *independence* (errors would otherwise correlate) or *privilege separation* (one party must not touch what another controls).
2. **Anything checkable is a script.** LLM judgement is spent only on meaning: reading the notes, choosing statements, finding proofs, deciding what to do after a failure.
3. **The kernel and CI decide "done"; a human decides "means the right thing".** No agent self-certifies.
4. **Risk-tier the effort.** Definitions and key theorems get the full audit; routine lemmas get script gates only.
5. **Cheap-first escalation.** Fast model → strong model → restructure the statement/decomposition → human.
6. **Everything leaves a trace.** Dump entries → companion documents → ledger.

### 2.1 Failure modes and their primary controls

| ID | Failure | Compiler catches it? | Primary control |
|---|---|---|---|
| F1 | Wrong statement (misread notes, sign/normalisation error, OCR error) | **No** | Blind oracle, differential tests, back-translation, human lock review |
| F2 | Vacuous or degenerate statement (zero operator, contradictory or unused hypotheses) | **No** (the Choir paper states this gap is not closed mechanically) | `lean_minimal_hypotheses`, witness lemmas, non-degeneracy lemmas, `anti_trivial.py` |
| F3 | Proof too hard / missing lemma | Yes (as failure) | Prover ladder, decomposition |
| F4 | Hallucinated Mathlib names | Yes | Retrieval policy; every name verified by `lean_local_search` |
| F5 | Statement drift after lock; `sorry` or axiom creeping into Core | Partly | `stub_lock.py` (now), comparator (later), `warningAsError`, `lean_verify` |
| F6 | Races and scope creep between parallel agents | No | Script-owned module lock, per-role file permissions |
| F7 | Knowledge lost between sessions | No | Dump → Scribe → companion docs; lessons memory |

F1 and F2 are the dangerous ones: a fully proved wrong theorem looks identical to a right one. Almost all the design effort in Section 4 goes there.

---

## 3. Agent roster v2

Three LLM roles plus the human overseer. Everything else is a script.

### 3.1 Roles

| Role | Instances | Model tier | Reads | May edit | Output |
|---|---|---|---|---|---|
| **Architect** | 1 conversation per chapter | Strongest available | notes, ledger, Mathlib (via tools) | `notes/md/`, `docs/spec/`, `BosonizeStubs/` (statements, definitions, non-degeneracy statements), `workflow/tasks/` | claims with explicit witnesses; stubs with one `sorry` per theorem; task cards; decompositions; triage of escalations |
| **Skeptic** | 2 fresh conversations per T1 claim (blind phase, audit phase) | Strongest available, **ideally a different model family from the Architect** ⚠ (depends on your Antigravity plan) | phase-dependent (see 4.1) | `oracle/`, `tests/`; verdict files only. Never Lean, never notes | oracle, differential-test spec, mutants, back-translation, audit verdict |
| **Prover** | N parallel, one per task card | Ladder: fast → strong | one task card, dependency signatures, MCP tools | the proof body of the one named theorem (plus private helper lemmas in that file) | proof, VeriRefine log |
| **Overseer (you)** | — | — | lock packets, gate packets | everything, via approvals | lock approvals, phase gates |

**Why Architect and Prover are separate:** the party that writes a statement must not be the party that is rewarded for proving it. This is the same split Choir uses (the orchestrator authors statements; workers only prove; the gate checks the statement is unchanged), and it makes statement drift an *impossible action* rather than a policy.

**Why Skeptic is separate from the Architect:** the Architect's misreading of the notes would otherwise leak into its tests too. Independence comes from three things, in order of strength: different information (blind phase), different model family (if available), different conversation (always).

### 3.2 What happened to the earlier categories

| Earlier role | Becomes |
|---|---|
| Planner/Prover (guideline) | Split: **Architect** (plans, states) and **Prover** (proves) |
| Tool-User | Not an agent. A retrieval *policy* (rule file) plus a cache script. A dedicated agent only adds hand-offs; the 3 req/30 s limit is handled by budgets and a cache |
| Critic/Corrector | The compile-repair loop lives in the Prover under the **VeriRefine** script; semantic criticism lives in the **Skeptic**; mechanical checks live in CI |
| Lesson-Learner | Script plus human pruning (6.4) |
| Librarian | Tools (`lean_local_search`, `lean_file_outline`) and the import guards |
| Scribe | Script (7) |
| Distiller / Preprocessor / Formalizer / Formatter | Architect steps: witness checklist → `claims.yaml` → stub → file template and guards |
| Yellow / Blue / Red / Purple | Architect / Prover / Skeptic / (merged: scripts + Overseer) |

### 3.3 Prover escalation ladder

1. **Fast model**, ≤ 3 attempts per distinct goal state (goal-state hash).
2. **Strong model**, ≤ 3 attempts, with all retrieval levels enabled.
3. **Architect**: restate dependencies, or **decompose** the target into child lemmas with placeholder bodies (Choir's "decompose" move), each becoming its own task card.
4. **Overseer**.

A per-task cap of verifier calls (suggested 60 ⚠ tune after the pilot) triggers the next rung even if no single goal state repeated. Every escalation is an `ERROR_ESCALATION` dump entry with the goal state attached.

### 3.4 Risk tiers

| Tier | What | Pipeline |
|---|---|---|
| **T1** | Definitions others depend on; theorems with regime hypotheses; anything in Ch.1, 7, 9, 10, 11 core | Full: blind oracle + mutation score + differential test + back-translation + `lean_minimal_hypotheses` + witness + non-degeneracy + (optional) dual formalization + lock packet |
| **T2** | Routine algebraic/combinatorial lemmas (Leibniz, summation by parts, DFT identities) | Oracle by script-assisted Skeptic blind phase only; differential test where computable; script gates; no back-translation |
| **T3** | Helper lemmas invented by Provers | Not locked. CI only |

The Architect assigns the tier in `claims.yaml` (`tier: T1|T2`); the Overseer can raise but never lower it.

---

## 4. Statement fidelity and anti-vacuity (the efficient replacement for "same agent writes statement and oracle")

A fully proved wrong theorem is the most expensive failure, so this pipeline spends effort *before* proofs begin. It costs a handful of cheap calls per claim, small next to the dozens of verifier calls a proof takes.

### 4.1 Independence by information

```
notes excerpt ──► Skeptic S1 (blind) ──► oracle + tests            (never sees Lean)
notes excerpt ──► Architect ──────────► Lean stub                  (never sees oracle expected values)
Lean stub ────► Skeptic S2 (fresh) ──► back-translation            (never sees notes)
        lock packet = notes | statement_nl | back-translation | Lean | audit table | oracle summary
```

* **S1 (blind phase):** input is only the chapter notes and the ledger's `statement_nl`. Output: an exact-arithmetic oracle module and its tests.
* **Architect:** writes the stub from the notes. It does not see the oracle's numbers.
* **S2 (audit phase):** a fresh conversation reads only the Lean stub and writes it back in plain mathematics. A mismatch between that and the notes means the Lean statement does not say what the notes say, and the compiler could never reveal that.
* **Lock packet** (`scripts/lock_packet.py` 🔧): one page with all views side by side. Your review becomes comparing two English texts, not parsing Lean.

### 4.2 Mechanical layers (no LLM)

| Layer | Mechanism | Catches |
|---|---|---|
| **Mutation score** 🔧 | Automated mutation of the oracle implementation (AST operators: swap `+1`/`−1`, flip an exponent sign, `<` ↔ `≤`, swap Δ/∇, swap `E`/`E⁻¹`). The oracle's tests must kill the mutants. Threshold ≥ 90 % of non-equivalent mutants ⚠. A mutation tool such as `mutmut` may be used (verify compatibility) or a small custom AST mutator | Weak or tautological oracles; replaces "an agent invents mutants" |
| **Differential testing** 🔧 | For definitions that are computable in Lean (finite lattice, band, `ZMod L`-indexed objects, occupation-set Fock bases), a Lean script prints values with `#eval` for L = 1..12; Python compares with the oracle | Lean definition ≠ the maths, caught by evaluation instead of judgement |
| **`lean_minimal_hypotheses`** | Per theorem: which explicit hypotheses are load-bearing. An unused hypothesis is a F2 alarm (this is how "evenness of L is never an unused context variable" becomes enforced) | Dead or decorative hypotheses |
| **Witness lemma** | Every regime hypothesis (margins in m, n, K, N) has a lemma exhibiting a satisfying instance | Contradictory hypotheses |
| **Non-degeneracy lemma** | Every operator/state ships a lemma like `rho_one_vac_ne_zero` | Zero or trivial objects |
| **`anti_trivial.py`** (built) | Regex scan for bodies `0`, `id`, `∅`, `⊥`, `True`. Heuristic only | Crude green-washing |
| **`lean_verify`** | Axioms per theorem; flags `sorryAx`; scans for `unsafe`, `implemented_by`, `debug.*` | Unsound proofs |
| **Dual formalization (BEq-style)** — T1 only | A second, independent formalization of the same `statement_nl`; a script (`beq.py` 🔧) tests mutual derivability (`T1 → T2` and `T2 → T1` by `exact`/`simp_all`/`aesop`) | Statement-level misreadings that survive everything above. Phase 2 (Ch.10–11) |

### 4.3 Statement immutability

* **Now:** `stub_lock.py` hashes each locked signature; a locked theorem keeps its hash when it moves from `BosonizeStubs/` to `Bosonize/Core/`. Guard against text edits, **not** against a definition silently changing underneath an unchanged signature.
* **Later (gate hardening):** ✔ Lean FRO's `comparator` compares a trusted *Challenge* module with the *Solution* module at the kernel level (statement, the definitions it depends on, axioms), in a `landrun` sandbox with `lean4export`. This covers the weakness above. Requirements: Linux, `landrun`, a `lean4export` matching our toolchain, a frozen Challenge snapshot built from the lock commit. ⚠ Test whether `landrun` works under WSL2 (it relies on Landlock). Note comparator does **not** detect vacuity; Section 4.2 does.
