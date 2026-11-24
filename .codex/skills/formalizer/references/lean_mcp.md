# Lean MCP operations for Bosonize-Lean

Use this reference with the repository's formalizer skill. The installed Lean/Mathlib and compiler determine what elaborates. The chapter scope, automatic pipeline review gates and approved locks determine what may be edited. MCP supplies feedback; it does not replace independent review or change mathematical contracts.

| Task | Read |
| --- | --- |
| Develop a proof or inspect an unfamiliar declaration | Proof loop |
| Interpret warnings, empty results, or timeouts | Result handling |
| Report Phase A/B/C validation | Evidence and phase gates |
| Tools are missing or one call fails | Connection and PATH diagnosis |

## Proof loop

1. Inspect `lean_goal` at the relevant tactic and `lean_diagnostic_messages` for the affected file/range. Use current source positions: lines and columns are 1-based, and edits can move them. Omit the goal column for before/after feedback; use an exact column when a line contains several proof steps.
2. Use `lean_local_search` to find project helpers and installed declarations. For a known type pattern, use `lean_loogle`; for a mathematical description or uncertain terminology, use an available semantic tool such as `lean_leansearch` or `lean_leanfinder`. Read the actual exposed schema and respect rate limits. Do not cycle through searches after the required declaration is already identified.
3. Inspect the candidate with `lean_hover_info`, `lean_declaration_file`, or a scratch `#check`. Hover columns should point to the start of the identifier. Check imports, namespaces, implicit binders, typeclass instances, carriers, conjugation, operator order, and any hypotheses against the locked goal before using it.
4. Try a small proof step. Where exposed and useful, `lean_multi_attempt` can compare a few tactics at the exact goal position without committing a source edit. It does not authorize theorem work during Phase A. Persist only authorized proof-body changes; public helpers/imports or other interface changes follow the independent review and scoped lock-amendment procedure before proof work resumes.
5. Reinspect the resulting goals and diagnostics. An empty goal list at one tactic position is local feedback; verify the whole declaration/file before reporting completion. Apply the formalizer's three-attempt stopping rule to the same unresolved goal, and continue independent authorized goals when possible.

Use MCP selectively during Phase A to check definitions, library APIs and expected stub diagnostics. Keep every proposed theorem as one `:= by sorry`; elaborate definitions without consuming stub proofs. During Phase B, replace only approved proof bodies. Preserve immutable Core in every phase.

## Result handling

- Check `isError` and the structured payload. A successful tool invocation can still return Lean errors; `success: true` can include warnings. Inspect severity, category, failed dependencies, and completeness rather than only the success flag.
- Diagnostic results with `partial: true`, `timed_out: true`, or pending elaboration ranges are incomplete. Goal status `still_elaborating` also needs a later check. Allow bounded additional elaboration time; if repeated waits do not yield a complete result, report the limitation and use the compiler instead of calling the result clean.
- Goal status `complete` describes that position. `no_goal_at_position` means the position carries no proof state, not that the theorem is proved. Recheck the tactic location when needed.
- An empty local-search result establishes absence only when the symbol index reports `consulted`; `warming`, `unavailable`, and `error` do not. If the tool fails before consulting the index, use shell/source retrieval rather than guessing a missing API.
- Phase A `sorry` diagnostics are expected only in theorem stubs. Count and report them. A definition depending on `sorryAx` violates the draft contract even if it elaborates. Linter warnings must be resolved at their cause for promotion; do not suppress them or dismiss them as irrelevant noise.
- Errors in imported dependencies make downstream results incomplete. Build the relevant dependency or identify its actual failure before changing the chapter. Use `lean_build` only when a build/LSP refresh is needed; do not fetch caches or restart the server after every tactic.

## Evidence and phase gates

Keep these claims distinct in the companion notebook and final report:

| Evidence | What it establishes |
| --- | --- |
| Native tool present in this chat's catalog | The chat can attempt that tool. |
| Successful native diagnostic/goal call | That tool and its project interaction worked for the recorded file/position. |
| Direct local MCP client test | The server works through that client; native chat exposure is a separate check. |
| Fresh compiler/build result | The recorded source and dependencies elaborate with the reported diagnostics. |
| Interface/Core guards | Approved frozen syntax/source bytes are preserved; mathematical proof completion is separate. |
| Fresh axiom inspection | The inspected declarations' transitive proof dependencies use the recorded axioms. |

Run commands from the repository root. Select staging or Core paths for the actual current phase, rather than copying a historical module path.

- **Phase A:** build the affected staging modules/aggregator and Core; verify exact notebook snapshots and one-sorry theorem bodies. Audit definitions and relevant generated data declarations separately from theorem stubs. Preserve existing manifest entries during drafting. Non-strict verification can confirm existing locks while naming new files; strict verification must still reject unreviewed additions. After the independent review passes, establish only the reviewed scoped lock and proceed automatically. Report any pre-lock boundary rather than claiming full CI passes.
- **Phase B:** use the committed approved baseline with the strict interface guard before/after batches. Compile the changed modules and update notebook evidence. An MCP `lean_verify` call can assist declaration inspection, but does not replace the repository guards or the final fresh audit.
- **Phase C:** follow the existing promotion workflow. Require zero warnings/placeholders and fresh theorem axiom output containing only `propext`, `Classical.choice`, `Quot.sound`. Import the freshly built Core aggregator for the final audit. Run CI and both guards against the committed promotion baseline; pre-migration references retain historical paths and are not the new baseline.

Useful compiler fallback commands are `lake env lean <path>` and, for completed chapters, `lake env lean -DwarningAsError=true <path>`. Use scratch `#check`/`#print axioms` declarations and shell `rg` in project sources and `.lake/packages/mathlib/Mathlib`. An isolated scratch proof can expose a goal through `trace_state` or `exact?`; any placeholders in that scratch are inspection aids, not proof evidence. Keep scratch artifacts outside guarded source directories, record the meaningful output in the notebook, and remove temporary project files.

## Connection and PATH diagnosis

Diagnose only as far as the failure requires; do not make every proof task run a server health suite.

1. **Identify the failing layer.** Check the tools actually exposed to the current chat, then make a relevant diagnostic call. An enabled entry from `codex mcp list` establishes configuration, not a successful connection. Report a single failed search tool separately from working goals/diagnostics; avoid saying the entire Lean MCP or LSP is unavailable without evidence.
2. **Check effective launch configuration when startup fails.** This project configures `lean-lsp-mcp` in [`.codex/config.toml`](../../../../.codex/config.toml). Inspect its command, arguments, working directory, project path and environment alongside the relevant startup error. A terminal PATH can differ from the desktop/WSL app-server PATH. Check resolution in the server's effective environment, not only `command -v` in the interactive shell; read only needed environment keys and avoid exposing credentials.
3. **Check tool dependencies when only one tool fails.** A declaration-search error about `rg` means search could not run; Lean diagnostics may still work. Verify `rg`, `uvx`, `lake` and `lean` where relevant to the failing operation. Shell `rg` being available does not establish that the MCP child can find it. Discover actual executable locations rather than hardcoding a versioned Codex installation path from an old report.
4. **Keep repairs within scope.** Proof authorization alone does not request changes to server configuration or installed packages. Continue useful compiler/local-source work when possible. When connection repair is authorized, fix the evidenced command/environment problem narrowly and preserve unrelated configuration. Do not duplicate a working server, weaken freeze checks, or reinstall Lean/Mathlib to resolve an executable PATH error.
5. **Verify a reported repair end to end.** Test initialization/tool listing if using a direct client, project diagnostics, detection of an intentional error in a temporary file, and goal retrieval on a simple valid proof. Remove probes. Recheck native tool exposure and calls before claiming this chat's integration is restored. Package initialization or a fresh-client test alone is insufficient.

Reload controls vary by app surface. Do not insist on an unavailable Settings/Restart control, infer a gray Configure button's cause, or restart the entire app during active work. If native calls already work, no refresh is required for that connection. When a reload is needed but no control is exposed to the agent, explain the limitation and use the user's available controls without claiming a restart has occurred.

For the historical desktop executable-resolution failure and tested repair, see [the 2026-10-09 report](../../../../note/lean_mcp_connection_repair_2026-10-09.md). Treat that report as a snapshot: recheck current tool exposure and executable resolution rather than assuming its status remains current.
