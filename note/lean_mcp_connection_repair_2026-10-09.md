# Lean MCP launch repair and live checks — 2026-10-09

## Finding

The desktop WSL app-server environment could not resolve `uvx`, `lake` or `lean` on its PATH. The project configured the bare command `uvx`; the interactive shell had additional user paths and therefore gave a misleadingly successful command lookup.

The local Codex log database contains an explicit startup failure (`codex_mcp::rmcp_client`, 2026-10-09 18:59:33 UTC):

```text
MCP server startup failed server_name="lean-lsp-mcp" error=No such file or directory (os error 2)
```

Subsequent catalog logs omitted the server without a ready client, including this chat. A subprocess launched with the actual desktop app-server environment reproduced `FileNotFoundError` for `uvx lean-lsp-mcp`. This is a confirmed executable-resolution failure, not evidence that the Lean project or its LSP is broken. An enabled entry in `codex mcp list` alone did not establish connectivity.

## Repair

Only the project `.codex/config.toml` launch configuration changed:

- Use `/home/lucas/.local/bin/uvx` explicitly.
- Set the server working directory to this project.
- Supply a PATH containing `/home/lucas/.elan/bin` and `/home/lucas/.local/bin` plus standard binary directories, so the server can resolve both `lake` and `lean` in the desktop environment.
- Set a 60-second startup timeout and `required = true`. Codex documents that a required enabled server must initialize for startup/resume to succeed; this avoids silently continuing without Lean. The documented optional startup catalog grace is one second. The tested server initialized in 1.044 seconds, so making the project-essential server required also avoids depending on that short optional grace.

No global configuration, Lean source, theorem proof, interface lock or Core hash was changed.

## Fresh end-to-end evidence

The direct client launched the configured command with the desktop app-server's actual inherited environment plus the configured overrides. The server identified itself as `Lean LSP` 0.31.0. These checks passed:

| Check | Result |
| --- | --- |
| MCP initialization and `tools/list` | Success; 21 tools, including `lean_goal` and `lean_diagnostic_messages`. |
| A01 diagnostics through MCP | `success=true`, no diagnostics, no failed dependencies, not partial or timed out. |
| Chapter 3 diagnostics through MCP | Same clean result. |
| Temporary valid proof diagnostics | Clean result. |
| Temporary invalid proof diagnostics | Correctly reported `True.intro : True` where `False` was required, at line 3/column 3. |
| Live goal through `lean_goal` | `status=goals`, with `n : ℕ` and `⊢ n + 0 = n` before `rfl`. |
| Fresh Codex app-server `config/read` | Loaded the fixed project configuration, including required=true, absolute command, PATH and cwd. |
| Fresh Codex app-server `mcpServerStatus/list` | Discovered all 21 tools; `toolsError=null`. No chat or model turn was created for this check. |
| Cleanup | Both temporary Lean probe files removed; direct client and fresh diagnostic app-server processes stopped. |

The direct MCP test process exited 0. The server emitted an ignored Python subprocess cleanup exception (`Event loop is closed`) while shutting down after all results were returned. That is a separate shutdown observation, not a failed diagnostics/goal call or the original startup failure; no third-party server package was patched or warning suppressed.

## Current-chat boundary and reload

The existing chat still had no native Lean tool entries after these checks. Fresh discovery proves the fixed launcher and Codex tool discovery work; it does not prove the already-running chat's cached connection has been replaced. The fresh inventory's runtimeStatus is null because no thread runtime was created for that test.

No callable server-restart control is exposed to this chat. Use Settings → MCP servers → lean-lsp-mcp → Restart, then check `/mcp` and send a new message so the refreshed native tool catalog can be verified. Do not interpret the earlier phrase “MCP/LSP was unavailable” as a claim that the configured server or Lean LSP was broken: during Phase B, Lean tools were not exposed to the chat.

Official guidance: [MCP configuration and restart](https://learn.chatgpt.com/docs/extend/mcp?surface=cli), [configuration reference](https://learn.chatgpt.com/docs/config-file/config-reference).
