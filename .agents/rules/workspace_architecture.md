# Workspace architecture and development scope

`workspace.toml` is the repository inventory and stack/tier authority.
`/home/lucas/Projects/ACTIVE_FOCUS.md` is the current sprint authority; read it
before starting work. Tiers determine audit coverage, not permission to expand
implementation scope. Root files belong to the hub; child projects are independent
Git repositories, never automatically submodules of the hub.

## Current allocation

Read ACTIVE_FOCUS.md for the latest project-specific authorization; dated
infrastructure snapshots do not determine current chapter status. Bosonize-Lean
CH19/A08 and finite CH20 are promoted. Its current scope is documentation/Git
reconciliation and theoretical question preparation, before new CH20b/CH21 proofs.
Version 1 stays standalone; a complete version 2 refactor on finiteQMB is deferred.
finiteQMB is separately active under its own user direction. Do not infer scope
for another project from this summary. No default Antigravity or desktop-subagent
fallback; provider work requires the current task's authorization and budget.

## Domain and verification contracts

Lean specifies and proves; Julia performs numerical/symbolic computation.
Keep their artifacts in their respective projects and package directories.
Python uses uv-managed environments if dependencies are needed; the hub pipeline
uses only Python 3.11 standard library. Lean uses elan/Lake and project CI.
Julia uses project-local environments. Publication projects own their assets.

Local agents implement, test and review repository changes. Browser LLMs receive
bounded packets and return candidate files; whitelist, interface checks and local
verification decide acceptance. Colab performs background compute/transcription;
Jules works only on explicitly assigned jobs. Configured API/Jules transports and browser handoffs share acceptance gates. No subscription or model
availability is assumed. See the hub README routing table and llm/PROTOCOL.md.

Keep valid GitHub remotes on lufreitas0000 for active repositories. Preview all
external candidate diffs and keep independent specifications/oracles. Compiler
success and non-vacuity/physical correctness are separate requirements. Use the
five-column discovery journal before changing definitions or pivoting algorithms.
