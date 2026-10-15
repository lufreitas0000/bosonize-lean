# I0–I2 infrastructure and human browser workflow checkpoint

Date: 2026-10-15. Scope: shared controller and workflow instructions; no chapter
proof edits, promotion, book rewrite or live model-generation pilot.

## Delivered

- Default external-first policy reconciled in hub skills/rules and synchronized
  to the 14 active/foundations repositories. Antigravity review/generation is
  disabled in routing and gated at CLI and backend entrypoints.
- `agentctl task` supports committed specs, immutable packet/source identities,
  output ownership, dependency waits, task-wide attempt/token/session ceilings,
  restart-aware dispatch state, private receipts and archived exact responses.
- Browser downloads, OpenAI generation/review and Jules document patches reuse
  the existing preservation and sandboxed ingest gate. Explicit live flags and
  existing account allowlist/admission apply to provider calls. Daily deferral
  restores a waiting task instead of stranding it as an ambiguous call.
- Browser author/reviewer labels are self-reported; actual provider receipts are
  retained separately and linked. No API billing is inferred from a web response.
  Default browser labels are `web-unspecified`, not an invented returned model.
- `make work` provides the local menu. `make lean-check N LEAN_PHASE=X` verifies
  without approval/merge/push. Old start/finish commands retain their semantics.
  Exact matching downloads, isolated checks and complete feedback avoid manual
  packet-id copying or reconstructing compiler failures.
- Generic document tasks have independent, candidate-hash-bound PASS/REVISE
  reviews and explicit approval before local fast-forward integration. No task
  operation automatically merges or pushes. Existing chapter finish is the
  explicit phase integration/approval action and may push as configured.
- The document verifier supports Markdown structure, project-authored notation
  rules, fresh isolated TeX compilation, undefined/duplicate-reference failures,
  and explicitly configured PDF/log retention.
- A committed CH18 documentation task spec is ready for the next live/manual
  pilot. It changes only the pedagogical Markdown and companion; no Lean/lock
  edit or unconditional vacuum/CCR claim is allowed.

## Acceptance evidence

- Shared pipeline: **167 tests passed**, including real Git/Lean A–B–C fixtures
  and the new verify-before-finish behavior. The separate cycle run passed 25
  tests; it is a subset, not additional proof scope.
- Orchestration regression suite: **127 tests passed**, including daily
  admission-recovery. The task acceptance subset passed **31 tests**,
  covering browser failure/retry/review/integration, fake API author/review,
  fake Jules patch collection, restart/idempotence, stale/mutated inputs,
  unexpected targets, moved candidate branches, independent review, budgets,
  missing usage, protected verifier hashes, symlinks and sandbox refusal.
- Bosonize local CI: 69 guard tests, strict 968-statement/1020-command locks,
  31 complete Core locks, both libraries and 15 verifier tests passed.
- Real TeX trial: a valid document passed and retained PDF/log; a document with
  an unresolved reference produced a PDF but was correctly rejected.
- Hub CI now includes orchestration tests and namespace-sandbox setup on the
  disposable runner. Local results above are not a claim of remote CI success.
- Both Make entrypoints were exercised; guides/fences, secret scan and whitespace
  checks passed. Frozen Lean sources and lock manifests have no changes.

Complete logs are retained privately under hub `.agentctl/sprints/I0-I2/evidence/`.
The inventory and locally verified private archive preserve 39 unpublished draft/
LaTeX input files; those contents were not added to public Git. A local archive
is not itself an independent off-machine backup.

## Daily operation and scope boundary

Read workspace `orchestrator/docs/HUMAN_WORKFLOW.md`, or start with `make work`.
For the document pilot, from this repository:

```bash
make work-start SPEC=packets/ch18_documentation.toml
make work
```

Send the packet to the chosen chatbot, download the full response, check it,
and return generated retry feedback when needed. A separate reviewer chat can
provide the review. Only finish after the required review and your own approval.
Routine file/verification work should not require a supervising agent.

The real CH18 pilot is **I3, pending**. CH19 remains B-complete/C unfinished.
CH20–21 remain reviewed drafts. AWS inference, Colab, Qwen, automatic scheduling,
the review paper and locality/RG research remain outside this sprint.
Operator escalation is for mathematical ambiguity, frozen-interface corrections,
unresolved context, exhausted limits or uncertain interrupted provider dispatch.
