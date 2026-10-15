# External pipeline planning checkpoint

Date: 2026-10-15. Initial planning snapshot, followed by the authorized I0–I2
implementation. See `note/infrastructure_i0_i2_completion_2026-10-15.md` for offline
acceptance evidence. No live pilot, proof development or book rewriting was started.

The canonical reusable design and retrospective are in the private workspace hub:
`/home/lucas/Projects/orchestrator/docs/EXTERNAL_PIPELINE_V4_PLAN.md`.
This project index deliberately does not duplicate that implementation plan.

Project requirements:

- Prefer Jules for bounded chapter/document/code patches and eligible OpenAI API
  pools for review and suitable proofs; no default Antigravity reviewer, author,
  desktop subagent, or fallback. Exhausted external budgets produce a checkpoint.
- Reconcile existing agent instructions and explicit `judge` entrypoints before
  calling this policy enforced. A routing TOML entry alone is insufficient.
- Extend the existing `agentctl` proof controller with generic task identity,
  immutable source inputs, asynchronous ownership, document/review result types,
  deterministic verifier plugins, provenance and cost/usage receipts.
- First proposed vertical slice: a small CH18 documentation repair via Jules,
  isolated verification and independent API review; frozen Core remains unchanged.
  Implement and test the infrastructure offline before dispatching the trial.
- The [book/coverage plan](BOOK_AND_SOURCE_COVERAGE_PLAN.md) and
  [adaptive roadmap](../adaptative_roadmap.md) own mathematical completion and
  publication decisions. The [audit](../note/ch18_and_orchestration_audit_2026-10-15.md)
  supplies concrete defects for the trial.
- Colab is optional bounded compute; local Qwen is optional low-risk assistance.
  Neither is an acceptance authority or a prerequisite to the first slice.

Future implementation must store safe task metadata and sanitized evidence in
version control while retaining secrets, private responses and raw transcripts in
their appropriate private stores. No current account-specific complimentary
entitlement, remaining balance or eligibility is assumed from this plan alone.
