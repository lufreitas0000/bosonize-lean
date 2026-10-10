# Usage allowance and resumable checkpoints

Apply this policy during authorized A–B–C development. It is an agent workflow safeguard, not a platform spending cap or a background monitor. The user adopted the default thresholds on 2026-10-10; explicit user overrides take precedence.

## Read live allowance

Use the exposed Codex app `get_usage_limits` tool (`mcp__codex_app__get_usage_limits`), or an equivalent supported read-only usage tool available in the current environment. Check before starting a chapter, moving between A/B/C phases, or launching a parallel proof group. During sustained work, recheck approximately every 5–10 minutes at tool or proof boundaries; do not start a polling loop or a separate monitoring agent.

Prefer `rateLimitsByLimitId` when populated; otherwise use `rateLimits`. Identify applicable windows by their reported duration: 300 minutes for five hours and 10080 minutes for a week. Compute `remainingPercent = max(0, min(100, 100 - usedPercent))` from a valid numeric reading. For multiple applicable buckets, act if any reported five-hour or weekly window crosses its threshold. Missing/null windows mean unavailable, not zero remaining. Report the bucket, observation time, remaining percentages and available reset times in the user's timezone.

The default trigger is **less than 10% remaining in a five-hour window OR less than 5% remaining in a weekly window**. At the exact threshold, recheck before the next substantial batch. Also checkpoint if the tool reports that ordinary usage is disallowed or a usage/spend limit has already been reached. A credit balance of zero alone does not mean the included allowance is exhausted. Do not automatically purchase credits, spend a reset credit, switch billing credentials, or change model/provider to bypass a limit.

These readings are account-wide snapshots, not this chat's token budget or a reservation for the next task. Other chats and delegated work can consume allowance between checks. Codex readings do not establish Gemini or other providers' remaining quota. Do not infer enough capacity to finish a large batch from a positive percentage alone.

If the usage tool is absent, fails or omits a relevant window, state the precise visibility limitation once and do not claim that monitoring is active for that window. Continue authorized work with normal small checkpoints unless a known limit or user instruction requires stopping; retry a transient failure at the next normal check. Do not inspect authentication secrets or invent an unsupported usage endpoint.

## Threshold response

1. Warn promptly with the observed allowance, reset times if available, and the threshold crossed. Recommend pausing; stop launching new proof batches, retries, phase transitions or agents. Tell active delegated agents to stop new proof search and save their completed work and current goals.
2. Save a minimal durable checkpoint in the active companion and roadmap, or the project's existing task-checkpoint location. Record chapter/phase, approved lock/baseline, completed versus unproved lemmas, pending reviews, last actual build/guard/axiom results, current failures, delegated work locations and the exact next action. Label stale or unrun checks accurately. Save already completed edits; do not add placeholders to completed proofs, relax guards, edit frozen Core or promote an incomplete chapter to close the task.
3. Commit only scoped work that is suitable for a checkpoint under the existing authorization, preserving unrelated edits. Keep incomplete work explicitly marked; if it cannot be validated with the remaining allowance, preserve it as a draft and record that limitation rather than claiming verification. Sync only when already authorized. Finish essential checkpoint operations without beginning a new full proof/audit cycle merely to reach a phase boundary.
4. Yield to the user after reporting the checkpoint and recommended pause. Leave the development task resumable, not complete. Do not schedule a restart automatically. On an explicit resume or an already-authorized scheduled continuation, read fresh usage before starting another substantial batch and apply the same policy again. An explicit user override may authorize continued work despite the warning.
