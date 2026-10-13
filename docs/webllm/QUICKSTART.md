# Web-LLM A–B–C checklist

**Chat proposes; local Lean checks; you review and approve.** Repeat per chapter.

## 1. Send → verify → correct

Prepare/review the phase spec and context, then commit them in a clean checkout.
Current task: CH15/A06 Phase B support. From the hub:

```bash
cd /home/lucas/Projects
repo=/home/lucas/Projects/Lean/bosonize-lean
make packet SPEC=Lean/bosonize-lean/packets/ch15_phase_b_support.toml COPY=1
```

Paste the complete packet into a fresh Chat. Save its JSON as `response.json`
beside the packet; substitute the printed directory:

```bash
packet_dir=/actual/generated/packet/directory
make preview PACKET="$packet_dir" RESPONSE="$packet_dir/response.json"
make ingest PACKET="$packet_dir" RESPONSE="$packet_dir/response.json" MODEL=chatgpt-chat-high
# On failure: paste feedback into the same Chat, replace JSON, and retry.
make feedback PACKET="$packet_dir" COPY=1
```

On success, inspect logs/diff and merge the printed branch:

```bash
branch=actual-branch-printed-by-ingest
git -C "$repo" diff HEAD.."$branch"
git -C "$repo" merge --ff-only "$branch"
make -C "$repo" ci
```

## 2. Complete the phase gate

- **A — Specify:** Complete definitions + one-sorry theorem stubs. Review scope,
  signs, margins and nonzero witnesses; integrate/compile staging and audit data
  axioms. Run `make -C "$repo" lock-update`, inspect the manifest diff, run CI,
  then commit the reviewed source/notebook/lock. Verify that commit with
  `STUB_LOCK_BASELINE_REF=HEAD make -C "$repo" ci`.
- **B — Prove:** Edit only frozen proof bodies. Require fresh target/dependency
  compilation, zero target placeholders/warnings and only standard axioms;
  review proofs and record evidence. CH15: complete 16 A06 proofs, then seven
  CH15 proofs using the proved support checkpoint.
- **C — Promote:** Review audit/lecture candidates; move completed sources and
  companions to Core, update imports/aggregators and scoped locks, add full-source
  hashes, rerun CI and fresh Core axiom audits, then commit/push. Follow the
  [promotion checklist](../../.agents/workflows/freeze_chapter.md).

**When HEAD changes, regenerate the packet.** Preflight errors can be pasted
straight into Chat. A placeholders are expected; unrelated staging placeholders
may remain during a partial B batch. A successful build does not establish the
intended mathematics. Never silently weaken statements or refresh locks to hide drift.
Finish **A → B → C** before the next chapter. Call Codex only when needed.
Details: [SELF_SERVICE.md](SELF_SERVICE.md).
