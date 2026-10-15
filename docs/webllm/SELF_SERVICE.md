# One-command chapter workflow

Run these commands from either `/home/lucas/Projects` or its
`Lean/bosonize-lean` repository. You do not need to name TOML files, packet IDs,
Git branches, Lean targets or evidence reports. The scripts keep those records.

## Your normal cycle

1. **Start the phase.** Its prompt is prepared, committed, pushed and copied to
   the clipboard. Open the printed `packet.md` if clipboard copying is unavailable.
2. **Send the prompt to Chat.** Ask it to carry out the packet and return its
   exact complete-file JSON envelope. Choose Chat's effort yourself.
3. **Read the result.** If you want changes, ask Chat to revise it using the same
   packet. Download the final JSON response to your normal Downloads folder.
4. **Finish the phase.** This records your approval of the downloaded content,
   finds the matching response, runs local checks and performs the integration,
   freeze/migration, evidence recording, merge, commits and push.
5. **Run the next start command printed by finish.** Phase B can have several
   dependency batches; use the same B start/finish commands for each batch.

```bash
# Example: a chapter whose Phase A is not yet done.
make lean-start-phaseA 16
# Read/send prompt, review Chat's result, download its JSON.
make lean-finish-phaseA 16

make lean-start-phaseB 16
# Read/send, review, download.
make lean-finish-phaseB 16
# If another proof dependency/batch remains, repeat those same two commands.

make lean-start-phaseC 16
# Read/send, review the lecture notes/companions and audit, download.
make lean-finish-phaseC 16
```

`make lean-start-phaseA CHAPTER=16` is equivalent to the positional form.
Run one cycle command at a time. Supported chapter presets are 15–21.

## Start now: CH18 Phase B

CH15–17 are complete and promoted. CH18 Phase A is frozen (34 theorem
contracts) and Phase B was started on 2026-10-15. Two equivalent routes produce
the Phase B response; finishing is the same.

**Browser route:** `make lean-start-phaseB 18` prints the packet; send it,
review and download the response.

**API/agent route (from the hub):** proofs are produced one theorem at a time and
accumulate as verified fragments (each compiled with only the standard axioms):

```bash
make api-prove-file FILE=BosonizeStubs/Ch18Bogoliubov.lean   # OpenAI pools → Jules → Gemini fallback
make jules-collect                                          # verify finished Jules sessions
make api-theorem FILE=BosonizeStubs/Ch18Bogoliubov.lean NAME=concrete_bogoliubov_witness CONJUNCTS=1 ALIAS=api-pro
make api-assemble FILE=BosonizeStubs/Ch18Bogoliubov.lean CHAPTER=18   # delivers response.json
```

Status: 33 of 34 theorems proved; `concrete_bogoliubov_witness` has 11 of 12
parts proved (part 8 pending). Then, for either route:

```bash
make lean-finish-phaseB 18
```

Finish runs the full Phase B verifier, CI, locks and evidence recording, exactly
as for a browser response. Afterwards the runner directs you to
`make lean-start-phaseC 18`. Tracked non-blocking review items are in
[review_warnings.md](review_warnings.md).

## Stable files; no intermediate-name bookkeeping

For CH18 B, the convenient location is always:

```text
/home/lucas/Projects/.packets/current/ch18/phaseB/packet.md
/home/lucas/Projects/.packets/current/ch18/phaseB/response.json
/home/lucas/Projects/.packets/current/ch18/phaseB/feedback.md
```

Replace only the chapter number and phase letter when opening another phase.
The stable folder points to the current immutable packet directory. Previous
packets, responses, failed worktrees and logs remain preserved. Internal IDs
and Git commit hashes are generated and recorded automatically.

Finish searches the packet folder, Linux `~/Downloads`, and Windows
`/mnt/c/Users/lucas/Downloads` for JSON/text/Markdown envelopes matching the
current **packet ID and base commit**. It uses the newest matching download,
archives its exact bytes and saves `response.json` automatically. Chat may name
its download however it likes. Plain Lean/Markdown without the packet envelope
is insufficient: the identity prevents an old chapter response being applied.

If your browser downloads elsewhere, set `WEBLLM_DOWNLOADS` once to that folder,
or save the envelope directly as the fixed `response.json` above. No copy/paste
of IDs or branches is needed.

## Corrections and failed checks

A failed finish preserves the primary checkout and the attempted candidate.
The runner prepares `feedback.md` and tries to copy it to the clipboard. Send
that feedback to the same Chat conversation, review its corrected response,
download it again, then repeat the **same finish command**.

```bash
# Optional: copy the recorded feedback again.
make lean-feedback 15 LEAN_PHASE=B
# Read the corrected response and retry.
make lean-finish-phaseB 15
# Optional: see current chapter status.
make lean-status 15
```

Do not restart merely to repair a response; keep the same snapshot and packet.
Repeating start while its snapshot is current reuses the same packet. Repeating
finish after success does not duplicate commits or merges. If you independently
change the primary repository commit, finish rejects the stale response; start
prepares a new packet while preserving the old one. Unrelated uncommitted edits
are never automatically staged or discarded.

## What each finish automates

| Phase | Automatic local work after your approval |
| --- | --- |
| A | Compile proposal and audit data; split the explicitly marked module blocks; create staging files and companions; register imports; add only their interface locks; run integrated data audits and CI; commit/merge/push |
| B | Preserve frozen definitions, headers and imports; require complete proofs for the requested batch; freshly compile reachable dependencies and audit data/theorems; record evidence and companion updates; run CI; commit/merge/push |
| C | Require completed reachable proofs and recorded B evidence; accept reviewed chapter/appendix/companion synchronization; move modules to Core; substitute imports without changing mathematics; migrate only their lock records; preserve existing Core hashes; run CI and fresh axiom/aggregator audits; commit/merge/push |

A's packet tells Chat how to mark module boundaries. You review that layout as
part of the proposal; the script chooses no mathematical decomposition behind
your back. C expands `import Bosonize` to the existing Core imports and rewrites
promoted staging imports, preventing aggregator cycles. It records the exact
migration. Unexpected dependencies or guard failures stop the transaction.

Checks run in isolated worktrees before the primary branch is fast-forwarded.
Passing Lean establishes elaboration/proofs of the written statements. Your
review remains responsible for their intended mathematics and for the prose.
Running finish is the approval action; no separate routine confirmation follows.

By default both start and finish push their scoped commits. `PUSH=0` keeps them
local; `COPY=0` disables clipboard copying. `MODEL=chatgpt-chat-high` is a
provenance label, not a model selector. Local scripts make no OpenAI model calls.
Your Git authentication must already work for automatic push.

For unusual tasks, direct verifiers and manual recovery, see
[MANUAL_REFERENCE.md](MANUAL_REFERENCE.md). The default workflow needs only the
start/finish commands above.
