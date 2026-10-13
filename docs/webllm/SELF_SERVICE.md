# Self-service Chat + local verification

For the short daily checklist, use [QUICKSTART.md](QUICKSTART.md).

The user can run this workflow without a Codex conversation. Chat drafts and
revises candidates; local Python/Git/Lean commands check them. These commands do
not call an OpenAI model. The human owns mathematical review, scope decisions,
interface approval and promotion. A separate Chat critique can help review but
does not turn an unexamined specification into a mathematically approved one.

The user confirmed that their plain Chat allowance differs from Codex/Work.
Drafting there can preserve Codex/Work allowance, provided repair/review overhead
does not dominate. This is user-reported account behavior, not a measured saving
or a claim that ChatGPT Work has separate usage from Codex.

## Current starting point

CH15/A06 Phase A is independently reviewed, integrated and frozen at `6e88812`.
There are 15 complete data declarations and 23 unproved contracts: A06 16, CH15 7.
Start with `packets/ch15_phase_b_support.toml`. Core remains unchanged.

From the hub:

```bash
cd /home/lucas/Projects
make packet SPEC=Lean/bosonize-lean/packets/ch15_phase_b_support.toml COPY=1
```

Paste the printed packet into Chat, save the actual JSON beside it and run:

```bash
make preview PACKET=/actual/packet/directory RESPONSE=/actual/response.json
make ingest PACKET=/actual/packet/directory RESPONSE=/actual/response.json MODEL=chatgpt-chat-high
```

The generated packet supplies the IDs and precise complete-file target. On a
verifier failure, `make feedback PACKET=/actual/packet/directory COPY=1` builds
a retry prompt. Preflight errors can be pasted directly. Never reuse a packet
after the original repository HEAD changes; regenerate from the new checkpoint.

## Accept a Phase B result yourself

1. Read the verifier log/report and inspect the actual proof diff on the branch
   printed by ingestion: `git -C Lean/bosonize-lean diff HEAD..<branch>`.
2. Check that only the requested proof bodies changed and that the proof remains
   meaningful. The importer already preserves headers/data and the verifier
   checks fresh compilation, no placeholders, warnings and standard axioms.
3. Merge the reviewed branch with `git -C Lean/bosonize-lean merge --ff-only
   <branch>`. Use the actual branch name, not the placeholder text here.
4. Run `make -C Lean/bosonize-lean ci` to refresh the primary build and check the
   complete project. While A06 is done and CH15 is still pending, the seven
   unrelated CH15 placeholders are expected; no completed target may retain one.
5. Update the companion/roadmap with actual evidence and commit/push that scoped
   checkpoint. Then prepare the CH15 proof packet from its actual dependency state.

The A06 verifier compiles target/dependency sources freshly in an isolated temporary
overlay against checked immutable Core. It rejects an unproved reachable dependency;
it does not reject unrelated staging placeholders. A complete target must be proved
before this strict importer accepts it. Do not mark the whole chapter Phase B complete
until both A06 and CH15 and their audits/reviews are complete.

## Prepare a later Phase A yourself

Use `make task-init` with `--phase A` to generate a reviewed-task template; see
CHAT_WORKFLOW.md and llm/PROTOCOL.md. Select the actual chapter/appendix source,
required existing Core APIs and precise scope. The current API-export script's
module list is CH15-specific; adapt it or include the relevant complete source
files as context. Commit inputs/spec before packet generation.

Phase A returns a Markdown proposal only. Preview/ingest invokes its configured
verifier, which compiles the proposal and audits data. Read the mathematical
contracts critically: carriers, signs, order, true adjoints, hypotheses/margins,
source fidelity and actual nonzero witnesses. Record your review verdict and
source hashes, including unresolved findings. In this self-service workflow,
your documented mathematical review supplies the approval gate; a compiler
pass alone does not. Do not claim an independent agent reviewed it if none did.

Extract the reviewed Lean declarations into staging, add appropriate imports to
BosonizeStubs.lean, and compile the modules. Freshly audit every staged data
declaration with `#print axioms` after building; only Classical.choice, propext
and Quot.sound are permitted and no data may depend on sorryAx. Record that
output in the companion. The proposal verifier checks this already, but changes
during integration require checking the integrated source again.

For an initial interface freeze, after all new staging entries have been reviewed:

```bash
cd /home/lucas/Projects/Lean/bosonize-lean
python3 scripts/guards/stub_lock.py --update
git diff -- docs/spec/stub_locks.v2.json
python3 scripts/guards/stub_lock.py --check --strict
python3 scripts/guards/core_lock.py
make ci
```

Inspect the full manifest delta: only intended reviewed entries may be added;
old entries/Core hashes must stay unchanged. The update command refuses changed
frozen content. Do not use --accept-changes to bypass that refusal. Commit the
reviewed source/notebook/manifest together before requesting proofs; then run
the guards with `--baseline-ref HEAD` to bind checks to the committed baseline.

## Complete Phase C yourself

The mechanical process is specified in `.agents/workflows/freeze_chapter.md`.
Follow its exact migration steps after completed proofs, zero warnings/placeholders,
fresh standard-axiom closure and your mathematical/proof review:

1. Plan source moves and review required staging-to-Core import substitutions.
2. Move completed modules to Bosonize/Core without changing mathematical
   declarations, names, namespaces or proof bodies; update both aggregators.
3. Migrate only their interface-lock paths and reviewed import/context hashes.
   Preserve every other lock record. A blanket regenerated baseline is not review.
4. Append complete-source SHA-256 hashes to docs/spec/core_locks.json without
   replacing old hashes. Move/update companion notebooks.
5. Use an evidence-grounded Phase C Chat packet for lecture/audit candidates.
   Review the actual prose for source preservation and exact proved scope.
6. Run full CI and fresh axiom audits through the Core aggregator. Record the
   actual results, commit/push the checkpoint, then verify both guards against it.

This promotion is currently a careful manual procedure; there is no one-command
automatic promotion or automatic mathematical approval. You can carry it out
without Codex, using the instructions and ordinary Git/file tools. Call Codex
when a failed guard, mathematical conflict, difficult proof or uncertain migration
needs assistance, or for a final independent audit.

## Stop conditions

Do not freeze a false/unresolved statement, silently alter a locked definition,
weaken a theorem to get a pass, promote incomplete proofs or equate a successful
build with physical correctness. Record obstructions before changing definitions.
Compiler errors belong in Chat feedback; substantive conflicts need a reviewed
specification correction and a new committed packet. Keep phase evidence and
checkpoints so assistance can resume from exact files rather than reconstructed history.
