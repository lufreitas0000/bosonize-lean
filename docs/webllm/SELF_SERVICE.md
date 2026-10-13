# Self-service chapter workflow: prepare → A → B → C

You can run this cycle without Codex. Chat drafts candidates; local Git, Python,
Lake and Lean check them. None of these scripts calls an OpenAI model. You own
mathematical review and approval, proof review, prose review and promotion. Your
confirmed separate Chat allowance makes offloading drafts possible; savings
still depend on how much repair they require.

## 1. Setup and command reference

Use Bash in WSL. Python 3.11+, Git, Make, the repository's pinned Lean/Lake and
Mathlib cache must be available. Start from clean, committed inputs.

```bash
export HUB=/home/lucas/Projects
export REPO="$HUB/Lean/bosonize-lean"
cd "$HUB"
make help
make -C "$REPO" help
make status
git -C "$REPO" status --short
make -C "$REPO" lock-check
# First-time/missing Mathlib cache only:
make -C "$REPO" cache-get
```

Run hub commands from `$HUB`; run Lean commands with `make -C "$REPO"`.

| Command | Purpose |
| --- | --- |
| `make chapter-task CHAPTER=15 PHASE=B` | Generate chapter task TOML and exact Core API digest; no model call/compile/freeze |
| `make task-init ARGS="..."` | Generic task generator for subjects outside the chapter presets |
| `make packet SPEC=... COPY=1` | Assemble committed context and copy the prompt; omit COPY if unavailable |
| `make preview PACKET=... RESPONSE=...` | Validate envelope/allowed changes and show diff; no ingestion or compile |
| `make ingest PACKET=... RESPONSE=... MODEL=chatgpt-chat-high` | Compile/audit in isolated worktree; successful candidate gets its own commit |
| `make feedback PACKET=... COPY=1` | Prepare retry prompt from failed verification logs |
| `make -C "$REPO" verify-a PROPOSAL=...` | Compile a Phase A Markdown proposal; audit every data declaration |
| `make -C "$REPO" verify-b TARGETS="..."` | Freshly compile requested staging proofs and dependencies; audit all declarations |
| `make -C "$REPO" verify-c PROPOSAL=...` | Check Phase C Markdown headings; human review decides prose correctness |
| `make -C "$REPO" audit-data TARGETS="..."` | Build selected integrated modules and audit named data; theorem placeholders may remain |
| `make -C "$REPO" audit-axioms TARGETS="..."` | Build selected modules and audit data/theorems; sorryAx is rejected |
| `make -C "$REPO" build-core` / `build-stubs` / `build-all` | Refresh libraries; a staging build can accept placeholders |
| `make -C "$REPO" lock-check` | Check statement/context locks and exact Core file hashes |
| `make -C "$REPO" lock-update` | Add reviewed initial interfaces; refuses changes to existing frozen content |
| `make -C "$REPO" ci` | Full guard tests, lock checks, library builds and verifier regression tests |
| `make -C "$REPO" test-webllm` / `make test-pipeline` | Regression tests when changing tooling |
| `make pipeline-demo` | Disposable demonstration of the transport/verification loop |

`MODEL` is a provenance label you supply, not an API/model selector. Choose effort
in Chat itself. Verification commands are trusted commands in your committed
specification; never adopt a model-supplied shell command without reviewing it.

## 2. Task specifications are generated, not handwritten per file

**One TOML describes one request/batch. It can target several files.** You normally
run `chapter-task` rather than write TOML. Chapter presets cover CH15–21, route
the actual chapter/appendix notes, generate a hash-bound Core API digest, choose
the phase's output and verifier, and keep toolchain/Core manifests locked.

```bash
cd "$HUB"
make chapter-task CHAPTER=15 PHASE=B
```

This prepares `packets/ch15_phase_b_auto.toml` and
`docs/webllm/generated/ch15_phase_b_auto_core_api.md` in Bosonize-Lean. It selects
A06 first because CH15 imports it and A06 still has unproved contracts. After A06
is proved, reviewed and merged, the next B task selects CH15. Preparation checks
source presence, frozen interfaces, Core hashes and dependency order; it does
not establish mathematical truth or compiler acceptance.

Customizations, all optional except actual Phase C evidence:

```bash
# Explicit ID: never overwrite a previous request.
make chapter-task CHAPTER=15 PHASE=B ID=ch15_phase_b_fields
# Explicit group: all placeholders in both complete files must be proved.
make chapter-task CHAPTER=15 PHASE=B ID=ch15_phase_b_joint \
  TARGETS="BosonizeStubs/A06ChiralFields.lean BosonizeStubs/Ch15DualFields.lean"
# Narrow/extend exact Core API selection and add a reviewed report.
make chapter-task CHAPTER=15 PHASE=B ID=ch15_phase_b_retry_scope \
  MODULES="A05MultiSpecies Ch10Heisenberg Ch14Mandelstam" \
  CONTEXT="note/ch15_phase_a_independent_review_2026-10-13.md"
# Later chapter, only after CH15 promotion/freeze:
make chapter-task CHAPTER=16 PHASE=A
```

`CHAPTER_REPO` overrides the repository path. `TARGETS`, `CONTEXT`, `MODULES` and
`EVIDENCE` accept space-separated entries without spaces in individual names.
A default B task takes the first pending dependency module, not an arbitrary
subset of its lemmas. An explicit B group can prove dependencies together.
A task refuses unproved dependencies outside its target group. Sequential A
preparation requires the previous chapter present in frozen Core; this is a
mechanical prerequisite, not proof that all its pedagogical work is complete.

| Change between requests | What to change |
| --- | --- |
| Next chapter | `CHAPTER=16`, then 17…21; source routing changes automatically |
| Phase | `PHASE=A`, `B`, or `C`; output, instructions and checks change |
| Next proof batch / a new request | Use a fresh `ID`; default IDs are never overwritten |
| Specific Lean files | Optional `TARGETS="... ..."`; B only edits those complete files |
| Relevant established APIs | Optional `MODULES="..."` with actual Core basenames |
| Reviews or additional source material | `CONTEXT="..."`; paths must already exist |
| Phase C proof/review evidence | Required `EVIDENCE="note/report.md ..."`; scripts do not fabricate it |

The TOML's `targets` is the response whitelist; `context` is read-only prompt
material; `lean_proofs` lists the B Lean targets; `locked` records immutable
inputs; `verify` contains argv arrays run locally; `timeout` is per command;
`max_packet_bytes` limits assembled prompt size. Review these fields and the
scope paragraph before committing. Generated scope is a starting specification,
so refine it where the actual mathematics requires more precision.

For a different subject, a single generic command can still generate a multi-file
specification. Replace every sample path and task with your actual inputs:

```bash
make task-init ARGS="--repo /absolute/project --id topic_b \
 --phase B --target src/First.lean --target src/Second.lean \
 --context docs/specification.md --verify 'make check' \
 --task 'Prove the approved frozen contracts in both complete files.'"
```

Lean targets need frozen interfaces and a suitable project-specific verifier.
The Bosonize chapter verifier/presets are not universal verifiers for other projects.

## 3. Commit preparation, then generate the packet

For the automatically prepared first CH15 B batch:

```bash
cd "$REPO"
cat packets/ch15_phase_b_auto.toml
# Read the API digest and refine scope/context if needed.
git add packets/ch15_phase_b_auto.toml \
  docs/webllm/generated/ch15_phase_b_auto_core_api.md
git diff --cached
git commit -m "webllm: prepare reviewed CH15 support proof task"
git status --short
cd "$HUB"
make packet SPEC="$REPO/packets/ch15_phase_b_auto.toml" COPY=1
```

The existing hand-tuned `packets/ch15_phase_b_support.toml` is also ready and
contains more specific CH15 proof guidance. You may use that spec directly:

```bash
make packet SPEC="$REPO/packets/ch15_phase_b_support.toml" COPY=1
```

**What `make packet` does:** it reads the committed task, standing/phase
instructions and the explicitly listed context/locked/target files from the
same Git HEAD. It combines their text, roles and hashes into one `packet.md`,
with exact response schema, IDs and trusted verification commands. It also
writes `manifest.json` and `response.example.json` to the printed packet folder
under the hub's ignored `.packets/packets/` directory. Repeated paths are deduplicated.

It does **not** compile Lean, build Lake, execute verifiers, recursively collect
all Core imports, or automatically include all Markdown. Core API context is a
separately generated digest that the task explicitly lists. Proof bodies are
omitted from that digest; full sources explicitly in context/targets stay full.
Different chapter/task specs therefore create different context packets. Every
packet is tied to an exact repository commit. An oversized packet is rejected;
review/narrow the API/context list and recommit before trying again.

## 4. Chat interaction and the common local response loop

Set the variables to the **actual directory printed by packet generation**;
the timestamp/ID changes on every run:

```bash
export PACKET="$HUB/.packets/packets/bosonize-lean/ACTUAL_PRINTED_ID"
export RESPONSE="$PACKET/response.json"
```

Start a fresh Chat conversation for a new phase/batch. Paste the complete packet
(or attach `packet.md`) and ask: “Carry out this packet. Return exactly its JSON
envelope and complete allowed files. If the specification is inconsistent,
explain the concrete obstruction; do not change the frozen contract.” The packet
contains the precise A/B/C request. Chat cannot run your local Lean verifier.

Save the actual returned envelope in `$RESPONSE`; `response.example.json` is a
schema example, not a completed response. Then:

```bash
cd "$HUB"
make preview PACKET="$PACKET" RESPONSE="$RESPONSE"
make ingest PACKET="$PACKET" RESPONSE="$RESPONSE" MODEL=chatgpt-chat-high
```

Alternatively use `CLIPBOARD=1` instead of `RESPONSE=...` if clipboard support works.
A failed attempt preserves its worktree, report and logs. For a compiler failure:

```bash
make feedback PACKET="$PACKET" COPY=1
```

Paste that feedback in the same Chat conversation. Save its corrected complete
response, repeat preview/ingest, and keep using the original packet while the
primary repository HEAD remains unchanged. For envelope/preflight errors with
no attempt log, paste the actual error directly. Never claim the compiler passed
when it did not. A substantive statement conflict needs a documented issue and
reviewed specification correction, rather than proof-only edits.

On success, ingestion prints an accepted branch/commit. It has **not merged it**:

```bash
export ACCEPTED_BRANCH='ACTUAL_PRINTED_BRANCH'
git -C "$REPO" diff HEAD.."$ACCEPTED_BRANCH"
# Read proof/proposal and the actual verification report; then accept it:
git -C "$REPO" merge --ff-only "$ACCEPTED_BRANCH"
make -C "$REPO" ci
```

A changed primary HEAD invalidates earlier packets. Finish/commit review notes
and companions, then regenerate the next packet. Do not push failed candidate
branches as completed work. Save accepted evidence in tracked `note/` or the
companion and commit/push the reviewed checkpoint yourself.

## 5. Phase A: propose, review, integrate, freeze

For a new chapter, after its predecessor is promoted:

```bash
cd "$HUB"
make chapter-task CHAPTER=16 PHASE=A
# Review/commit generated files as in step 3, then:
make packet SPEC="$REPO/packets/ch16_phase_a_auto.toml" COPY=1
```

A returns a Markdown proposal: source map, scope, exactly one Lean block,
companion and review obligations. Data declarations are complete; every theorem
is a one-sorry contract. Preview/ingest invokes the proposal compiler/data audit.
A direct check is also available:

```bash
make -C "$REPO" verify-a PROPOSAL=docs/webllm/drafts/ch16_phase_a_auto.md
```

Review carriers, adjoints, signs, normalization, budgets, hypotheses/margins,
source fidelity and explicit nonzero witnesses. Record verdict, unresolved
findings and exact source hashes. Compiler success does not approve the intended
mathematics. Your documented review is the self-service approval gate; call a
review independent only if a separate reviewer actually performed it.

Manually extract approved declarations into correctly named `BosonizeStubs/`
files, choose actual imports, register them in `BosonizeStubs.lean`, and write the
mirrored companions under `docs/companion/BosonizeStubs/`. This source integration
is not performed by the Markdown importer. Review the integrated source again.
Use your actual chapter/support paths in place of the examples below:

```bash
export TARGETS='BosonizeStubs/ActualSupport.lean BosonizeStubs/Ch16ActualName.lean'
make -C "$REPO" build-stubs
make -C "$REPO" audit-data TARGETS="$TARGETS"
# After mathematical review of all new interfaces:
make -C "$REPO" lock-update
git -C "$REPO" diff -- docs/spec/stub_locks.v2.json
make -C "$REPO" lock-check
make -C "$REPO" ci
```

Inspect the manifest delta: add only the intended reviewed entries, preserve
all old records/Core hashes. `lock-update` refuses changed frozen content;
never bypass refusal with `--accept-changes`. Commit approved source, review,
companions and manifest together. Bind the audit to that committed checkpoint:

```bash
cd "$REPO"
python3 scripts/guards/stub_lock.py --check --strict --baseline-ref HEAD
python3 scripts/guards/core_lock.py --baseline-ref HEAD
git push
```

The hub's `make lock-freeze` is a different whole-file lock mechanism. Use the
Bosonize commands above for its mathematical declaration locks.

## 6. Phase B: complete one dependency batch, then the chapter

CH15/A06 Phase A is already integrated/frozen: 15 complete data declarations and
23 unproved contracts (16 A06, seven CH15). No Phase B completion is claimed yet.
Start with the existing hand-tuned support task, or prepare the automatic B task.
Use the common Chat/local response loop, inspect proofs and merge the accepted
support result. Then:

```bash
make -C "$REPO" verify-b TARGETS=BosonizeStubs/A06ChiralFields.lean
make -C "$REPO" ci
# Commit actual review/companion evidence before generating the next request.
cd "$HUB"
make chapter-task CHAPTER=15 PHASE=B ID=ch15_phase_b_fields
# Review/commit generated spec + digest, then:
make packet SPEC="$REPO/packets/ch15_phase_b_fields.toml" COPY=1
```

The second task now chooses `BosonizeStubs/Ch15DualFields.lean` and includes the
proved A06 dependency. Its local direct audit is:

```bash
make -C "$REPO" verify-b TARGETS=BosonizeStubs/Ch15DualFields.lean
```

The B importer freezes headers, definitions, imports and context. All placeholders
in every returned target must be gone, with no new top-level helpers. The verifier
freshly compiles reachable staging sources in a temporary overlay against checked
immutable Core; treats warnings as errors; checks standard-axiom closure for data
and theorems. Unrelated staging placeholders may remain. A general staging build
can pass with those placeholders and does not establish B completion.

## 7. Phase C: evidence-grounded prose, then local promotion

After every chapter/support proof is accepted and reviewed, save actual reports
and review conclusions in the repository and commit them. Prepare the prose task
while the completed modules still reside in staging:

```bash
cd "$HUB"
make chapter-task CHAPTER=15 PHASE=C \
  EVIDENCE="note/ACTUAL_PROOF_VALIDATION.md note/ACTUAL_PROOF_REVIEW.md"
# Review/commit spec + generated digest; then:
make packet SPEC="$REPO/packets/ch15_phase_c_auto.toml" COPY=1
```

Replace the evidence placeholders with real files. C preparation rejects pending
reachable proofs and missing evidence. Ingestion reruns the B verifier and checks
the Markdown candidate structure. It does not certify prose truth: compare each
claim with the proved scope and reports, preserving reference theory and clearly
identifying remaining formal/conditional/analytic claims. Integrate reviewed
prose into the appropriate chapter/appendix and companion locally.

Follow [freeze_chapter.md](../../.agents/workflows/freeze_chapter.md) for promotion:
move completed modules to `Bosonize/Core/`, update imports and aggregators,
migrate only their lock paths and approved import/context hashes, append their
whole-source Core hashes, move/update companions, and record the exact migration.
The self-service workflow uses your documented review; do not invent agent review.

For CH15, `A06ChiralFields.lean` currently imports `Bosonize`. It must use the
specific Core dependencies after promotion, because importing an aggregator
that now imports A06 would create a cycle. The CH15 import of
`BosonizeStubs.A06ChiralFields` must become the corresponding Core import.
Review these substitutions before recalculating only affected lock records.
Never blanket-regenerate the baseline or replace existing Core hashes.

After the scoped migration, using actual promoted filenames:

```bash
make -C "$REPO" lock-check
make -C "$REPO" ci
make -C "$REPO" audit-axioms \
  TARGETS="Bosonize/Core/A06ChiralFields.lean Bosonize/Core/Ch15DualFields.lean"
# Final aggregator access check (in a temporary directory):
AUDIT_DIR=$(mktemp -d)
printf '%s\n' 'import Bosonize' > "$AUDIT_DIR/Access.lean"
(cd "$REPO" && lake env lean -DwarningAsError=true "$AUDIT_DIR/Access.lean")
rm -r "$AUDIT_DIR"
```

Append actual named `#print axioms` checks to that aggregator test if documenting
specific downstream access. Record outputs and review, commit/push the complete
checkpoint, verify guards against HEAD, and only then start the next chapter's A.
Promotion changes Lean paths/imports, manifests and prose; it remains a reviewed
local operation, not an automatic mathematical approval button.

## What to do now

For the most specific first request, run `make packet` with the existing
`ch15_phase_b_support.toml`, paste it into Chat, and follow step 4. To learn the
new automatic setup first, use `make chapter-task CHAPTER=15 PHASE=B`, review and
commit its generated spec/digest, then generate its packet. Both request the 16
A06 proofs. Choose one request and finish its response/review before moving on.
Call Codex for concrete errors, a mathematical conflict, uncertain migration or
an optional final audit; routine Chat/local verification does not require it.
