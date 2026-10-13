# ChatGPT Chat workflow for the remaining Bosonize chapters

For normal chapter work, use the automated [start/finish workflow](SELF_SERVICE.md):
`make lean-start-phaseB 15`, review/download the Chat response, then
`make lean-finish-phaseB 15`. The runner handles packets, branches, source
integration, checks, locks, evidence, commits and pushes. The lower-level
commands below remain available as background and troubleshooting guidance.

Prepared October 13, 2026. CH15/A06 is the first real task. The current verified
freeze contains 23 Core modules, 793 statements and 632 context/data commands;
fresh `make ci` passed both libraries and 69 guard tests. CH15–21 remain development
targets. This guide does not mark a new chapter as implemented.

## What you do and what the local agent does

Use the Chat tab and its Medium/High effort controls as you described. The pipeline
does not require a model picker or API key. We do not infer the exact model identity
from an effort setting. Suggested effort: High for interface design/review and
difficult proof diagnosis; Medium for routine proof construction and prose editing.
Record the observed interface/effort as `MODEL=chatgpt-chat-high` or
`MODEL=chatgpt-chat-medium`; that label is provenance, not a model API identifier.

You submit the packet and transfer the returned JSON. The Chat model proposes
artifacts using the supplied context. The local agent/compiler reviews, verifies,
integrates and records evidence. Sending a packet does not grant the Chat tab access
to your local checkout or installed Lean environment. Compilation claims need actual
local output. Start a fresh chat for a new phase or independent review; stay in the
phase chat while correcting its response from compiler feedback.

## First real task: CH15/A06 Phase A

The committed task is `packets/ch15_phase_a.toml`. It covers the Chapter 15 portion
of A06: oriented fields, Hermiticity, finite-character kernels on actual budget
inputs, periodic forward differences, and the zero-mode obstruction. The A06
Hamiltonian/normal-ordering material belongs to CH16 and is excluded here.

From the hub root:

```bash
cd /home/lucas/Projects
make packet SPEC=Lean/bosonize-lean/packets/ch15_phase_a.toml COPY=1
```

The command prints a new packet directory and copies its `packet.md` when clipboard
support is available. Paste the full packet into a new Chat conversation. Use High
effort. If clipboard copying is unavailable, open packet.md and copy it manually.
The packet contains the exact source notes, a hash-bound API digest, verification
contract, task, targets, packet ID and base SHA. No private project path alone can
substitute for its content in the Chat tab.

Expected first interaction:

> Implement the Phase A draft described in the packet below. Treat source claims
> critically. Return exactly its JSON envelope with the complete Markdown artifact.
> Do not claim to have run Lean locally. Do not change the scope or oracle.

Paste the packet immediately after that instruction. The model returns one JSON
object with `packet_id`, `base_sha`, and `files`. The only file is
`docs/webllm/drafts/ch15_phase_a.md`. Its Markdown contains the source map, design,
one complete Lean draft block, companion notebook and unresolved review obligations.
Definitions are complete; every proposed theorem is exactly a one-sorry stub.

Save just that JSON as `response.json` beside the generated packet. A single enclosing
json fence is supported. This is a complete-file envelope, not a Git patch or an
unstructured explanation. You can also copy the JSON and use `CLIPBOARD=1` below.

```bash
# Substitute the actual generated directory in both variables.
packet_dir=/absolute/path/printed/by/make/packet
make preview PACKET="$packet_dir" RESPONSE="$packet_dir/response.json"
make ingest PACKET="$packet_dir" RESPONSE="$packet_dir/response.json" MODEL=chatgpt-chat-high
```

The local verifier parses the draft, rejects incomplete data/extra commands,
elaborates a temporary candidate with the installed compiler, and prints fresh data
axioms. It rejects data that indirectly depends on a theorem's sorry. Only the
expected theorem-placeholder warnings are permitted. It reuses the unchanged primary
checkout's existing Core compiler environment; the temporary candidate is outside
guarded source and never becomes a staging module. The primary HEAD must still match
the packet. Neither definitions nor locks are installed by artifact acceptance.

If verification fails:

```bash
make feedback PACKET="$packet_dir" COPY=1
```

Paste the feedback into the same Chat conversation:

> This is the actual local verifier output for your previous response. Correct the
> complete artifact under the same packet ID and base SHA. Preserve the intended
> statements; explain a substantive mathematical conflict instead of hiding it.

Save the corrected JSON and repeat preview/ingest. If the failure is only envelope
syntax, paste the preflight error directly; preflight failures have no worktree/report.
If the repository HEAD changes, generate a fresh packet and use its new identifiers.

After elaboration succeeds, the local agent performs an independent mathematical
review of the actual draft: actual carriers/adjoints, sign and normalization,
species-specific input margins, no-aliasing, nonzero admissible witnesses, and source
fidelity. A separate Chat can provide an additional critique, but a self-review in the
drafting conversation is not the independent gate. The local review must address real
counterexamples and unresolved findings. Only then does the local agent split the
candidate into reviewed staging files/companion, compile them, establish the scoped
v2 interface lock, and commit the Phase A baseline. Build-with-sorry is elaboration
evidence; the phase remains unproved.

## Phase B: prove the reviewed interface

Generate B packets only after the approved staging source and locks are committed.
The local agent prepares a new spec with `phase = "B"`, actual `.lean` targets listed
in `lean_proofs`, required API/oracle context and committed verification commands.
Verification includes both guards, warning-free builds and fresh axiom audits.
The first isolated Lean worktree may need Mathlib dependency/cache preparation;
put the reviewed cache/build steps in the spec and allow an appropriate timeout.

Expected Chat instruction:

> Prove the frozen theorem bodies in this Phase B packet. Preserve all definitions,
> names, binders, hypotheses, conclusions, imports, attributes and context. Return
> complete files. No sorry, admit, sorryAx, native_decide or new top-level declarations.
> Use the supplied compiler diagnostics when correcting the result.

Start at Medium for routine clusters; use High for difficult goals. Return the exact
JSON envelope, preview it, ingest it, and use feedback as in A. An invented Mathlib
lemma is not proof evidence. After three attempts at the same goal, the local agent
records the obstruction and changes the supported approach or requests an independent
diagnosis. A genuine interface defect goes through scoped review before relocking;
the lock is never regenerated to disguise drift.

**Current importer constraint:** every returned Lean file must have all placeholders
eliminated. It does not accept a full file that proves one theorem while leaving
unrelated sorry stubs. Organize small reviewed modules during Phase A or complete a
whole target in the Chat conversation before ingesting it. Do not pretend partial
whole-file responses have passed. Sectional local proof work remains possible, but
it is a separate reviewed integration path from this strict importer.

Importer acceptance is not B→C approval. The local agent independently reviews the
proof/statement meaning, audits all theorem and data dependencies for only
Classical.choice/propext/Quot.sound, records zero placeholders/warnings and commits
the proved checkpoint. A fresh packet must reflect that exact checkpoint.

## Phase C: audit, explain, promote and freeze

The local agent gathers fresh compiler/axiom/guard outputs and the final source.
A `phase = "C"` packet asks Chat for Markdown audit and pedagogical candidates.
Core sources, manifests and aggregators are never returned through this artifact
transport. Use High for audit, Medium for a lecture revision once scope is settled.

Expected Chat instruction:

> Audit the supplied completed CH15/A06 implementation and evidence. Draft the
> complementary lecture and declaration mapping. Preserve the reference exposition,
> state the exact finite constructive realization and its hypotheses, and separate
> unproved physical/analytic interpretations. Flag unsupported claims. Do not invent
> test results, change Lean, or declare promotion complete.

The local agent reviews the audit and lecture diff independently, then performs the
exact promotion: staging-to-Core path migration, reviewed import substitutions,
aggregator update, scoped interface-manifest migration, complete-source SHA freeze,
companion migration and approved lecture synchronization. Old Core hashes remain
unchanged. Fresh CI and axiom checks through `import Bosonize` must pass after
promotion. Commit/push the validated checkpoint and update the roadmap. Only that
completes C. Read `.agents/workflows/freeze_chapter.md` for the precise procedure.

## Repeat across the remaining chapters

| Next item | Phase A attention | Phase B/C acceptance focus |
| --- | --- | --- |
| CH15 + A06 subset | Oriented kernels, periodic additive difference, input margins | Actual adjoints/cancellation, zero-mode obstruction and nonzero admissible inputs |
| CH16 + remaining A06 subset | Normal ordering, finite spatial collapse and normalization | Weighted energy identity; genuine excited witness with all premises; no asymptotic inference |
| CH17 + A07 subset | Raw versus chosen interaction, sea-Wick one-body correction | Preserve exact model choice and energy-shell SW meaning |
| CH18 + A07 subset | Parameter record, pairing transformation, vacuum semantics | Typed budget action and explicit scalar vacuum shift |
| CH19 + A08 subset | Constructed polynomial/quasi-free state | Positivity/normalization and both ordered contractions; distinct from finite-Fock density matrices |
| CH20 + A09 subset | Charge/CCR model, formal coefficient calculus, residuals | Formal correlators and generator duality without analytic evaluation or automatic CAR comparison |
| CH21 + A10 subset | Parity-constrained charges, two Klein factors, conditional leakage | Genuine leakage witness/premises; KT flow and Mott gaps remain separate physical context |

This is the dependency queue, not a promise that every source claim can be proved.
Every chapter gets its own A baseline, B evidence and C promotion checkpoint.

## Current evidence and limits

The actual Chat response has passed elaboration and independent mathematical
review. Its exact declarations are staged and frozen: 16 A06 contracts/13 data
and seven CH15 contracts/two data. All 23 theorem bodies remain unproved.
The first Phase B task is packets/ch15_phase_b_support.toml. Generate a fresh
packet from the committed reviewed baseline; the original Phase A packet is
retained as provenance and is stale for re-ingestion after this integration. Phase A/C artifact
transport extends the existing B-only Lean importer without weakening its proof
locks. A draft-only verifier test is not mathematical approval of the chapter.

Official product context: https://learn.chatgpt.com/docs/models?surface=web and
https://learn.chatgpt.com/docs/web describe model/effort controls where available.
Your observed Chat interface determines what can actually be selected. The effort
allocation above is a workflow recommendation, not a measured model capability claim.

## Phase B support verifier

The A06-first batch uses scripts/webllm/verify_phase_b.py. It checks strict locks
against the matching primary baseline, verifies unchanged Core and dependency
configuration, builds Core, and freshly recompiles the selected target and all
reachable staging dependencies in a temporary olean overlay. It audits every
theorem and named data declaration with warnings treated as errors. It reuses
only Core/Mathlib inputs from the checked primary compiler environment; candidate
proofs never overwrite that environment's staging cache. Thus the seven unrelated
CH15 stubs can remain while the complete A06 target is verified. The CH15 batch
will depend on fully proved A06 and use a new committed packet afterward.

## Self-service mode

The user can run every local check and own the mathematical review and phase
transition decisions without a Codex conversation. See [SELF_SERVICE.md](SELF_SERVICE.md).
Call Codex for issues or a final independent audit as desired. Local verification
commands do not invoke a model; automatic mathematical approval is not provided.

## CH15 Phase B context after the diagnostic reply

Run `python3 scripts/webllm/export_core_api.py` to refresh the comprehensive
reference from the exact frozen Core sources. It checks the complete inventory
and each source hash before writing. The reference includes all Core definitions,
instances and theorem headers in their original command order, plus 16 selected
complete Core proofs and a guide covering every A06 target obligation. This fixes
the missing Ch07/A03 context without changing a Lean declaration or proof.

The A06 start command uses this comprehensive reference as its generated API,
avoids a second narrow digest and inherits the support spec's 400,000-byte packet
budget. This is a local transport limit, not a claim about a particular ChatGPT
model's context capacity. The entire Mathlib library is not included. Context
coverage is not a proof of the outstanding statements.

After committing refreshed inputs, `make lean-start-phaseB 15` creates a new packet
and preserves earlier packets in history. It prints both the stable file to send
to the ChatGPT web chat and the actual created packet path. Use the new packet ID
and base SHA for the next response; the old diagnostic remains historical evidence.
