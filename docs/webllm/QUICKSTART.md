# Daily browser + Lean checklist

From `/home/lucas/Projects` or `Lean/bosonize-lean`:

For guided operation, run `make work`. It makes no model calls. Choose `L` and
the chapter; the menu finds its waiting phase and offers prepare/check/retry/finish.

Direct commands remain available. At the current CH19 B-complete checkpoint:

```bash
make lean-start-phaseC 19
```

Read/send the prepared packet to Chat. Review its output; request corrections
there until satisfied. Download the complete JSON response to Downloads.

```bash
make lean-check 19 LEAN_PHASE=C
```

Check verifies locally without approval, merge or push. If it fails, send the
complete `feedback.md` to the chatbot, download the correction, and repeat check.
After reading the candidate and completing the required review:

```bash
make lean-finish-phaseC 19
```

Finish automatically finds the matching response, verifies it, records your
approval, integrates it, commits and pushes. It prints the next start command.
Repeat B for the next dependency batch; then start/finish C for promotion.
For the next chapter, use the same commands with A and its chapter number.

If verification fails, send the generated feedback to Chat, review/download the
correction and repeat finish. The primary checkout stays unchanged on check
failure. Optional: `make lean-feedback 19 LEAN_PHASE=C` copies feedback again.

No TOML paths, packet IDs or Git branches need to be copied. See
[SELF_SERVICE.md](SELF_SERVICE.md) for the stable folders, phase checks and recovery.

The full browser/document/API/Jules operator guide is at workspace
`orchestrator/docs/HUMAN_WORKFLOW.md`. The chatbot needs only the packet; local
scripts handle file matching, compiler verification, logs and retry construction.
