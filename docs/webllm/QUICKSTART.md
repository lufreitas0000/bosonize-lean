# Daily Chat + Lean checklist

From `/home/lucas/Projects` or `Lean/bosonize-lean`:

```bash
make lean-start-phaseB 15
```

Read/send the prepared packet to Chat. Review its output; request corrections
there until satisfied. Download the complete JSON response to Downloads.

```bash
make lean-finish-phaseB 15
```

Finish automatically finds the matching response, verifies it, records your
approval, integrates it, commits and pushes. It prints the next start command.
Repeat B for the next dependency batch; then start/finish C for promotion.
For the next chapter, use the same commands with A and its chapter number.

If verification fails, send the generated feedback to Chat, review/download the
correction and repeat finish. The primary checkout stays unchanged on check
failure. Optional: `make lean-feedback 15 LEAN_PHASE=B` copies feedback again.

No TOML paths, packet IDs or Git branches need to be copied. See
[SELF_SERVICE.md](SELF_SERVICE.md) for the stable folders, phase checks and recovery.
