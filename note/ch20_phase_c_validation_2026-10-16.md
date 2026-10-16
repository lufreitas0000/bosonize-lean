# CH20 Phase C local validation — 2026-10-16

The verified finite CH20 module is promoted to `Bosonize/Core/Ch20CDW.lean`.
Promotion commit `426f402` moves the accepted Phase B source byte-for-byte,
SHA256 `00693b1dafb43d59f185143912d8a78a4303708c637afe97eed45404ad74fd7f`.
Namespace, definitions, imports, statements and proof bodies are unchanged.
The v2 lock moves only its path key, all 33 existing Core hashes are retained,
and the new full-source lock brings the frozen Core total to 34 files.
The Core aggregator imports CH20; staging imports Core.

The companion moves to `docs/companion/Bosonize/Core/Ch20CDW.md`, retaining its
history and appending mapping/review/evidence. The pedagogical note adds a
130-line mathematical constructive-realization section; the original 8207 bytes
are preserved as an exact prefix. Final note SHA256:
`b5b014fc9a612d64f5bfba94ccbc18f7000df7cc13393028ddff06b71ff39b22`.
Author `/root/review_proof`; independent migration/pedagogical reviewer
`/root/audit_locks`: PASS on the exact source/note hashes, no corrections needed.

Fresh evidence is recorded in `docs/verification/ch20-phase-c-20261016/`:
`ci-and-audit.log`, `all-declarations.log`, `core-aggregator.log`, `receipt.json`.
The reproducible `run_audit.py` runs full `make ci`, scans for forbidden proof
tokens, freshly compiles source with axiom output for all 159 declarations,
then imports `Bosonize` and audits all 91 original public data/theorem contracts.
Only propext, Classical.choice and Quot.sound are permitted. Compilation uses
warning-as-error; all checks run in the required namespace sandbox with network
disabled and credentials hidden. Strict guards use the committed promotion
baseline. Existing Core source bytes are unchanged.

An initial CI attempt failed a Phase A verifier test because its compiler-root
selection compared the isolated checkout with primary HEAD. The retry explicitly
sets the supported WEBLLM_COMPILER_ROOT to the same isolated audited checkout;
the verifier retains its exact-HEAD check. No check or sandbox was weakened.
The complete initial failure log is retained separately.

This is local Phase C acceptance of the finite chapter, with 64 original theorem
contracts proved and frozen. Formal vertices, full Wick/state transport,
finite-Fock unitary duality, analytic evaluation and continuum claims remain
separately scoped CH20b or later obligations. No other chapter is started.
No browser-runner transaction, merge to main, push, or remote CI is claimed.
