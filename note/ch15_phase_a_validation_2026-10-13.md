# CH15/A06 reviewed Phase A validation — October 13, 2026

The actual Web-Chat response was accepted twice with identical response SHA-256
`a991716358c7a3f3757678c7223370782c4bf6466842f380b1fb54779f897455`.
Commit 0d19c9d was integrated by fast-forward; the duplicate branch is preserved.

The exact independently reviewed declarations are staged in
BosonizeStubs/A06ChiralFields.lean and BosonizeStubs/Ch15DualFields.lean.
The split preserves all mathematical source text, names, statements and data;
CH15 imports its A06 support. Independent review PASS and exact hashes are in
ch15_phase_a_independent_review_2026-10-13.md. Numerical oracle evidence is
reproducible and explicitly limited to the concrete finite-ground parameter case.

There are 15 complete data declarations and 23 one-sorry theorem contracts:
A06 has 13 data/16 stubs; CH15 has two data/seven stubs. Fresh staged-data axiom
auditing passes all 15 dependencies with only standard axioms and no sorryAx.
No new theorem is proved and no Core promotion has occurred.

Only the two reviewed staging entries were added to the v2 interface manifest;
every prior record and all 23 complete-source Core hashes are unchanged. Strict
checks now cover 816 statements and 657 commands (793 statements remain Core).
Full make ci passes 69 guard tests, both libraries (Core 3408, staging 3411 jobs),
and six real compiler/verifier tests. Staging emits exactly 23 expected sorry
warnings; these are permitted Phase A placeholders, not proof completion. The
pre-existing CH13 tactic suggestion is informational.

Phase B uses a complete-target batch for the 16 A06 contracts first. The committed
spec is packets/ch15_phase_b_support.toml. Its verifier freshly compiles candidate
staging/dependency oleans in a temporary overlay, checks frozen baselines and
standard axiom closure, and never uses a stale staging olean as proof evidence.
Tests establish dependency ordering, cycle rejection, fresh dependent compile,
and rejection of an unproved dependency. The seven CH15 contracts await a later
packet based on the actually completed A06 checkpoint. Native Lean MCP is not
exposed here; installed Lean/Lake compilation supplied the checks.

The validated source/notebooks/locks are committed together before proof edits.
After commitment, rerun the strict guards against that exact Git reference and
retain its commit in the phase transition report. No mathematical scope approval
or extra human confirmation is required beyond the existing review and user
instruction to freeze and proceed to Phase B.
