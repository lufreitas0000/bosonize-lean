# V1-S4 Phase C acceptance — 2026-10-19

**Accepted:** exact finite current-word comparison, through A–B–C.
Stop after S4; S5 has not started. No push or release was performed.

## Implementation

Promoted source: `Bosonize/Core/V1S4FiniteCurrentComparison.lean`.
SHA-256: `3f436b970c78bb5126a18ab0ffc4a523bea61dd855f60b491baf410f96770b3e`.
This is byte-identical to the independently accepted staging source.

Creation of positive weight `m=i+1` maps to `A05.rho h ν (+m)`;
annihilation maps to `A05.rho h ν (-m)`. There is no square-root factor.
The free-algebra homomorphism preserves displayed product order without
asserting global finite-dimensional CCR.

The unnormalized polynomial map sends a monomial to its actual ordered
positive-current partition state on the finite free sea. On the weighted
energy domain `≤K`, its image lies in the fixed-charge total-energy budget and
the span of current partitions using the available modes. Under R2 it has the
exact oscillator Gram form `∏ m^k k!` and trivial restricted kernel. No
surjectivity onto the full budget is asserted when required parts exceed M.

`covered_word_action_contract` proves rightmost-first path intertwining.
The path certificate tracks each active species' energy, local lowering
source margin, every live budget, and a first killed branch. The theorem also
retains `2K+|Nν|≤h`. `covered_word_moment_contract` extracts the vacuum moment;
`covered_dressed_moment_contract` gives the squeezed comparison after the
exact inverse-Bogoliubov free-algebra expansion. Every branch with nonzero
coefficient has its own path certificate.

`uniform_margin_path` derives full coverage with `K=d*M` from word length at
most d and `2*d*M+|Nν|≤h` for each species. Substitution preserves length, so
this wrapper covers every inverse branch as well. There are ordinary/dressed
finite-linear-combination corollaries and a normalized constant theorem.
The combined structural/global margins are sufficient, with no optimality claim.

The elaborating examples cover constants and M=0, unsqueezed contractions,
nonzero squeeze `(c,s)=(5/4,3/4)`, mixed species, and an order-sensitive
fourth-order word. Quadratic and fourth-order regulators are respectively
`h=4,M=1,d=2` and `h=8,M=1,d=4`, with zero admissible charges. Both raw and
dressed fourth-order comparisons are instantiated. The anomalous annihilator
pair demonstrates that raw unsqueezed moments differ from omegaP at nonzero
squeeze.

## Review and validation

Independent reviewer: `/root/s4_diagnosis` (native, read-only).
Integrated mathematical/proof review: **PASS**; pedagogical review: **PASS**.
Exact artifacts, findings and resolutions are recorded in
`independent-review-2026-10-19.md`. The reviewer also approved the byte-preserving
promotion and sole S4 statement-record migration. No required review was
self-approved.

- 53 named lemmas/theorems proved; all eight original contracts complete.
- All 92 named declarations, including definitions and instances, freshly
  audited through the Core aggregator by `phase-c-audit.lean`.
- Only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` in S4's audit.
- Zero placeholders, added axioms, unsafe shortcuts, or target warnings.
- Required namespace sandbox used for compiler, audit and CI commands.
- Fresh Core build and full `make ci` pass after promotion; both libraries,
  strict statement/Core guards, and guard/verifier tests pass.
- All 38 earlier Core files and complete-source hashes are unchanged; 39 now
  frozen. S4 statement/command hashes migrate unchanged with the file path.
- Pedagogical update preserves every baseline byte and adds exactly the
  independently reviewed S4 section. Source/companion links resolve.

Evidence files: `phase-c-build.txt`, `phase-c-ci.txt`, `phase-c-axioms.txt`,
`preservation.json`. Build/CI log trailing whitespace is normalized; complete
axiom output remains untouched. The Phase B receipts remain historical evidence at
commit `ca220eb`; their audit source imports the historical staging path.
The intentional `Fixture.value`/`sorryAx` entry in CI is a verifier negative
test fixture, not an S4 theorem dependency.

The complete post-promotion axiom output is byte-identical to the reviewed
Phase B output, SHA-256
`b5617c59ed2267a35286a63da0953c7a4ff27acc9183376d86e99fab005f376f`.
Post-promotion audit source:
`8efb279b0a3bd3863de34c8187cc0f55eb87c11d52323d43c899e421bd7e5e71`.
Post-promotion statement lock:
`01516b59a555e12533944190bd95ac6cf57e4d19212ae5308586613d9e6511c9`.
Core lock:
`9fd2d31fb66c407370d0dc8ff32191b966be8aaa776646c49f3c53c6119de8ed`.

## Remaining scope

No unresolved S4 acceptance gate remains. The result compares transformed
observables in a free finite sea. It does not construct an interacting finite
ground state, identify omegaP with a finite interacting density matrix, prove
physical field/vertex equality, eliminate projection residuals, establish
full-budget surjectivity or global finite CCR, implement particle-hole
symmetry, or prove analytic/continuum/thermodynamic results. Fixed-regulator
comparison of arbitrary word length is not claimed. S5 remains unstarted.

Proof checkpoints in this resumption: `e4145ed` (inverse expansion/norm),
`5fcda09` (Gram), `b78c131` (word action/moments), and `ca220eb` (final reviewed
proof/audit batch). `9270de5` restores original manifest ordering after a
serialization-only change; final manifests preserve all unrelated records.
The Phase C commit includes the source/lock migration, additive pedagogy,
companion, acceptance receipts and only S4's roadmap edits.
