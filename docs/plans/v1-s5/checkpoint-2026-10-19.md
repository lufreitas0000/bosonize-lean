# S5 Phase B checkpoint — 2026-10-19

**S5 is incomplete.** Phase A reviewed/locked; Phase B partial; no promotion,
freeze, pedagogical acceptance, push or release. Stop scope remains S5.

Initial baseline `5865ca3`; reviewed interface `803bdf9`; manifest serialization
restoration `c3acc51`. Current source hashes: `checkpoint-hashes.json`.
One independent native reviewer: `/root/s5_review`.

## Verified work

- `V1S5FiniteVectorStates`: selected normalized lowest eigenvector, global
  Rayleigh minimum, complex linear vector functional, normalization, positivity,
  energy evaluation, ambient extension, and generic subtype adjoint identity.
- `V1S5FiniteGroundState`: actual A05 total-energy budget, nonzero sea,
  isometric inclusion, adjoint identities/coordinate projection, full Chapter 17
  pairing Hamiltonian self-adjointness, compression and ground existence.
- `V1S5MomentObstruction`: actual repeated lowering, ambient and compressed
  powers, finite normal moment vanishing, A08 oscillator factorial moment,
  general and constructed-ground raw dictionary discrepancies.
- `V1S5SmallInteractingModel`: admissibility, explicit eight current-word kets,
  a bijection with all actual joint partition labels, and their state bridge.

Scoped build of all four current sources passed: `checkpoint-build.txt`.
The two finite-state modules have zero placeholders/warnings. Across S5 there
are 36 named theorem declarations, 26 completed proof bodies and 10 original
unproved contracts. This is a build with placeholders, not acceptance.

Strict statement locks pass (1304 statements/1370 commands globally). All 39
prior Core sources/hashes and unrelated statement records remain unchanged.
Initial Phase A data audit covered all 19 original data declarations with
permitted standard axioms only. Fresh complete post-amendment axiom/dependency
audits remain pending; do not infer them from the earlier data audit.

## Open obligations

1. `raw_obstruction_witness`: a concrete specialization has a conversion
   heartbeat obstruction. General obstruction is proved; failed specialization
   is preserved in `.scratch/v1-s5/raw-witness-failed-candidate.txt` and
   `moment-batch5.txt`. The original staging placeholder remains.
2. Nine small-model contracts: orthonormality, completeness, full matrix action,
   complete spectral basis, global ground minimum, both selected moments and
   both exact discrepancies. None is claimed proved.
3. Complete fresh axioms/dependencies, zero warnings/placeholders, independent
   final proof review, full integration/CI, promotion/freeze and pedagogical
   synchronization/review. No Phase C gate has passed.

The isolated small-label proof passed (`.scratch/v1-s5/small-label8.txt`).
The orthonormality experiment in `small-gram.lean` is incomplete; its second
diagnostic shows scalar normalization goals of the form `4-2*(sqrt(2))²=0`,
after the partition products reduce. Preserve the existing successful helpers.

The reviewer approved the exact source split and additions, preserving all 19
original definitions and original conclusions. Generic finite-state code must
be a module importing Rayleigh; the physical file stays non-module because
frozen Ch17 is non-module. Both now build. A generic abstract-space inclusion
identity resolved costly concrete instance conversion; no carrier was changed.

## Usage stop and resumption

Five-hour allowance reached 9% remaining (weekly 15%), below the adopted 10%
cutoff. New proof work stopped. The reported five-hour reset is October 19,
2026 at 17:08:01 America/Fortaleza. No reset credit, paid provider or automatic
restart was used. Recheck live allowance, HEAD/status and locks before resuming.
Resume the witness and small-model proofs, then all B/C gates. Do not start S6.
