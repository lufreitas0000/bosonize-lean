# Historical CH16 resumable checkpoint — 2026-10-13

Superseded: the authorized A–B–C cycle completed at `5fbb9bf`. See [final validation](ch16_phase_c_validation_2026-10-13.md). The following preserves the earlier paused state and resumption instructions.

User scope: repair supplied CH16 drafts and finish A–B–C. The full request is
not complete. Phase A accepted, merged and pushed at b56b47c; Phase B and C
remain unaccepted and unstarted by the runner.

Independent reviewer /root/characters passed all six A07 and thirteen CH16
contracts with 29 data declarations. The earlier finish was interrupted, not a
mathematical failure. Retried staging build, data-axiom audit, both strict guards
and CI passed. Existing 25 Core files remain unchanged. Approved interfaces
and definitions are frozen; do not regenerate locks to accommodate proofs.

## Saved proof work

[Candidate archive](ch16_phase_b_candidates_2026-10-13.json) contains full target
files with only proof-body substitutions, approved baseline source hashes and
actual compiler output. These candidate interfaces match the approved locks.
A combined scratch compile exits 0: ten declarations have only propext,
Classical.choice and Quot.sound. A07's six proofs independently compile as a
complete module with zero warnings. Four CH16 proofs are independently complete:
field_chiral_identity, excited_ket_mem_budget, excited_ket_nonzero and
concrete_dispersion_gap. The gap proof is exact primitive-root algebra.

first_mode_error_zero, error_nonzero_witness and concrete_excited_error_witness
have compiled bodies but inherit sorryAx from single_mode_error_eigenvector;
they are NOT complete proofs. Six unchanged main obligations remain:
chiral_spatial_collapse_on_budget, field_weighted_on_budget,
field_weighted_after_excursion, error_weighted_on_budget, ground_error_zero,
and single_mode_error_eigenvector. The last two field/error consequences can
be derived after actual spatial collapse and eigenvector proofs.

Accepted primary staging sources still contain all 19 original proof stubs.
No partial batch was imported or promoted. The complete A07 candidate is ready
for fresh verification against a newly generated Phase B packet. Candidate
scratch files and input provenance remain at
/home/lucas/Projects/.packets/worktrees/ch16-local-abc/scratch/.

## Next action

Recheck current allowance and Git/locks, then make lean-start-phaseB 16
MODEL=codex-local COPY=0. It should select A07 first. Load the archived A07 file
at the NEW packet base, run make lock-check and make verify-b for A07, serialize
its actual complete contents with new packet identifiers and accept through the
runner. Then generate the CH16 packet and complete its remaining dependency
cluster. Fresh combined compiler/axiom verification and CI precede Phase C;
independent pedagogy review and exact promotion/locks follow. Preserve existing
Core, all approved statements and source reference material. Do not start CH17.

## Usage-policy stop

Live account reading: 91% used / 9% remaining in the five-hour window, 31% used
in the weekly window. The formalizer's default threshold is below10% remaining.
New proof search/batches/transitions stopped; the already-running Phase A
transaction was allowed to finish, and existing work was preserved. Reported
five-hour reset: October13,2026 at20:16:10 America/Fortaleza. No reset credits
were used and no automatic wakeup was authorized or scheduled.
