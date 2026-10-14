# CH17 Phase B: resumable A07 proof checkpoint

Recorded: 2026-10-13T22:38:11.921445-03:00. This is a partial development checkpoint, not runner acceptance or Phase B completion.

## Baseline and saved work

Primary main and the active packet remain at `f464a50f3d07e81153150ca570a4aea3ad90155a`.
Packet: `ch17_cycle_b_a8767708-20261014T011412Z-5d98e758`.
Candidate worktree: `/home/lucas/Projects/.packets/worktrees/ch17-phase-b`.
Candidate branch: `codex/ch17-phase-b`.
Source: `BosonizeStubs/A07InteractionsAndBogoliubov.lean`.
Source SHA-256: `f229dcf0a706dc337d84b13c0cdae278894f9f43d523e287929d9f1713a70915`.
All frozen definitions, imports, instances, statement headers, v2 lock records and Core source bytes are preserved.

## Verified progress

Thirteen of eighteen A07 proof bodies are implemented. Fresh combined compilation with installed Lean 4.35.0-rc4 exited 0. Only five original placeholder warnings remain; no non-placeholder warnings occurred. Fresh #print axioms for all eighteen A07 contracts establishes eleven standard-axiom-only proofs:

- hyperbolic_params_exist
- sea_normal_bilinear_diag
- sea_normal_rho_nonzero
- quartic_sea_wick_zero_repeated
- hopping_mode_kills_ground
- pairing_mode_ground_nonzero
- hopping_mode_self_adjoint
- pairing_mode_self_adjoint
- bogoliubov_creator_adjoint
- bogoliubov_expansion_on_budget
- bogoliubov_ccr_on_budget

The other two implemented bodies, raw_intra_eq_current_sub_correction and raw_inter_eq_hopping, compile but inherit sorryAx from unfinished supporting lemmas. They are not yet complete proofs. Their exact correction sign, zero/positive/negative transfer split and hopping orientation passed independent read-only review by same_ccr. No pairing substitution or finite edge simplification was introduced.

The four user-supplied Claude candidates from attachment 898ba9d9-956d-4b85-9b44-49641fb9dbdf were adopted for scalar existence and the three adjoint results, compiled on their first attempt and freshly axiom audited. Attachment 1969cf81-edbd-424f-b8ba-dd68a825937d supplied mathematically consistent alternative star-based drafts; these alternatives were not needed. Other local proofs were developed by characters (three basic sea-Wick bodies), joint_ccr (four budget bodies), and primary (two wrappers). Unavailable flash/pro models were replaced by the inherited available agent model.

Strict stub guard against the committed packet baseline passes: 872 statements and 867 frozen commands. Core guard passes for all 27 Core source files. Whole Phase B warning-as-error verification and runner acceptance have NOT been attempted because five A07 stubs remain. A10 and CH17 are untouched Phase A stubs (11 and 8 obligations respectively). No Phase C work occurred.

Compiler and axiom evidence is embedded below. Original exploratory logs, snapshots and proof fragments remain under the candidate worktree's scratch directory and are copied to the flat packet folder with a local-phaseB- prefix.

## Remaining A07 obligations and exact next actions

1. sea_normal_rho_zero: identify the zero-transfer sum with relative charge by number-operator basis action and sea occupation counting.
2. quartic_sea_wick_identity: prove the general stable sea-word CAR contraction for opposite validPairs, retaining repeated indices and m=0.
3. species_raw_intra_eq_current_sub_correction: aggregate exact finite edge commutators and finite-distance Wick weights; no global scalar CCR replacement.
4. sea_wick_correction_ground_zero: evaluate number operators on the actual joint sea occupation ket.
5. sea_wick_correction_full_band: compare saturated diagonal weights with 2P-N via basis extensionality/relative charge.

No mathematical defect was established in these contracts; proof infrastructure is unfinished. Once all five are proved, run fresh warning-as-error verification and axiom auditing of the entire A07 module. Serialize the COMPLETE target source into the existing packet's response.json using the unchanged packet ID/base SHA, then accept via make lean-finish-phaseB 17. Only after A07 acceptance prepare the next packet and complete A10, then CH17. The sharper CH17 Sugawara contract needs a new proof under K+|N|<h; installed Core's sufficient 2K+|N|≤h bridge must not silently strengthen the frozen hypotheses.

## Usage pause

Live allowance reported 91% used in the five-hour window (9% remaining), 46% weekly used (54% remaining). The formalizer policy requires stopping new proof work below 10% five-hour or 5% weekly remaining. All agents stopped new proof search and saved their work. Reported five-hour reset: October 14, 2026 at 01:45:22 America/Fortaleza. No reset credit was spent and no automatic wakeup was scheduled. On resumption first recheck usage, primary main/packet identity, candidate checkpoint and strict locks; do not discard this branch or begin from the original placeholders.

## Fresh combined compiler and axiom output

```text
/home/lucas/Projects/.packets/worktrees/ch17-phase-b/scratch/checkpoint-audit.lean:274:6: warning: declaration uses `sorry`
/home/lucas/Projects/.packets/worktrees/ch17-phase-b/scratch/checkpoint-audit.lean:277:6: warning: declaration uses `sorry`
/home/lucas/Projects/.packets/worktrees/ch17-phase-b/scratch/checkpoint-audit.lean:313:6: warning: declaration uses `sorry`
/home/lucas/Projects/.packets/worktrees/ch17-phase-b/scratch/checkpoint-audit.lean:329:6: warning: declaration uses `sorry`
/home/lucas/Projects/.packets/worktrees/ch17-phase-b/scratch/checkpoint-audit.lean:332:6: warning: declaration uses `sorry`
'Bosonize.A07Interactions.hyperbolic_params_exist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.sea_normal_bilinear_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.sea_normal_rho_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.sea_normal_rho_zero' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.quartic_sea_wick_identity' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.quartic_sea_wick_zero_repeated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.species_raw_intra_eq_current_sub_correction' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'Bosonize.A07Interactions.raw_intra_eq_current_sub_correction' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'Bosonize.A07Interactions.sea_wick_correction_ground_zero' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'Bosonize.A07Interactions.sea_wick_correction_full_band' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'Bosonize.A07Interactions.raw_inter_eq_hopping' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.hopping_mode_kills_ground' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.pairing_mode_ground_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.hopping_mode_self_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.pairing_mode_self_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.bogoliubov_creator_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.bogoliubov_expansion_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A07Interactions.bogoliubov_ccr_on_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
```
