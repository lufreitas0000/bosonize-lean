# CH20 Phase B resume review — 2026-10-16

Status: independent reviews completed; integration and acceptance interrupted by disappearance of the existing worktree. No Phase B acceptance or Phase C promotion.

## Inspected checkpoint

Worktree: `/home/lucas/.codex/worktrees/ch20-phase-b/bosonize-lean`.
HEAD: `0cfbf0c0b56ed020be89ac5be6537b994e702c6c` (detached).
Initial status: modified `BosonizeStubs/Ch20CDW.lean`, modified `docs/spec/stub_locks.v2.json`, untracked `.scratch/`.
Canonical source SHA256 independently recorded: `a7168fd19c5e72c0f7d1371a1b67b83e827030dcbc75e5e544d9a9008b64106d`.
Scratch `.scratch/ch20_nonzero.lean` SHA256: `89a70ed3fd53af44e6e897b3b332a58d8e78a5bc5a68daff6659854ef0f69f9e`.
The canonical source had one remaining actual placeholder, in `concrete_discarded_channel_nonzero` at line 2169. The cutoff-zero theorem was proved.

## Independent proof review

Reviewer `/root/review_proof`: PASS for the scratch coefficient argument and adaptation to the frozen ground-vector theorem, conditional on fresh integrated compilation/axiom audit.

For h=2, zero-charge seas occupy modes {-1,0}. Removing (L,-1) leaves {0}, charge -1 and excitation 1; intermediate cutoff zero discards it. Creating (R,+1) gives right ground occupation {-1,0,1}, charge +1 and excitation zero. The resulting target occupation has total excitation one and is admitted by target cutoff one. Equality with that occupation forces the unique pair k=-1,p=+1, preventing cancellation. The coefficient is a product of nonzero normalization, Fourier characters and fermion signs, with correct adjoint conjugation/order.

Fresh primary and reviewer Lean MCP diagnostics on the scratch source: success=true, partial=false, timed_out=false, no failed dependencies, no errors or sorry diagnostics; three unused-simp-argument warnings at line 370 in `rightSpecies_residual_m1`. This helper IS in the proof dependency closure. Remove redundant arguments, rather than suppressing the linter.

Scratch `concrete_nonzero_from_inner` proves the map nonzero; the canonical contract proves its value on groundVector nonzero. Preserve the canonical statement and use the coefficient proof directly: assume zero output, apply Subtype.val, change the resulting equality to projected residual acting on groundKet, then apply its inner product with the witness ket to contradict the coefficient lemma.

Minimal local integration closure:
- Reuse canonical targetZeroMn, targetZeroM0, targetZeroOccupation, targetZeroSpeciesBridge, ground_memX, targetZeroLeftSpeciesOccupation/Excitation, targetZeroErased_not_mid_budget, discardedResidualDoubleExpansion, inner_fsumX, inner_if_zeroX, sum_single_pairX.
- Local let m1, residual_m1_g, residual_m1_f.
- Local have proofs from scratch: speciesEraseBridge, speciesInsertBridge, residual_m1_pair_unique, rightSpecies_residual_m1, residual_m1_target_budget, mapIf, inner_zero_ifX, residual_m1_inner_expand, residual_m1_coefficient_nonzero.
- Reuse active canonical targetZeroMode/Pair instances; do not duplicate generic expansion helpers or unused scratch declarations.

## Independent lock audit

Reviewer `/root/audit_locks`: strict working-manifest and committed HEAD checks FAIL. Existing modified lock covers Pi.Bounds import and ten omit prefixes but omits helper additions.

At the recorded canonical hash, all original non-lemma commands are retained unchanged, all 64 original lemma contracts retained; ten header differences are solely `omit [Fintype σ] in` prefixes. Added: 47 private helper lemmas, 18 local order/DecidableEq instances derived directly from A05, three private occupation definitions, four balanced helper sections and a τ variable. Pi.Bounds supplies Real.pi_gt_three in the concrete μ counterexample. No Core/dependency source changes in git diff. Independent reviewer approves these additive scoped interface amendments in principle, conditioned on fresh elaboration/axiom audit and final-hash recheck. No complete lock amendment was made in this turn. Core guard against HEAD passed for 33 complete Core files.

Need complete independently reviewed CH20-only manifest amendment; compare all unrelated records byte/structurally unchanged, commit reviewed baseline and run strict verification against it before canonical proof edits. No silent blanket regeneration.

The Phase B verifier chooses phase_a.compiler_root(repo) and that checkout's HEAD for its strict baseline. Check this behavior before running it on an isolated amended baseline; never weaken the baseline guard to accommodate differing checkout HEADs.

## Interruption

A separate integration candidate/script were written to `.scratch/ch20_integrated.lean`, `.scratch/nonzero_body.txt`, `.scratch/integrate_nonzero.py` in the original worktree, and compiler validation was started with output redirected to `.scratch/integrated-diagnostics.log`. No result was obtained. The canonical source was not edited by this turn, and nothing was staged or committed.

At approximately 15:46 Fortaleza time, the entire `bosonize-lean` child disappeared from the worktree parent directory. Subsequent shell cwd creation failed; explicit shell from `/` worked and confirmed the child absent. `git worktree list` no longer included it, and the app artifact list was empty. Lean MCP reported the candidate path absent. The compiler process ended with exit 1 and no recoverable captured output. Cause is unknown; no tool in this turn removed or archived the worktree. User was asked whether another chat moved/archived/deleted it. The parent directory remains empty. The original base commit still exists in Git.

Do not recreate at that path or overwrite a recovered checkpoint before resolving its location/state. The primary checkout contains unrelated manuscript/governance edits; preserve them. This report is the only surviving repository file deliberately added by this turn outside the disappeared worktree.

Remaining: locate/recover the original uncommitted checkpoint; integrate adapted proof; resolve actual compiler warnings/errors; complete all declaration/data transitive axiom checks (only propext, Classical.choice, Quot.sound), strict committed lock/Core guards, fresh chapter/build/required runner evidence, companion update and atomic Phase B commit. Stop at Phase B as requested. No provider calls, push, or Phase C work were performed.
