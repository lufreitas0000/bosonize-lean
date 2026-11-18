---
title: "CH21 Phase B Adversarial W4 Referee Audit & Runtime Verification"
phase: Phase B
milestone: V1-S9
status: active
owner: lufreitas0000
last_updated: "2026-11-18"
tags: [bosonize-lean, v1-s9, ch21, referee]
depends_on:
  - BosonizeStubs/Ch21SpinfulModels.lean
  - docs/companion/BosonizeStubs/Ch21SpinfulModels.md
  - docs/plans/v1-s9/ch21_api_reconciliation.md
  - docs/plans/v1-s9/ch21_umklapp_derivation.md
  - docs/plans/v1-s9/ch21_phase_a_referee.md
---

# Chapter 21 Phase B Adversarial `W4` Referee Audit & Resolution Record

**Date:** 2026-11-18  
**Reviewer:** `physics-referee` subagent (`91145087-71b3-41d0-8469-44db30055568`, W4 adversarial Phase B audit) + direct coordinator compiler/axiom verification  
**Worktree & Branch:** `/home/lucas/Projects/.worktrees/bosonize-lean-ch21-v1s9-20261118` (`feat/v1-s9-ch21-spinful-models`, branched from `9fbbdce`)

---

## 1. Combined Verdict

- **Mathematical & Lean 4 Static Audit (`physics-referee` `91145087`):** **PASS — zero F1 (wrong statement / sign / prefactor) and zero F2 (vacuity / hidden assumption) defects** across all `1,283` lines of [`BosonizeStubs/Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean) (`56` exported proof declarations: `51` `lemma`s + `5` `theorem`s, `19` `private lemma`s, zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`).
- **Resolution of W4 Blocking Items `[B1]`–`[B3]`:**
  - **`[B1]` Independent Runtime Verification (RESOLVED):** Executed directly inside the worktree:
    * `lake build BosonizeStubs.Ch21SpinfulModels`: exited `0` (`Build completed successfully (3449 jobs)`), zero warnings/errors on `Ch21SpinfulModels.lean`.
    * `python3 scripts/guards/core_lock.py --root .`: exited `0` (`Verified 44 complete Core source file(s)`).
    * Temporary `#print axioms` check via `lake env lean`: exited `0`, checking all `56/56` exported declarations (`51` lemmas + `5` theorems), finding zero `sorryAx` and only standard Lean axioms (`{propext, Classical.choice, Quot.sound}`).
  - **`[B2]` Stub Lock (`docs/spec/stub_locks.v2.json`) (DEFERRED TO HUMAN DRAFT PR REVIEW):** Confirmed `scripts/guards/stub_lock.py --check --strict` flags `BosonizeStubs/Ch21SpinfulModels.lean` as a new unbaselined staging file (`75 unlocked lemma(s), 42 unfrozen command(s)`). Per `stub_lock.py --update` policy (`human-reviewed state only`), the lock baseline is intentionally **not** self-written by automation on the Draft PR branch and awaits human acceptance upon PR merge/promotion.
  - **`[B3]` Relative Markdown Links (RESOLVED):** Updated `../../notes/...` -> `../../../notes/...` in [`docs/companion/BosonizeStubs/Ch21SpinfulModels.md`](../../companion/BosonizeStubs/Ch21SpinfulModels.md) and [`docs/plans/v1-s9/ch21_api_reconciliation.md`](./ch21_api_reconciliation.md).

---

## 2. Verification Details of Phase B Changes

1. **`[W1]` Eq. (21.5) `singletOrderSC` Sign Alignment:**
   - Verified `singletOrderSC h b x := Ch20.orderSC h b singletBranchesB x - Ch20.orderSC h b singletBranchesA x` matches `O_{SSC}(x) := c_{(R,\uparrow,x)} c_{(L,\downarrow,x)} - c_{(R,\downarrow,x)} c_{(L,\uparrow,x)}` in [`notes/md/ch21_spinful_models.md`](../../../notes/md/ch21_spinful_models.md) verbatim.
2. **`B4` Witness Theorem `umklapp_zero_charge_witness_coeff`:**
   - Verified `ket_instDecidableEqProd_eq` (`Subsingleton.elim` on `DecidableEq`), `umklappBackwardSite` orthogonal annihilation on `umklappZeroChargeWitness`, unique active tuple `(1, 1, 1 - h, 1 - h)`, odd CAR permutation count `h + 2h + (3h - 1 + 2h) = 2 * (4h - 1) + 1` (sign `-1`), exact Fourier phase `ζ^(-2hx) = 1`, normalization `(2h)^{-2}`, and spatial sum returning `-((gU : ℂ) / ((2 * (h : ℂ)) ^ 2))`.
   - Verified explicit non-vacuity / F2 guards `umklapp_witness_h2_coeff` (`-gU / 16`), `umklapp_witness_h1_coeff` (`-gU / 4`), and `umklapp_zero_budget_not_invariant` hold constructively without `sorryAx`.

---

## 3. Non-Blocking Roadmap Items (`[W1]`–`[W5]` for Future Phase C / Extension)

- `[W1]` Front-1 metadata updated to `phase: Phase B`, `milestone: V1-S9`, `status: active` on companion/reconciliation/derivation docs (`ch21_phase_a_referee.md` retains note on superseded Phase A `A - B` ordering).
- `[W2]` `singletOrderSC` combined projection theorem on `W = V_{t,1} ⊔ V_{t,2}` (Eq. (21.7)) remains future work beyond current `B3` channel identities.
- `[W3]` Concrete properness witnesses for `B1`/`B2` (analogous to `B4`) may be added during Phase C consolidation.
- `[W4]` `scripts/webllm/audit_axioms.py` should filter private lemmas or use in-file `#print axioms` when auditing `BosonizeStubs.Ch21SpinfulModels`.
- `[W5]` Phase C pedagogical sync in `notes/md/ch21_spinful_models.md` deferred until human Draft PR review and acceptance.
