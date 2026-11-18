---
title: "Chapter 21 Phase A Adversarial W4 Referee Audit & Resolution Record"
phase: Phase A
milestone: V1-S9
status: superseded_by_phase_b
owner: lufreitas0000
last_updated: "2026-11-18"
tags: [bosonize-lean, v1-s9, ch21]
depends_on:
  - BosonizeStubs/Ch21SpinfulModels.lean
  - docs/companion/BosonizeStubs/Ch21SpinfulModels.md
  - docs/plans/v1-s9/ch21_api_reconciliation.md
  - docs/plans/v1-s9/ch21_umklapp_derivation.md
---

# Chapter 21 Phase A Adversarial `W4` Referee Audit & Resolution Record

**Date:** 2026-11-18  
**Reviewer:** `physics-referee` subagent (`4c6418c0-14e4-4836-a472-fd19c02425e4`, W4 adversarial audit)  
**Audited Targets:**
1. [`BosonizeStubs/Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean)
2. [`docs/companion/BosonizeStubs/Ch21SpinfulModels.md`](../../companion/BosonizeStubs/Ch21SpinfulModels.md)
3. [`docs/plans/v1-s9/ch21_api_reconciliation.md`](./ch21_api_reconciliation.md)
4. [`docs/plans/v1-s9/ch21_umklapp_derivation.md`](./ch21_umklapp_derivation.md)

---

## 1. Summary Verdict

- **Lean 4 Contract (`BosonizeStubs/Ch21SpinfulModels.lean`):** **VERIFIED** across all four mathematical blocks (`B1`, `B2`, `B3`, `B4`), with zero F1 (wrong statement / sign / prefactor) and zero F2 (vacuity / hidden assumption) defects. Note one non-blocking sign-convention observation `[W1]` on `singletOrderSC` (`c_{R↓} c_{L↑} - c_{R↑} c_{L↓}`, `-1` times Eq. (21.5) of `notes/md/ch21_spinful_models.md`; kept as-is for Phase A stability, reversible in Phase B if desired without affecting either channel identity).
- **Documentation (`[B1]`–`[B4]`):** Four prose/precision defects flagged by the referee were resolved and verified immediately after the review (see Section 3).
- **Build & Axiom Verification:** `lake build BosonizeStubs.Ch21SpinfulModels` exits `0` with only the single intentional `sorry` warning on `umklapp_zero_charge_witness_coeff` (line 822). Across all `56` exported declarations (`51` `lemma`s + `5` `theorem`s) checked via `#print axioms`, `52` depend strictly on `{propext, Classical.choice, Quot.sound}` (or `{propext}` / `{propext, Quot.sound}`), `1` (`umklapp_zero_charge_witness_coeff`) uses `sorryAx`, and `3` (`umklapp_witness_h2_coeff`, `umklapp_witness_h1_coeff`, `umklapp_zero_budget_not_invariant`) depend transitively on `umklapp_zero_charge_witness_coeff`.

---

## 2. Claim-by-Claim Verification Summary

1. **`B4` Witness & `-g_U / (2h)^2` Sign/Prefactor (`umklapp_zero_charge_witness_coeff`):**
   - Verified `A05.groundKet` vs `umklappZeroChargeWitness`: `DecidableEq` is a `Subsingleton`, and `A02.FockSpace` depends only on `Occupation ι`, so `instDecidableEqProd` vs `A05.localModeDecidableEq h` leaves inner products and equality invariant (Phase B proof will bridge via `Subsingleton.elim` as in `Ch07VacuumBudget.lean`).
   - Verified `precedingCount` ordering matches `A05.speciesOrder h` (`L↑=0 < L↓=1 < R↑=2 < R↓=3`, ascending band indices).
   - Verified `A05.liftedAnnihilation` at `periodicTwist (2*h)` gives `ζ^(+k*x)` and `LinearMap.adjoint` conjugates to `ζ^(-k*x)`.
   - Verified `umklappForwardSite` right-to-left evaluation order `c_{2}(1-h)`, `c_{3}(1-h)`, `c†_{1}(1)`, `c†_{0}(1)` on `S₀`, giving preceding counts `2h + (3h - 1) + 2h + h = 8h - 1` (odd for all `h ≥ 1`, sign `-1`), Fourier phase `ζ^((-1 - 1 + 1 - h + 1 - h)x) = ζ^(-2hx) = 1`, normalization factor `(2h)^{-2}`, spatial sum `(g_U / (2h)) * (2h)`, final matrix element `-g_U / (2h)^2` (`-g_U / 4` at `h = 1`, `-g_U / 16` at `h = 2`), and orthogonal cancellation of `umklappBackwardSite`.
2. **`B1` Raw Chiral Currents (`rhoChargeL/R`, `rhoSpinL/R`):**
   - Verified factor `2 * Ch10.schwingerCoefficient m n` (`-2m` when `m + n = 0`) and cross-commutator cancellation `schwinger - schwinger = 0` for `rhoChargeL/R` with `rhoSpinL/R`, plus explicit non-vacuity witness `h = 2, K = 0, m = -1, n = 1, Ns = 0`.
3. **`B3` Two-Channel Spin-Singlet Pairing:**
   - Verified `singletBranchesA := (brRDown, brLUp)` and `singletBranchesB := (brRUp, brLDown)` shift `(N₀..N₃)` by `(-1, 0, 0, -1)` and `(0, -1, -1, 0)`, preserve `Q_s`, lower `Q_c` by `2`, occupy orthogonal target budgets, and instantiate `Ch20.projected_sc_residual` on both channels (non-vacuous via `Ch20.orderSC_ground_coeff` at `h = 1`).
4. **`B2` Umklapp Self-Adjointness, Diagonal Vanishing & `SpinChargeSublattice`:**
   - Verified exact bijection `branchesToSpinCharge` ↔ `spinChargeToBranches` on the 4-equation mod-4 sublattice, `umklappOp_self_adjoint` (`gU : ℝ`), and `umklappOp_charge_diagonal_zero` across all fixed-charge sectors (non-vacuous at `h = 1, Ns = 0, u = v = groundKet 1 0`).

---

## 3. Resolution of Referee Items `[B1]`–`[B4]`

| ID | Target | Referee Finding | Resolution Applied |
| :--- | :--- | :--- | :--- |
| `[B1]` | `docs/companion/BosonizeStubs/Ch21SpinfulModels.md` line 6 | Reported partial subset count (`22`) instead of full exported declaration count. | Updated to exact verified counts: `56` exported declarations (`51` `lemma`s, `5` `theorem`s), of which `52` (`51` `lemma`s + `umklappOp_charge_diagonal_zero`) are proved axiom-clean, `1` is the isolated `sorry` stub `umklapp_zero_charge_witness_coeff`, and `3` depend transitively on `umklapp_zero_charge_witness_coeff`. |
| `[B2]` | `docs/companion/BosonizeStubs/Ch21SpinfulModels.md` line 16 | Correlated `±/∓` shorthand did not explicitly enumerate all 4 mod-4 sublattice congruences. | Listed all 4 exact congruences from `SpinChargeSublattice` explicitly. |
| `[B3]` | `docs/plans/v1-s9/ch21_umklapp_derivation.md` lines 24, 76, 80, 98 | Line 98 overclaimed `K ≤ 1` non-invariance for arbitrary shifted sectors (ignoring Pauli-blocked filled sectors like `(2,2,2,2)` at `h = 2`); minor `Ch01.Lattice` vs `Fin (2 * h)` drift. | Restricted `K ≤ 1` counterexample statement to charge-boxes/subspaces containing `|Ω₀⟩` and aligned domain notation to `Fin (2 * h)` (`≃ Ch01.Lattice (2 * h)`). |
| `[B4]` | `docs/plans/v1-s9/ch21_api_reconciliation.md` lines 43, 46, 48 | Scratch note residue on singlet channel order, non-existent `umklappZeroChargeWitness_def`, and overstated `jointBudget` proof status vs `chargeSector`. | Cleaned channel tuple order `(brRDown, brLUp)` / `(brRUp, brLDown)`, corrected symbol name `umklappZeroChargeWitness`, clarified `chargeSector` in Lean vs derived `2*(h - 1)` energy in `ch21_umklapp_derivation.md`. |
