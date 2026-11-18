---
title: "CH21 API Reconciliation (BosonizeStubs.Ch21SpinfulModels)"
phase: Phase B
milestone: V1-S9
status: active
owner: lufreitas0000
last_updated: "2026-11-18"
tags: [bosonize-lean, v1-s9, ch21]
depends_on:
  - notes/md/ch21_spinful_models.md
  - notes/appendices/a09_duality_spin_and_umklapp.md
  - Bosonize/Core/A05MultiSpecies.lean
  - Bosonize/Core/A06ChiralFields.lean
  - Bosonize/Core/Ch20CDW.lean
---

# CH21 API Reconciliation (`BosonizeStubs.Ch21SpinfulModels`)

**Date:** 2026-11-18  
**Milestone:** V1-S9 / CH21 Phase B (`BosonizeStubs/Ch21SpinfulModels.lean`)  
**Frozen Core Baseline:** Commit `9fbbdce` (`44` frozen modules under `Bosonize/Core/`, imported via `import Bosonize`)

---

## 1. Purpose

This note reconciles the draft symbols and mathematical assumptions in [`CH21_PARALLEL_WEB_RND.md`](../CH21_PARALLEL_WEB_RND.md), [`ch21_spinful_models.md`](../../../notes/md/ch21_spinful_models.md), and [`a09_duality_spin_and_umklapp.md`](../../../notes/appendices/a09_duality_spin_and_umklapp.md) against the actual frozen Lean 4 exports in `Bosonize/Core/*` for [`BosonizeStubs/Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean).

---

## 2. Reconciled Module & Symbol Map

| Draft / Note Symbol | Live Frozen Core Export (`import Bosonize`) | Notes & Required Adapter Adjustments |
| :--- | :--- | :--- |
| `Ch20.orderParamSC` | `Bosonize.Ch20.orderSC` (`Bosonize/Core/Ch20CDW.lean`) | Plan doc named `orderParamSC`; frozen Core exports `orderSC h b branches x`, `fieldOf h b branches?` / `fieldOf h b ν x`, `scTarget branches Ns`, `scShift branches ν`, `scTarget_apply`, `scResidualOp h b branches x Ns Km`, `ambient_sc_residual`, `projected_sc_residual`, `raiseCharge_lowerCharge`. |
| Multi-species mode & Fock space | `Bosonize.A05` (`Bosonize/Core/A05MultiSpecies.lean`) | `Mode σ h := σ × Ch01.Band (2 * h)`, `speciesOrder h`, `Occupation σ h`, `FockSpace σ h`, `Operators σ h`. |
| Multi-species charges & budgets | `Bosonize.A05`, `Bosonize.Ch07` | `A05.admissible h Ns`, `A05.jointBudget h Ns K := Ch07.speciesBudget h Ns (K : ℤ)`, `A05.jointConfiguration h Ss`, `A05.groundConfiguration h Ns`, `A05.groundKet h Ns`, `A05.ground_mem_budget`, `A05.chargeObservable h ν`, `A05.charge_budget`. |
| Multi-species fermionic & bosonic ops | `Bosonize.A05` | `A05.annihilation h ν k`, `A05.creation h ν k`, `A05.rho h ν m`, `A05.liftedAnnihilation h b ν x`, `A05.rho_adjoint`, `A05.rho_cross_commute`. |
| Chiral orientation & branches | `Bosonize.A06` (`Bosonize/Core/A06ChiralFields.lean`) | `A06.Orientation` (`.right`, `.left`), `A06.Branches σ` (`rightSpecies`, `leftSpecies`, `distinct`). |
| Multi-species Schwinger commutator | `Bosonize.A06.joint_signed_current_commutator`, `Bosonize.Ch10.schwingerCoefficient` | Signature: `joint_signed_current_commutator (h K : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (m n : ℤ) (hmargin : \|m\| + \|n\| + (K : ℤ) + \|Ns ν\| ≤ (h : ℤ)) (v ∈ A05.jointBudget h Ns K) : A02.commutator (A05.rho h ν m) (A05.rho h ν n) v = Ch10.schwingerCoefficient m n • v` where `Ch10.schwingerCoefficient m n := if m + n = 0 then -(m : ℂ) else 0`. |
| Charge lowering & sector projection | `Bosonize.Ch13.lowerCharge`, `Bosonize.Ch14.projection`, `Bosonize.Ch14.projectedMap` | `Ch13.lowerCharge Ns ν = Function.update Ns ν (Ns ν - 1)`; `Ch14.projection h Ns K` and `Ch14.projectedMap h Ns Nt Ks Kt` match `Ch20.projected_sc_residual`. |
| Band & characters | `Bosonize.Ch01`, `Bosonize.A01`, `Bosonize.Ch06Ext` | `Ch01.inBandPredicate L k := -(L : ℤ) < 2 * k ∧ 2 * k ≤ (L : ℤ)`, `Ch01.Band L := {k : ℤ // inBandPredicate L k}`, `A01.integerCharacter`, `A01.canonicalRoot`, `A01.normalization`, `Ch06Ext.BoundaryTwist`, `Ch06Ext.periodicTwist`, `Ch06Ext.twistedCharacter`. |
| Discrete Schrieffer-Wolff (`A10`) | `Bosonize.Core.A10DiscreteSchriefferWolff` | Standalone CH21 Phase A targets `B1–B4` on `A05`/`A06`/`Ch20` first without adding unrequested coupling into frozen `A10` structures; `A10` perturbative connection remains future Phase B/extension territory. |

---

## 3. Canonical CH21 Conventions Enforced in Phase A

1. **Compiler Options (`lakefile.toml`):** Both `autoImplicit = false` and `relaxedAutoImplicit = false` are active workspace-wide. Every variable and universe/type parameter in `BosonizeStubs/Ch21SpinfulModels.lean` must be explicitly bound.
2. **4-Species Carrier Order (`Fin 4`):**
   - `0` = `L↑` (left-moving spin-up)
   - `1` = `L↓` (left-moving spin-down)
   - `2` = `R↑` (right-moving spin-up)
   - `3` = `R↓` (right-moving spin-down)
   - Matching `A05.speciesOrder h` with `0 < 1 < 2 < 3`.
3. **Currents & Schwinger Factor `2m`:**
   - Because `A05.rho h ν m` uses a single signed mode index `m` uniformly across species and `A06.joint_signed_current_commutator` returns `Ch10.schwingerCoefficient m n • v` (with coeff `-m` when `m + n = 0`) for each distinct species `ν` independently (`A05.rho_cross_commute` handles `ν ≠ ν'`), any summed 2-species raw current (charge `ρ_c(m) = ρ_↑(m) + ρ_↓(m)` or spin `ρ_s(m) = ρ_↑(m) - ρ_↓(m)` per chirality, or raw total currents across two branches) adds two independent species commutators of equal sign `(-1)^2 + (+1)^2 = 2` (or subtracted chiral pairs), giving coefficient `2 * Ch10.schwingerCoefficient m n` (`-2m` when `m + n = 0`) under the combined margin hypothesis `|m| + |n| + (K : ℤ) + max(|Ns ν₁|, |Ns ν₂|) ≤ (h : ℤ)`.
4. **Two-Channel Spin-Singlet SC Target (`Ch20` Reuse):**
   - Represent the two singlet pairing channels directly using two `A06.Branches (Fin 4)` configurations in `A06.Branches` `(rightSpecies, leftSpecies)` order (`singletBranchesA := ⟨brRDown, brLUp, _⟩` for `(R↓=3, L↑=0)` and `singletBranchesB := ⟨brRUp, brLDown, _⟩` for `(R↑=2, L↓=1)`) so `Ch20.orderSC`, `Ch20.scResidualOp`, and `Ch20.projected_sc_residual` apply verbatim without re-implementing singlet residual proofs from scratch.
5. **Umklapp Normal-Ordering & Sign Contract:**
   - Normal-ordered real-space Umklapp density sums `(g_U / (2*h)) * ∑_{x : Fin (2*h)} (c†_{L↑}(x) c†_{L↓}(x) c_{R↓}(x) c_{R↑}(x) + h.c.)`.
   - With strict operator ordering `c†_0 c†_1 c_3 c_2` acting on the zero-charge vacuum `|Ω₀⟩` (`N = 0` on all branches) and target `umklappTargetConfig` (charge `(+1, +1, -1, -1)` with holes at band bottom `1 - h`), the Jordan-Wigner / `A05` occupation-parity factor is strictly `(-1)^(8h - 1) = -1`, yielding matrix element `-g_U / (2 * h)^2` (`-1/16` at `h = 2, g_U = 1`; `-1/4` at `h = 1, g_U = 1`).
6. **Witness Budget vs Invariance:**
   - Define `umklappZeroChargeWitness` / `umklappTargetConfig` explicitly as a concrete ket in `chargeSector h (+1, +1, -1, -1)` (with derived excitation energy `2 * (h - 1)` documented in `ch21_umklapp_derivation.md` while `|Ω₀⟩ ∈ A05.jointBudget h (fun _ => 0) 0`), prove zero-charge budget non-invariance constructively from the single isolated `B4` CAR witness evaluation theorem `umklapp_zero_charge_witness_coeff`, and document the `h = 2, L = 4` ground-to-ground selection rule and `|Ω₀⟩`-containing `K ≤ 1` counterexample in `ch21_umklapp_derivation.md`.
