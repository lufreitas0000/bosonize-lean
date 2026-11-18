# Mirrored Companion: `BosonizeStubs.Ch21SpinfulModels` (Chapter 21 Phase B)

**Lean Module:** [`BosonizeStubs/Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean)  
**Reference Notes:** [`notes/md/ch21_spinful_models.md`](../../../notes/md/ch21_spinful_models.md), [`notes/appendices/a09_duality_spin_and_umklapp.md`](../../../notes/appendices/a09_duality_spin_and_umklapp.md)  
**API & Derivation Notes:** [`ch21_api_reconciliation.md`](../../plans/v1-s9/ch21_api_reconciliation.md), [`ch21_umklapp_derivation.md`](../../plans/v1-s9/ch21_umklapp_derivation.md)  
**Phase Status:** Phase B Complete (`lake build BosonizeStubs.Ch21SpinfulModels` succeeds with zero warnings and zero `sorry`s; all `56/56` exported declarations (`51` `lemma`s, `5` `theorem`s) are proved axiom-clean on `{propext, Classical.choice, Quot.sound}`).

---

## 1. Carrier Conventions & Physical Correspondence

| Convention | Lean Realization | Mathematical Meaning |
| :--- | :--- | :--- |
| 4-branch index | `SpinBranch := Fin 4` (`brLUp := 0`, `brLDown := 1`, `brRUp := 2`, `brRDown := 3`) | Canonical lexicographic order `L↑ < L↓ < R↑ < R↓` matching `A05.speciesOrder h`. |
| Macroscopic tuple | `SpinChargeTuple` (`qc, qs, jc, js : ℤ`) via `branchesToSpinCharge` | `qc = N_{L↑}+N_{L↓}+N_{R↑}+N_{R↓}`, `qs = N_↑ - N_↓`, `jc = N_R - N_L`, `js = (N_{R↑}-N_{R↓}) - (N_{L↑}-N_{L↓})`. |
| Integer sublattice | `SpinChargeSublattice q` / `ChiralSpinChargeParity qc qs` | Exact mod-4 congruences `(qc + qs - jc - js) % 4 = 0`, `(qc - qs - jc + js) % 4 = 0`, `(qc + qs + jc + js) % 4 = 0`, and `(qc - qs + jc - js) % 4 = 0`, plus per-chirality mod-2 congruence `(qc + qs) % 2 = 0` recovering `(N_↑, N_↓) = ((qc+qs)/2, (qc-qs)/2)`. |
| Chiral spin/charge currents | `rhoChargeL`, `rhoSpinL`, `rhoChargeR`, `rhoSpinR` | Sums/differences `A05.rho h ν₁ m ± A05.rho h ν₂ m` on same-chirality spin pairs `(0, 1)` and `(2, 3)`. |
| Two-channel singlet SC | `singletBranchesA := (R↓, L↑)`, `singletBranchesB := (R↑, L↓)`, `singletOrderSC` | Reuses frozen `Bosonize.Ch20.orderSC` and `Ch20.projected_sc_residual` across two spin-singlet channels `A` and `B`, with `singletOrderSC := Ch20.orderSC singletBranchesB - Ch20.orderSC singletBranchesA`. |
| Real-space Umklapp | `umklappForwardSite`, `umklappBackwardSite`, `umklappOp`, `periodicUmklappOp` | `(g_U / (2h)) ∑_{x : Fin (2h)} (c†_{L↑}(x) c†_{L↓}(x) c_{R↓}(x) c_{R↑}(x) + h.c.)` at `Ch06Ext.periodicTwist (2*h)`. |
| `B4` target state | `umklappZeroChargeWitness h hh := A02.ket (umklappTargetConfig h hh)` | Occupations `groundConfiguration h 1` on `L↑, L↓` (`+1`) and `(groundConfiguration h 0).erase (1 - h)` on `R↑, R↓` (`-1`). |

---

## 2. Exported API, Hypotheses & Verification Inventory

### Section 1: Four-Branch Carrier & Parity Sublattice (`A1`, `B1`)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `SpinBranch`, `brLUp`–`brRDown` | `abbrev`/`def` | — | Complete (0 `sorry`) | Canonical `Fin 4` indices `(0,1,2,3)` + pairwise inequality lemmas (`by decide`). |
| `branchesToSpinCharge`, `spinChargeToBranches`, `SpinChargeSublattice` | `def` | — | Complete (0 `sorry`) | Exact integer map `(N_{L↑}, N_{L↓}, N_{R↑}, N_{R↓}) ↔ (Q_c, Q_s, J_c, J_s)`. |
| `branchesToSpinCharge_mem_sublattice`, `spinCharge_left_inv`, `spinCharge_right_inv` | `lemma` | `SpinChargeSublattice q` for right inverse | Proved (0 `sorry`) | Constructive bijection between `(Fin 4 → ℤ)` and the mod-4 parity sublattice. |
| `chiral_spinCharge_recover` | `lemma` | `nUp nDown : ℤ` | Proved (0 `sorry`) | `(qc+qs)%2 = 0` and `(qc+qs)/2 = nUp`, `(qc-qs)/2 = nDown` matching Appendix A09. |

### Section 2: Sector Orthogonality & Observables (`B1`)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `chargeSector h Ns`, `jointBudget_le_chargeSector` | `def`/`lemma` | `h : ℕ, Ns : SpinBranch → ℤ` | Proved (0 `sorry`) | Full charge sector `{S \| ∀ ν, relativeCharge S ν = Ns ν}` containing `A05.jointBudget h Ns K`. |
| `distinct_charge_sectors_orthogonal`, `distinct_charge_budgets_orthogonal` | `lemma` | `Ns₁ ≠ Ns₂` | Proved (0 `sorry`) | Inner product vanishes between distinct branch-charge sectors / joint budgets. |
| `mem_chargeSector_iff_eigen`, `charge_commutator_maps_sector` | `lemma` | `∀ ν, commutator (chargeObservable ν) A = (q ν) • A` | Proved (0 `sorry`) | Joint eigenspace characterization and automatic sector shift `Ns ↦ Ns + q` from charge commutators. |
| `totalChargeObservable`, `totalSpinObservable` (+ `_self_adjoint`, `_budget`) | `def`/`lemma` | `v ∈ A05.jointBudget h Ns K` | Proved (0 `sorry`) | Self-adjoint total charge `Q_c` and total spin `Q_s` observables with eigenvalues `qc, qs` on every budget. |

### Section 3: Raw Chiral Currents & `2m` Schwinger Algebra (`B1`)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `rhoChargeL/R`, `rhoSpinL/R` (+ `_adjoint`) | `def`/`lemma` | `h : ℕ, m : ℤ` | Proved (0 `sorry`) | `(ρ_{χ,c/s}(m))† = ρ_{χ,c/s}(-m)`. |
| `rhoChargeL_commutator`, `rhoSpinL_commutator`, `rhoChargeR_commutator`, `rhoSpinR_commutator` | `lemma` | `0 < h`, `v ∈ A05.jointBudget h Ns K`, **both** spin margins `\|m\| + \|n\| + K + \|Ns ν\| ≤ h` | Proved (0 `sorry`) | `[ρ_{χ,α}(m), ρ_{χ,α}(n)] v = (2 * Ch10.schwingerCoefficient m n) • v` (`-2m • v` when `m + n = 0`). |
| `rhoChargeL_rhoSpinL_commutator`, `rhoChargeR_rhoSpinR_commutator` | `lemma` | `0 < h`, `v ∈ A05.jointBudget h Ns K`, both spin margins `≤ h` | Proved (0 `sorry`) | Same-chirality charge-spin Kac-Moody commutation `[ρ_{χ,c}(m), ρ_{χ,s}(n)] v = 0` via cross-species cancellation `schwinger - schwinger = 0`. |
| `rhoChargeR_rhoChargeL_commute`, `rhoSpinR_rhoSpinL_commute` | `lemma` | Unconditional (ambient `Module.End ℂ`) | Proved (0 `sorry`) | Opposite chiralities commute identically on the whole Fock space via `A05.rho_cross_commute`. |

### Section 4: Two-Channel Spin-Singlet Pairing (`A3`, `B3`)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `singletBranchesA`, `singletBranchesB`, `singletOrderSC` | `def` | — | Complete (0 `sorry`) | `singletOrderSC := Ch20.orderSC singletBranchesB - Ch20.orderSC singletBranchesA` (matching Eq. (21.5) `c_{R↑} c_{L↓} - c_{R↓} c_{L↑}`). |
| `singlet_targets_distinct`, `singlet_channel_targets_orthogonal` | `lemma` | — | Proved (0 `sorry`) | Channels `A` and `B` land in orthogonal `SpinBranch → ℤ` sectors (`scTarget A ≠ scTarget B`). |
| `singlet_preserves_spin_and_shifts_charge` | `lemma` | — | Proved (0 `sorry`) | Both channels shift `Q_c ↦ Q_c - 2` while preserving `Q_s`. |
| `singletA_projected_residual`, `singletB_projected_residual` | `lemma` | `h Ks Km Kt : ℕ` | Proved (0 `sorry`) | Direct instantiations of `Ch20.projected_sc_residual` on both singlet channels. |

### Section 5: Real-Space Umklapp Operator (`A2`, `B2`)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `umklappDelta`, `umklappForwardTarget`, `umklappBackwardTarget` | `def` | — | Complete (0 `sorry`) | Shifts `(+1, +1, -1, -1)` and `(-1, -1, +1, +1)`. |
| `umklapp_targets_distinct`, `umklapp_quantum_number_shifts` | `lemma` | — | Proved (0 `sorry`) | Preserves `Q_c, Q_s, J_s`, shifts `J_c` by `∓4` (`±4`), pairwise distinct sectors. |
| `umklappForwardSite`, `umklappBackwardSite`, `umklappOp`, `periodicUmklappOp` | `def` | `gU : ℝ` | Complete (0 `sorry`) | Real-space 4-fermion operator summed over `x : Fin (2 * h)` at `periodicTwist (2 * h)`. |
| `umklappBackwardSite_eq_adjoint`, `umklappOp_self_adjoint` | `lemma` | `gU : ℝ` | Proved (0 `sorry`) | Exact self-adjointness `(H_U(g_U))† = H_U(g_U)`. |
| `umklappForwardSite_charge_commutator`, `umklappBackwardSite_charge_commutator`, `umklappForwardSite_maps_sector`, `umklappBackwardSite_maps_sector` | `lemma` | `v ∈ chargeSector h Ns` | Proved (0 `sorry`) | Exact CAR commutator charge shifts and charge-sector mapping proofs. |
| `umklappOp_charge_diagonal_zero` | `theorem` | `u ∈ jointBudget h Ns K₁`, `v ∈ jointBudget h Ns K₂` | Proved (0 `sorry`) | All fixed-charge diagonal matrix elements `⟨u | H_U(g_U) | v⟩` vanish identically. |

### Section 6: Zero-Charge Witness & `B4` Non-Invariance (`A4`, `B4`)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `witnessUpperMode` (`1`), `witnessLowerMode` (`1 - h`), `umklappTargetSpeciesConfig`, `umklappTargetConfig`, `umklappZeroChargeWitness` | `def` | `0 < h` | Complete (0 `sorry`) | Concrete band-bottom hole (`1 - h`) and particle (`+1`) witness configuration in `FockSpace`. |
| `umklappTargetSpeciesConfig_charge`, `umklappZeroChargeWitness_mem_target_sector`, `umklappZeroChargeWitness_orthogonal_zero_budget` | `lemma` | `0 < h` | Proved (0 `sorry`) | Proves `|Ψ_target⟩` has species charges `(+1, +1, -1, -1)` and is orthogonal to `jointBudget h 0 K` for all `K`. |
| `umklapp_zero_charge_witness_coeff` | `theorem` | `0 < h, gU : ℝ` | Proved (0 `sorry`) | Exact CAR matrix element `⟨Ψ_target | H_U(g_U) | Ω₀⟩ = -g_U / (2h)²` (`DecidableEq` bridged via `Subsingleton.elim`, `umklappBackwardSite` orthogonal, `8h - 1` odd CAR swaps, zero momentum transfer `(-1 - 1 + (1-h) + (1-h)) = -2h`). |
| `umklapp_witness_h2_coeff`, `umklapp_witness_h1_coeff` | `theorem` | `gU : ℝ` | Proved (0 `sorry`) | Specializes `umklapp_zero_charge_witness_coeff` to `-g_U / 16` (`h = 2, L = 4`) and `-g_U / 4` (`h = 1, L = 2`). |
| `umklapp_zero_budget_not_invariant` | `theorem` | `0 < h, K : ℕ, gU : ℝ, gU ≠ 0` | Proved (0 `sorry`) | `periodicUmklappOp h gU (groundKet h 0) ∉ jointBudget h 0 K` for every `K`. |

---

## 3. `h = 2, L = 4` Selection Rule Note

As derived in [`ch21_umklapp_derivation.md`](../../plans/v1-s9/ch21_umklapp_derivation.md), at `h = 2` (`L = 4`) the ground-to-ground overlap `⟨Ω(+1,+1,-1,-1) | H_U | Ω(0,0,0,0)⟩` vanishes identically because the forced annihilation momenta `k_2 = k_3 = 0` and creation momenta `k_0 = k_1 = 1` yield spatial sum `∑_{x=0}^3 (-1)^x = 0`. Nonzero scattering requires hole creation at the band bottom `1 - h = -1` (producing `{0}` in `R↑, R↓` with total excitation cost `2(h - 1) = 2`), which lies outside `K ≤ 1` low-energy cutoffs as well as outside any fixed zero-charge sector.
