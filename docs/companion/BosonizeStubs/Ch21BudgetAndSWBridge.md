# Mirrored Companion: `BosonizeStubs.Ch21BudgetAndSWBridge` (Chapter 21 Phase B)

**Lean Module:** [`BosonizeStubs/Ch21BudgetAndSWBridge.lean`](../../../BosonizeStubs/Ch21BudgetAndSWBridge.lean)  
**Parent Staging Modules:** [`BosonizeStubs/Ch21SpinfulModels.lean`](../../../BosonizeStubs/Ch21SpinfulModels.lean), [`BosonizeStubs/Ch21CocycleAndLeakage.lean`](../../../BosonizeStubs/Ch21CocycleAndLeakage.lean)  
**Reference LaTeX Sections:** [`notes/latex/chapters/sections/21.1.tex`](../../../notes/latex/chapters/sections/21.1.tex) (L575–621), [`notes/latex/chapters/sections/21.2.tex`](../../../notes/latex/chapters/sections/21.2.tex) (L380–397), [`notes/latex/chapters/sections/21.4.tex`](../../../notes/latex/chapters/sections/21.4.tex) (L348–401)  
**Audit Reference:** [`docs/plans/v1-s9/v1_release_readiness_audit.md`](../../plans/v1-s9/v1_release_readiness_audit.md)  
**Phase Status:** Phase B Complete — Awaiting Human Phase C Promotion (`lake env lean -DwarningAsError=true BosonizeStubs/Ch21BudgetAndSWBridge.lean` exits `0` with zero warnings and zero `sorry`s; `python3 scripts/webllm/audit_axioms.py BosonizeStubs/Ch21BudgetAndSWBridge.lean` exits `0` across all `63` exported declarations [`36` exported proofs: `19` `theorem`s + `17` `lemma`s; `27` exported data/instance commands: `23` `def`s + `4` `local instance`s; plus `20` `private lemma`s] using standard axioms `[propext, Classical.choice, Quot.sound]` only).

---

## 1. Carrier Conventions & Physical Correspondence

| Convention | Lean Realization | Mathematical Meaning |
| :--- | :--- | :--- |
| Local mode order instances | `localModeLinearOrderCh21Bridge`, `localModeLTCh21Bridge`, `localModeLECh21Bridge`, `localModeDecidableEqCh21Bridge` | Lexicographic `A05.speciesOrder h` (`L↑ < L↓ < R↑ < R↓`, then momentum `k ∈ Ch01.Band (2*h)`) matching frozen `A05`/`Ch14`. |
| Graded energy-tuple subspaces | `gradedSectorSet h Ns es`, `gradedSectorSpace h Ns es`, `gradeTupleIndex K` | Exact per-species charge `Ns` and exact per-species excitation tuple `es : Fin 4 → ℕ`, realizing `⨂_α ℋ_{α, N_α}^{(e_α)}` on `A05.FockSpace SpinBranch h`. |
| Product-cutoff space | `productCutoffSet h Ns K`, `productCutoffSpace h Ns K` | Per-species independent cutoff `∀ ν, excitationEnergy ≤ K`, realizing `⨂_α (⨁_{e=0}^K ℋ_{α, N_α}^{(e)})`. |
| `K = 1` counterexample ket | `bandZero h hh`, `singleExciteZero h hh`, `k1DoubleExciteSpeciesConfig h hh`, `k1DoubleExciteConfig h hh`, `k1DoubleExciteKet h hh` | Basis ket promoting `k = 0 ↦ 1` in both `L↑` and `L↓` while keeping `R↑, R↓` in the sea ground (`0 < h`), having per-species costs `(1, 1, 0, 0)` and total cost `2 > 1`. |
| Matrix-level SW projectors & `W^(2)` | `swLowProjMatrix`, `swHighProjMatrix`, `swOffDiagMatrix`, `swSecondOrderMatrix` | Diagonal matrix projectors `P, Q` from `inLow : ι → Bool`, off-diagonal perturbation `V_off = P V Q + Q V P`, and `W^(2) = (1/2) P [S₁, V] P` built on `A10.swGeneratorMatrix`. |
| Spinful free-fermion Hamiltonian | `spinfulFreeHamiltonian h` | `H₀ = ∑_ν (H_ν - E_{sea})` diagonal in the 4-branch occupation basis (`E(Ω₀) = 0`, `E(Ψ_target) = 2h`). |
| Spinful Umklapp SW block | `umklappBlockBasis`, `umklappBlockInLow`, `umklappBlockEnergy`, `umklappBlockH0Matrix`, `umklappBlockVMatrix`, `umklappBlockProj`, `umklappBlockVOp`, `umklappBlockS1Op` | Concrete 2-state Umklapp-coupled block `{|Ω₀⟩ ∈ jointBudget h 0 0, |Ψ_target⟩ ∈ jointBudget h (+1,+1,-1,-1) (2*(h-1))}` instantiating both matrix-level `A10` (`sw_generator_commutator_eq`, `nonResonant`) and operator-level `A10.sw_compressed_bch_second_order`. |

---

## 2. Exported API, Hypotheses & Verification Inventory

### Local Instances (4 exported `local instance` declarations)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `localModeLinearOrderCh21Bridge` | `local instance` | `h : ℕ` | Complete (0 `sorry`) | `LinearOrder (A05.Mode (Fin 4) h) := A05.speciesOrder h`. |
| `localModeLTCh21Bridge` | `local instance` | `h : ℕ` | Complete (0 `sorry`) | `LT (A05.Mode (Fin 4) h) := (A05.speciesOrder h).toLT`. |
| `localModeLECh21Bridge` | `local instance` | `h : ℕ` | Complete (0 `sorry`) | `LE (A05.Mode (Fin 4) h) := (A05.speciesOrder h).toLE`. |
| `localModeDecidableEqCh21Bridge` | `local instance` | `h : ℕ` | Complete (0 `sorry`) | `DecidableEq (A05.Mode (Fin 4) h) := A05.localModeDecidableEq h`. |

### Section 1: Graded Direct-Sum Decomposition vs. Product-Cutoff Counterexample (`eq:ch21-budget-energy-sum`, `eq:ch21-not-product-cutoff`)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `gradedSectorSet` | `def` | `h : ℕ, Ns : SpinBranch → ℤ, es : SpinBranch → ℕ` | Complete (0 `sorry`) | Occupation predicate `∀ ν, relativeCharge S ν = Ns ν ∧ excitationEnergy S ν = es ν`. |
| `gradedSectorSpace` | `def` | `h : ℕ, Ns : SpinBranch → ℤ, es : SpinBranch → ℕ` | Complete (0 `sorry`) | Coordinate submodule `A03.coordinateSpace (gradedSectorSet h Ns es)` realizing `⨂_α ℋ_{α, N_α}^{(e_α)}`. |
| `productCutoffSet` | `def` | `h : ℕ, Ns : SpinBranch → ℤ, K : ℕ` | Complete (0 `sorry`) | Occupation predicate `∀ ν, relativeCharge S ν = Ns ν ∧ excitationEnergy S ν ≤ K`. |
| `productCutoffSpace` | `def` | `h : ℕ, Ns : SpinBranch → ℤ, K : ℕ` | Complete (0 `sorry`) | Coordinate submodule `A03.coordinateSpace (productCutoffSet h Ns K)` realizing `⨂_α (⨁_{e=0}^K ℋ_{α, N_α}^{(e)})`. |
| `gradeTupleIndex` | `def` | `K : ℕ` | Complete (0 `sorry`) | Simplex index set `{es : SpinBranch → ℕ \| ∑ ν, es ν ≤ K}`. |
| `ket_mem_gradedSectorSpace_iff` | `lemma` | `h : ℕ, Ns, es, S` | Proved (0 `sorry`) | `A02.ket S ∈ gradedSectorSpace h Ns es ↔ ∀ ν, A02.ket (speciesConfiguration h S ν) ∈ Ch07.energySpace h (Ns ν) (es ν)`. |
| `tensorVector_mem_gradedSectorSpace` | `lemma` | `∀ ν, vs ν ∈ Ch07.energySpace h (Ns ν) (es ν)` | Proved (0 `sorry`) | Ordered tensor product `A05.tensorVector h vs` maps into `gradedSectorSpace h Ns es`. |
| `gradedSectorSpace_orthogonal` | `lemma` | `es₁ ≠ es₂`, `u ∈ gradedSectorSpace h Ns es₁`, `v ∈ gradedSectorSpace h Ns es₂` | Proved (0 `sorry`) | Distinct excitation-grade tuples yield mutually orthogonal subspaces (`inner ℂ u v = 0`). |
| `gradedSectorSpace_iSupIndep` | `theorem` | `h : ℕ, Ns : SpinBranch → ℤ, K : ℕ` | Proved (0 `sorry`) | Internal direct-sum linear independence `iSupIndep` of `{gradedSectorSpace h Ns es.val}` over `∑ ν, e ν ≤ K`. |
| `budgetSet_eq_iUnion_gradedSectorSet` | `lemma` | `0 < h` | Proved (0 `sorry`) | Exact set partition `Ch14.budgetSet h Ns K = ⋃_{∑ e_ν ≤ K} gradedSectorSet h Ns es`. |
| `ket_mem_jointBudget_iff_graded` | `theorem` | `0 < h` | Proved (0 `sorry`) | Exact basis-ket equivalence `A02.ket S ∈ A05.jointBudget h Ns K ↔ ∃ es, ∑ ν, es ν ≤ K ∧ ∀ ν, charge = Ns ν ∧ excitation = es ν`. |
| `jointBudget_eq_graded_sum` | `theorem` | `0 < h` | Proved (0 `sorry`) | Equation `eq:ch21-budget-energy-sum`: `A05.jointBudget h Ns K = ⨆_{∑ e_ν ≤ K} gradedSectorSpace h Ns es` (orthogonal direct sum with `gradedSectorSpace_iSupIndep`). |
| `jointBudget_le_productCutoff` | `theorem` | `0 < h` | Proved (0 `sorry`) | Natural inclusion `A05.jointBudget h Ns K ≤ productCutoffSpace h Ns K`. |
| `productCutoffSpace_eq_graded_sum` | `theorem` | `0 < h` | Proved (0 `sorry`) | Graded decomposition `productCutoffSpace h Ns K = ⨆_{∀ ν, e_ν ≤ K} gradedSectorSpace h Ns es`. |
| `bandZero` | `def` | `0 < h` | Complete (0 `sorry`) | Fermi-surface momentum `k = 0` inside `Ch01.Band (2 * h)`. |
| `singleExciteZero` | `def` | `0 < h` | Complete (0 `sorry`) | Single-species energy-1 excitation `insert 1 ((groundConfiguration h 0).erase 0)`. |
| `singleExciteZero_charge_and_excitation` | `lemma` | `0 < h` | Proved (0 `sorry`) | `relativeCharge h (singleExciteZero h hh) = 0 ∧ excitationEnergy h (singleExciteZero h hh) = 1`. |
| `k1DoubleExciteSpeciesConfig` | `def` | `0 < h` | Complete (0 `sorry`) | Per-species occupation: `singleExciteZero` on `L↑, L↓`; `groundConfiguration h 0` on `R↑, R↓`. |
| `k1DoubleExciteConfig` | `def` | `0 < h` | Complete (0 `sorry`) | Combined 4-branch configuration `A05.jointConfiguration h (k1DoubleExciteSpeciesConfig h hh)`. |
| `k1DoubleExciteKet` | `def` | `0 < h` | Complete (0 `sorry`) | Basis ket `A02.ket (k1DoubleExciteConfig h hh)`. |
| `k1_product_cutoff_strict_superset` | `theorem` | `0 < h` | Proved (0 `sorry`) | Equation `eq:ch21-not-product-cutoff`: proves `k1DoubleExciteKet h hh` lies in each species `Ch07.fixedBudget h 0 1` and in `productCutoffSpace h 0 1`, has `totalExcitation = 2`, lies outside `A05.jointBudget h 0 1`, and proves strict inclusion `A05.jointBudget h 0 1 < productCutoffSpace h 0 1`. |

### Section 2: General-`h` Singlet Klein-Product Sign (`eq:ch21-pair-general-sign`)

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `singlet_klein_product_sign_eq` | `theorem` | `0 < h` | Proved (0 `sorry`) | Equation `eq:ch21-pair-general-sign`: exact CAR fermion-sign products equal `(-1)^(h + 1)` for both channel 1 (`2h - 1` and `3h - 2` preceding fermions) and channel 2 (`h - 1` and `4h - 2` preceding fermions). |
| `singlet_klein_sign_channel1` | `theorem` | `0 < h, x : ℤ` | Proved (0 `sorry`) | Channel 1 (`singletBranchesB`: `R↑, L↓`) ground-to-ground matrix element `⟨Ω_{T_B}, orderSC(B, x) Ω₀⟩ = (-1)^(h + 1) / (2 * h)` at periodic twist. |
| `singlet_klein_sign_channel2` | `theorem` | `0 < h, x : ℤ` | Proved (0 `sorry`) | Channel 2 (`singletBranchesA`: `R↓, L↑`) ground-to-ground matrix element `⟨Ω_{T_A}, orderSC(A, x) Ω₀⟩ = (-1)^(h + 1) / (2 * h)` at periodic twist. |
| `singlet_pair_general_sign` | `theorem` | `0 < h, x : Fin (2 * h)` | Proved (0 `sorry`) | Full general-`h` singlet pairing theorem: `singletOrderSC` yields `(-1)^(h + 1) / (2 * h)` on `Ω_{T_B}` and `-((-1)^(h + 1) / (2 * h))` on `Ω_{T_A}`, with `⟨Ω_{T_B}, Ω_{T_A}⟩ = 0`. |
| `singlet_pair_general_sign_h2` | `theorem` | `x : Fin (2 * 2)` | Proved (0 `sorry`) | Clean `h = 2` specialization for every lattice site `x : Fin 4`: `-(1 / 4)` on `Ω_{T_B}` and `+(1 / 4)` on `Ω_{T_A}`. |

### Section 3: Explicit Sum-Over-States Formula for `W^(2)` (`prop:ch21-sw-intermediate`) & `Ch21 → A10` Block Bridge

| Symbol | Kind | Explicit Hypotheses | Status | Mathematical Content |
| :--- | :--- | :--- | :--- | :--- |
| `swLowProjMatrix`, `swHighProjMatrix` | `def` | `[DecidableEq ι], inLow : ι → Bool` | Complete (0 `sorry`) | Diagonal matrix projectors `P` (`inLow i = true`) and `Q` (`inLow i = false`). |
| `swOffDiagMatrix` | `def` | `[DecidableEq ι], inLow : ι → Bool, V : Matrix ι ι ℂ` | Complete (0 `sorry`) | Off-diagonal block `V_off(i, j) = if inLow i ≠ inLow j then V i j else 0`. |
| `swSecondOrderMatrix` | `def` | `[Fintype ι] [DecidableEq ι], inLow, E, V` | Complete (0 `sorry`) | `W^(2) = (1/2) P [S₁, V] P` with `S₁ = A10.swGeneratorMatrix inLow E (swOffDiagMatrix inLow V)`. |
| `swLowProjMatrix_comm_diagEnergy` | `lemma` | `[Fintype ι] [DecidableEq ι], inLow, E` | Proved (0 `sorry`) | Exact commutation `[P, diagEnergyMatrix E] = 0`. |
| `swOffDiagMatrix_eq_block` | `lemma` | `[Fintype ι] [DecidableEq ι], inLow, V` | Proved (0 `sorry`) | `swOffDiagMatrix inLow V = P * V * Q + Q * V * P`. |
| `swOffDiagMatrix_conjTranspose` | `lemma` | `V.conjTranspose = V` | Proved (0 `sorry`) | Hermiticity preservation `(swOffDiagMatrix inLow V)ᴴ = swOffDiagMatrix inLow V`. |
| `sw_generator_matrix_commutator` | `lemma` | `A10.nonResonant inLow E (swOffDiagMatrix inLow V)` | Proved (0 `sorry`) | Wrapper instantiating `A10.sw_generator_commutator_eq`: `[S₁, H₀] = -V_off`. |
| `sw_generator_matrix_skew_hermitian` | `lemma` | `V.conjTranspose = V` | Proved (0 `sorry`) | Wrapper instantiating `A10.sw_generator_skew_hermitian`: `S₁ᴴ = -S₁`. |
| `sw_second_order_intermediate_sum` | `theorem` | `A10.nonResonant inLow E (swOffDiagMatrix inLow V)`, `inLow l = true`, `inLow l' = true` | Proved (0 `sorry`) | Proposition `prop:ch21-sw-intermediate` (`eq:ch21-sw-intermediate-sum`): exact sum-over-`I_Q` matrix entry formula for `W^(2)_{l l'}` plus nonvanishing of every denominator `E_l ≠ E_μ`, `E_{l'} ≠ E_μ` in the sum. |
| `sw_second_order_diagonal_shift` | `theorem` | `Vᴴ = V`, `A10.nonResonant`, `inLow l = true` | Proved (0 `sorry`) | Equation `eq:ch21-sw-diagonal-shift`: diagonal shift `W^(2)_{l l} = ∑_{μ ∈ I_Q, V_{lμ} ≠ 0} ‖V_{lμ}‖² / (E_l - E_μ)`. |
| `sw_second_order_diagonal_nonpos_of_ordered` | `theorem` | `Vᴴ = V`, `A10.nonResonant`, `inLow l = true`, `∀ μ ∈ I_Q, V_{lμ} ≠ 0 → E_l < E_μ` | Proved (0 `sorry`) | Strictly ordered spectrum sign rule (`21.4.tex` L397–399): `(W^(2)_{l l}).re ≤ 0 ∧ (W^(2)_{l l}).im = 0`. |
| `spinfulFreeHamiltonian` | `def` | `h : ℕ` | Complete (0 `sorry`) | Diagonal free-fermion relative-energy Hamiltonian `H₀ = ∑_ν (H_ν - E_{sea})` on `A05.FockSpace SpinBranch h`. |
| `spinfulFreeHamiltonian_self_adjoint` | `lemma` | `h : ℕ` | Proved (0 `sorry`) | `LinearMap.adjoint (spinfulFreeHamiltonian h) = spinfulFreeHamiltonian h`. |
| `spinfulFreeHamiltonian_ground_zero` | `lemma` | `0 < h` | Proved (0 `sorry`) | `spinfulFreeHamiltonian h (A05.groundKet h 0) = 0`. |
| `umklappZeroChargeWitness_mem_budget` | `lemma` | `0 < h` | Proved (0 `sorry`) | `umklappZeroChargeWitness h hh ∈ A05.jointBudget h (+1,+1,-1,-1) (2 * (h - 1))`. |
| `spinfulFreeHamiltonian_umklappWitness` | `lemma` | `0 < h` | Proved (0 `sorry`) | `spinfulFreeHamiltonian h (umklappZeroChargeWitness h hh) = (2 * h) • umklappZeroChargeWitness h hh` (`E = 4` at `h = 2`). |
| `umklappBlockBasis`, `umklappBlockInLow`, `umklappBlockEnergy` | `def` | `0 < h` | Complete (0 `sorry`) | Orthonormal 2-state basis `{|Ω₀⟩, |Ψ_target⟩}`, low/high indicator `(true, false)`, and baseline energies `(0, 2h)`. |
| `umklappBlockH0Matrix`, `umklappBlockVMatrix` | `def` | `0 < h, gU : ℝ` | Complete (0 `sorry`) | Gram matrices of `spinfulFreeHamiltonian h` and `periodicUmklappOp h gU` on `umklappBlockBasis h hh`. |
| `umklappBlock_orthonormal` | `lemma` | `0 < h, i j : Fin 2` | Proved (0 `sorry`) | `⟨b_i, b_j⟩ = δ_{ij}` for `umklappBlockBasis h hh`. |
| `umklappBlockH0Matrix_eq_diag` | `lemma` | `0 < h` | Proved (0 `sorry`) | `umklappBlockH0Matrix h hh = A10.diagEnergyMatrix (umklappBlockEnergy h)`. |
| `umklappBlockVMatrix_explicit` | `lemma` | `0 < h, gU : ℝ` | Proved (0 `sorry`) | `umklappBlockVMatrix h hh gU = !![0, -g_U/(2h)²; -g_U/(2h)², 0]` via `umklappOp_charge_diagonal_zero`, `umklapp_zero_charge_witness_coeff`, and `umklappOp_self_adjoint`. |
| `umklappBlock_a10_hypotheses` | `theorem` | `0 < h, gU : ℝ` | Proved (0 `sorry`) | Verifies `[P, H₀] = 0`, `Vᴴ = V`, `V_off = V`, and `A10.nonResonant` on the spinful Umklapp block. |
| `umklappBlock_sw_generator_and_shift` | `theorem` | `0 < h, gU : ℝ` | Proved (0 `sorry`) | Instantiates `A10.sw_generator_commutator_eq`, `A10.sw_generator_skew_hermitian`, and `sw_second_order_diagonal_shift`, obtaining `W^(2)_{00} = -g_U² / (32 h⁵)`. |
| `umklappBlock_sw_h2` | `theorem` | `gU : ℝ` | Proved (0 `sorry`) | Concrete `h = 2` specialization: `H₀ = diag(0, 4)`, `V_{01} = V_{10} = -g_U / 16`, and `W^(2)_{00} = -g_U² / 1024`. |
| `umklappBlockProj`, `umklappBlockVOp`, `umklappBlockS1Op` | `def` | `0 < h, gU : ℝ` | Complete (0 `sorry`) | Coordinate projector `Π_block` onto `{S₀, S_target}`, projected Umklapp perturbation `Π_block H_U Π_block`, and explicit skew-Hermitian generator `S₁` on `A05.Operators SpinBranch h`. |
| `umklappBlock_a10_bch_bridge` | `theorem` | `0 < h, gU t : ℝ` | Proved (0 `sorry`) | Operator-level instantiation of `A10.sw_compressed_bch_second_order` with `P = Ch14.projection h 0 0`, `Q = 1 - P`, `H₀ = spinfulFreeHamiltonian h`, `V = umklappBlockVOp h hh gU`, `S₁ = umklappBlockS1Op h hh gU`: proves `[P, H₀] = 0`, `S₁† = -S₁`, `[S₁, H₀] = -offDiagPart`, `P * bchSecondOrderPolynomial ... * P = swEffectiveSecondOrder ...`, and `swEffectiveSecondOrder ... |Ω₀⟩ = (-(t² g_U²) / (32 h⁵)) • |Ω₀⟩`. |
| `umklappBlock_a10_bch_bridge_h2` | `theorem` | `gU t : ℝ` | Proved (0 `sorry`) | Concrete `h = 2` operator-level BCH bridge specialization giving effective ground-state shift `-(t² g_U²) / 1024`. |

---

## 3. Verification Summary

- `lake env lean -DwarningAsError=true BosonizeStubs/Ch21BudgetAndSWBridge.lean`: exit `0` (zero warnings, zero errors, zero `sorry`s).
- `python3 scripts/webllm/audit_axioms.py BosonizeStubs/Ch21BudgetAndSWBridge.lean`: exit `0` (`PASS: 63 freshly built data/theorem declarations`, standard axioms `[propext, Classical.choice, Quot.sound]` only).
- `lake build Bosonize && lake build BosonizeStubs`: exit `0`.
- `python3 scripts/guards/core_lock.py`: exit `0` (`44` Core files untouched).
- `python3 -m unittest discover -s scripts/guards -p 'test_*.py'`: exit `0`.
- `python3 -m unittest discover -s scripts/webllm -p 'test_*.py'`: exit `0`.
