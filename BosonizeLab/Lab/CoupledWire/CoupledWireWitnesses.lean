module

public import Bosonize.Core.CoupledWire
import Mathlib.Tactic.NormNum

/-!
# Coupled-Wire Duality Concrete Finite-`N_y` Witnesses (Lab Quarantine)

Quarantines concrete fixed-dimension (`N_y = 3, 4, 5, 6`, `Fin 2`/`Fin 3`/`Fin 4`, `decide`)
non-vacuity witnesses and refutations for the 9 Mathlib4-native `Bosonize/Core/CoupledWire/*`
modules under `BosonizeLab/Lab/CoupledWire/` so production `Bosonize/Core/` maintains zero
Rank-0 regressions (`delta_lean_rank0_count == 0`).
-/

@[expose] public section

namespace BosonizeLab.CoupledWire

open scoped BigOperators
open Matrix Bosonize.CoupledWire

/-! ### 1. Duality Matrix (`D^2`, `D P D^T`, `D A D^T`, Odd-`N` Counterexample) -/

theorem duality_odd_N3_counterexample :
    (∑ k ∈ Finset.range 3, dualityEntry 0 k * dualityEntry k 0 = 0) ∧
    (∑ k ∈ Finset.range 3, dualityEntry 0 k * dualityEntry k 1 = 1) := by
  decide

theorem duality_even_N4_identities :
    (∀ i ∈ Finset.range 4, ∀ j ∈ Finset.range 4,
      ∑ k ∈ Finset.range 4, dualityEntry i k * dualityEntry k j = if i = j then 1 else 0) ∧
    (∀ i ∈ Finset.range 4, ∀ j ∈ Finset.range 4,
      ∑ k ∈ Finset.range 4, dualityEntry i k * paritySign k * dualityEntry j k =
        if i = j then -paritySign j else 0) ∧
    (∀ i ∈ Finset.range 4, ∀ j ∈ Finset.range 4,
      ∑ j1 ∈ Finset.range 4, ∑ j2 ∈ Finset.range 4,
        dualityEntry i j1 * skewSignEntry j1 j2 * dualityEntry j j2 = -skewSignEntry i j) := by
  refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_, fun i hi j hj => ?_⟩
  · exact dualitySq_even 2 i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
  · exact duality_chirality_flip_even 2 i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
  · exact duality_skewSign_flip_even 2 i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)

theorem duality_even_N6_identities :
    (∀ i ∈ Finset.range 6, ∀ j ∈ Finset.range 6,
      ∑ k ∈ Finset.range 6, dualityEntry i k * dualityEntry k j = if i = j then 1 else 0) ∧
    (∀ i ∈ Finset.range 6, ∀ j ∈ Finset.range 6,
      ∑ j1 ∈ Finset.range 6, ∑ j2 ∈ Finset.range 6,
        dualityEntry i j1 * skewSignEntry j1 j2 * dualityEntry j j2 = -skewSignEntry i j) :=
  ⟨fun _ hi _ hj => dualitySq_even 3 _ _ (Finset.mem_range.mp hi) (Finset.mem_range.mp hj),
   fun _ hi _ hj => duality_skewSign_flip_even 3 _ _ (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)⟩

/-! ### 2. Boundary Defects, Dirac Mass & SSH Edge Zero-Mode Witnesses (`N = 4, 5, 6`) -/

theorem pbc_even_N4_closing_defect :
    (∀ z ∈ Finset.range 4,
      (∑ k ∈ Finset.range 4, pbcDiffEntry 4 3 k * dualityEntry k z) +
        paritySign 3 * pbcDiffEntry 4 3 z = -(2 * paritySign z)) ∧
    (∑ z ∈ Finset.range 4,
      ((∑ k ∈ Finset.range 4, pbcDiffEntry 4 3 k * dualityEntry k z) +
        paritySign 3 * pbcDiffEntry 4 3 z) ^ 2 = 16) :=
  ⟨fun z hz => pbc_defect_row_even 4 z (by decide) (by decide) (Finset.mem_range.mp hz),
   by simpa using pbc_defect_row_even_frobenius_sq 4 (by decide) (by decide)⟩

theorem dirac_mass_N4_topo_zero_mode :
    ∀ y ∈ Finset.range 4,
      ∑ z ∈ Finset.range 4, wireMassEntry 4 0 1 y z * evenWireTopoLeftEdge z = 0 :=
  fun y hy => evenWireTopoLeftEdge_in_kernel 1 2 y (Finset.mem_range.mp hy)

theorem ssh_N4_edge_residual_witness :
    (∑ z ∈ Finset.range 4, sshWireMatrix 1 3 4 3 z * leftEdgeVec 1 3 2 z = -1) ∧
    (∑ z ∈ Finset.range 4, sshWireMatrix 1 3 4 0 z * leftEdgeVec 1 3 2 z = 0) ∧
    (∑ z ∈ Finset.range 4, sshWireMatrix 1 3 4 1 z * leftEdgeVec 1 3 2 z = 0) ∧
    (∑ z ∈ Finset.range 4, sshWireMatrix 1 3 4 2 z * leftEdgeVec 1 3 2 z = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using sshWire_even_leftEdge_residual 1 3 2 3 (by decide) (by decide)
  · exact sshWire_even_leftEdge_interior_zero 1 3 2 0 (by decide) (by decide)
  · exact sshWire_even_leftEdge_interior_zero 1 3 2 1 (by decide) (by decide)
  · exact sshWire_even_leftEdge_interior_zero 1 3 2 2 (by decide) (by decide)

theorem ssh_N5_exact_zero_mode_witness :
    ∀ r < 5, ∑ z ∈ Finset.range 5, sshWireMatrix 1 3 5 r z * oddLeftEdgeVec 1 3 2 z = 0 :=
  fun r hr => sshWire_odd_leftEdge_zero 1 3 2 r hr

theorem ssh_N6_left_profile_witness :
    leftEdgeVec 1 3 3 0 = 9 ∧ leftEdgeVec 1 3 3 2 = -3 ∧ leftEdgeVec 1 3 3 4 = 1 := by
  decide

/-! ### 3. Bloch `2×2` Dirac Cone, Symmetries & Dual Kinetic Cancellation (`N = 4, 6`) -/

theorem pauliY_sq_unit :
    pauliY * pauliY = (1 : Matrix (Fin 2) (Fin 2) GaussianInt) := by
  simpa using pauliY_sq_scale 1

theorem bloch_pythagorean_5_3_4_witness :
    blochWireMatrixHomog 1 0 1 1 5 3 4 * blochWireMatrixHomog 1 0 1 1 5 3 4 =
      ((80 : ℤ) : GaussianInt) • (1 : Matrix (Fin 2) (Fin 2) GaussianInt) ∧
    blochWireMatrixHomog 1 0 1 1 5 (-5) 0 * blochWireMatrixHomog 1 0 1 1 5 (-5) 0 = 0 := by
  constructor
  · rw [blochWireMatrixHomog_sq]; rfl
  · exact (blochWireHomog_single_node_uniqueness 1 0 1 1 5 (-5) 0
      (by decide) (by decide) rfl (by decide) (by decide)).2 ⟨rfl, rfl, rfl⟩

theorem mamTimeRevOp_unit_sq_witness :
    mamTimeRevOp 1 0 * (mamTimeRevOp 1 0).map star =
      (⟨-1, 0⟩ : GaussianInt) • (1 : Matrix (Fin 2) (Fin 2) GaussianInt) ∧
    mamTimeRevOp (-1) 0 * (mamTimeRevOp (-1) 0).map star =
      (⟨1, 0⟩ : GaussianInt) • (1 : Matrix (Fin 2) (Fin 2) GaussianInt) := by
  constructor
  · simpa using mamTimeRevOp_bloch_sq 1 0
  · simpa using mamTimeRevOp_bloch_sq (-1) 0

theorem doubledLattice_two_node_contrast_witness :
    doubledLatticeMatrix 1 0 2 0 * doubledLatticeMatrix 1 0 2 0 = 0 ∧
    ((1 : ℤ) ^ 2 + 0 ^ 2 = 1) ∧ (((-1 : ℤ) ^ 2 + 0 ^ 2 = 1)) := by
  have h := doubledLatticeHomog_distinct_zeros 1 2 1 (by decide)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem dual_kinetic_N4_N6_witness :
    (∑ y ∈ Finset.range 4,
      ((∑ z ∈ Finset.range 4, dualityEntry y z * (z : ℤ)) ^ 2 + (y : ℤ) ^ 2 -
        (∑ z ∈ Finset.range 4, dualInvTransEntry y z * paritySign z * (z : ℤ)) ^ 2) = 0) ∧
    (∑ y ∈ Finset.range 6,
      ((∑ z ∈ Finset.range 6, dualityEntry y z * ((z : ℤ) - 2)) ^ 2 + ((y : ℤ) - 2) ^ 2 -
        (∑ z ∈ Finset.range 6, dualInvTransEntry y z * paritySign z * ((z : ℤ) - 2)) ^ 2) = 0) :=
  ⟨dual_kinetic_cancellation_exact 4 (fun z => (z : ℤ)),
   dual_kinetic_cancellation_exact 6 (fun z => (z : ℤ) - 2)⟩

/-! ### 4. Staggered CS, Mutual-CS `(3, 3, 2)` Gauge Invariance, `π`-Mode & Dirac-CFL -/

theorem staggeredCS_N4_TI_and_2DEG_witness :
    (twoNu 0 0 = 1 ∧ twoNu 0 1 = -1 ∧ twoNu 0 2 = 1 ∧ twoNu 0 3 = -1) ∧
    (twoNu 1 0 = 2 ∧ twoNu 1 1 = 0 ∧ twoNu 1 2 = 2 ∧ twoNu 1 3 = 0) ∧
    (staggeredCSVarOBC 4 0 0 + (-2 * paritySign 0) = -1 ∧
     staggeredCSVarOBC 4 0 3 + (-2 * paritySign 3) = 1) := by
  decide

theorem mutualCS_T3_X3_N2_gauge_inv_witness :
    let f : ℕ → ℕ → ℕ → ℤ := fun t x y => (t : ℤ) + 2 * (x : ℤ) - (y : ℤ)
    let g : ℕ → ℕ → ℕ → ℤ := fun t x y => 3 * (t : ℤ) - (x : ℤ) + (y : ℤ)
    mutualCSAction 3 3 2
      (fun t x y => f t x y + dtC 3 g t x y)
      (fun t x y => f t x y + dxC 3 g t x y)
      (fun t x y => f t x y + dyP 2 g t x y) f g f =
    mutualCSAction 3 3 2 f f f f g f :=
  mutualCSAction_gauge_inv 3 3 2 (by decide) (by decide) (by decide) _ _ _ _ _ _ _

theorem piMode_and_diracCfl_clean_ph_half_witness :
    (piModeSchurMat (2 : ℤ) 3).det = 21 ∧
    (diracCflFourDfSigmaEM (1 : ℤ) 0 0 1 = 2 ∧
     2 * diracCflFourDfSigmaEM (1 : ℤ) 0 0 1 = 4) := by
  refine ⟨?_, ?_⟩
  · rw [piModeSchurMat_det]; norm_num
  · simpa using diracCfl_ph_sym_hall_half (1 : ℤ)

/-! ### 5. 6-Wire 3-Cone, Fu–Kane `T`-Pfaffian `-4` Correction, `transProj` & `N = 2` Klein -/

theorem threeCone_and_tPfaffian_witness :
    (threeCone01Ham 1 0 1 3 2 5 3 4).det = ((4096 : ℤ) : GaussianInt) ∧
    threeConeDet6 1 0 1 3 2 2 5 5 0 = 0 ∧
    dualityTransposeApply 12 (fkPairOp 1) 5 = -4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [threeCone01Ham_det_general]; norm_num
  · exact (threeCone_mass_gapping_and_zero_mode 1 0 1 3 2 2 5 3 4 (by decide) (by decide)).2.2.1
  · rw [fkPairOp_duality_exact 12 1 5 (by decide)]; decide

theorem transProj_Fin3_and_Fin4_witness :
    let q3 : Fin 3 → ℤ := ![1, 2, 2]
    let q4 : Fin 4 → ℤ := ![1, 1, 1, 1]
    euclidNormSq q3 = 9 ∧
    Matrix.trace (transProj q3) = 18 ∧
    transProj q3 *ᵥ q3 = 0 ∧
    transProj q3 * transProj q3 = (9 : ℤ) • transProj q3 ∧
    Matrix.trace (transProj q4) = 12 := by
  have h3norm : euclidNormSq (![1, 2, 2] : Fin 3 → ℤ) = 9 := by decide
  have h4norm : euclidNormSq (![1, 1, 1, 1] : Fin 4 → ℤ) = 4 := by decide
  refine ⟨h3norm, ?_, transProj_mulVec_self _, ?_, ?_⟩
  · rw [transProj_trace, h3norm]; norm_num
  · rw [transProj_mul_self, h3norm]
  · rw [transProj_trace, h4norm]; norm_num

theorem qed3_conductivity_inverse_cleared_witness :
    ∀ K_J K_irr : ℤ,
      (K_irr + 1 * 6 ^ 2) * K_J = 6 ^ 2 →
      3 * K_J = 2 * 6 →
      2 * (K_irr + 1 * 6 ^ 2) = 3 * 6 →
      (2 : ℤ) * 3 = 3 * 2 :=
  fun K_J K_irr hD hJ hI =>
    qed3_conductivity_inverse_product_cleared K_J K_irr 1 6 2 3 3 2 (by decide) hD hJ hI

/-- Explicit refutation witnessing that dropping `sgn(y - y')` in MAM App. 11 violates
commutator antisymmetry `[φ_{+,0}, φ_{-,1}] + [φ_{-,1}, φ_{+,0}] = 0`, whereas the exact
finite-`2m` `commVarphi_HalfPi` satisfies antisymmetry identically. -/
theorem mam_app11_dropped_sgn_breaks_skew :
    let naiveApp11 := fun (y y' : ℕ) => if y = y' then (0 : ℤ) else (2 : ℤ)
    naiveApp11 0 1 + naiveApp11 1 0 ≠ 0 ∧
    commVarphi_HalfPi 2 1 0 1 1 (-1) + commVarphi_HalfPi 2 (-1) 1 0 (-1) 1 = 0 ∧
    commVarphi_HalfPi 3 1 2 2 1 1 = 0 := by
  refine ⟨by decide, ?_, ?_⟩
  · have h := commVarphi_skew 2 1 0 1 1 (-1) (by decide) (by decide)
    omega
  · exact (commVarphi_same_species_bosonic 3 1 2 2 1 (Or.inl rfl) (by decide) (by decide)).2.1 rfl

end BosonizeLab.CoupledWire
