import Bosonize
import BosonizeStubs.A07InteractionsAndBogoliubov
import BosonizeStubs.A10DiscreteSchriefferWolff

namespace Bosonize.Ch17

open scoped BigOperators Classical

section ScalarParameters

noncomputable def v1Velocity (vF g4 : ℝ) : ℝ :=
  vF + g4 / (2 * Real.pi)

noncomputable def v2Velocity (g2 : ℝ) : ℝ :=
  g2 / (2 * Real.pi)

noncomputable def canonicalMu (h : ℕ) (vF : ℝ) : ℝ :=
  Real.pi * vF / ((2 * h : ℕ) : ℝ)

def sugawaraMargin {σ : Type*} (h M K : ℕ) (Ns : σ → ℤ)
    (branches : A06.Branches σ) : Prop :=
  K ≤ M ∧
    (K : ℤ) + |Ns branches.rightSpecies| < (h : ℤ) ∧
    (K : ℤ) + |Ns branches.leftSpecies| < (h : ℤ)

noncomputable def zeroModeEnergyScalar {σ : Type*} (h : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) : ℝ :=
  let L : ℝ := ((2 * h : ℕ) : ℝ)
  let nr : ℝ := (Ns branches.rightSpecies : ℝ)
  let nl : ℝ := (Ns branches.leftSpecies : ℝ)
  (2 * Real.pi * vF / L) * (nr * (nr + 1) / 2 + nl * (nl + 1) / 2) +
    (g4 / (2 * L)) * (nr ^ 2 + nl ^ 2) +
    (g2 / L) * nr * nl -
    mu * (nr + nl)

noncomputable def symmetricZeroModeScalar {σ : Type*} (h : ℕ)
    (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) : ℝ :=
  let L : ℝ := ((2 * h : ℕ) : ℝ)
  let nr : ℝ := (Ns branches.rightSpecies : ℝ)
  let nl : ℝ := (Ns branches.leftSpecies : ℝ)
  (Real.pi * v1Velocity vF g4 / L) * (nr ^ 2 + nl ^ 2) +
    (g2 / L) * nr * nl

lemma zero_mode_scalar_canonical_mu {σ : Type*} (h : ℕ) (vF g4 g2 : ℝ)
    (branches : A06.Branches σ) (Ns : σ → ℤ) :
    zeroModeEnergyScalar h vF g4 g2 (canonicalMu h vF) branches Ns =
      symmetricZeroModeScalar h vF g4 g2 branches Ns := by
  unfold zeroModeEnergyScalar symmetricZeroModeScalar canonicalMu v1Velocity
  dsimp
  by_cases hh : h = 0
  · simp [hh]
  · have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    field_simp
    ring

end ScalarParameters

section LuttingerHamiltonians

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def chemicalPotentialOp (h : ℕ) (mu : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (mu : ℂ) • (A05.chargeObservable h branches.rightSpecies +
    A05.chargeObservable h branches.leftSpecies)

noncomputable def freeSugawaraKinetic (h M : ℕ) (vF : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  let prefactor : ℂ := ((2 * Real.pi * vF : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)
  prefactor • (Ch16.sugawara h M branches +
    ((2 : ℂ)⁻¹) • (A05.chargeObservable h r * (A05.chargeObservable h r + 1) +
      A05.chargeObservable h l * (A05.chargeObservable h l + 1)))

noncomputable def freeFermionKinetic (h : ℕ) (vF : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let prefactor : ℂ := ((2 * Real.pi * vF : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)
  prefactor •
    (A07Interactions.computationalMomentum h branches.rightSpecies +
      A07Interactions.computationalMomentum h branches.leftSpecies)

noncomputable def zeroModeEnergyOp (h : ℕ) (vF g4 g2 mu : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let L : ℂ := ((2 * h : ℕ) : ℂ)
  let nr := A05.chargeObservable h branches.rightSpecies
  let nl := A05.chargeObservable h branches.leftSpecies
  (((2 * Real.pi * vF : ℝ) : ℂ) / L) •
      (((2 : ℂ)⁻¹) • (nr * (nr + 1) + nl * (nl + 1))) +
    ((g4 : ℂ) / (2 * L)) • (nr * nr + nl * nl) +
    ((g2 : ℂ) / L) • (nr * nl) -
    chemicalPotentialOp h mu branches

noncomputable def luttingerOscillatorOp (h M : ℕ) (vF g4 g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (((2 * Real.pi : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)) •
    ∑ m ∈ Finset.Icc 1 M,
      A07Interactions.pairingMode h m
        (v1Velocity vF g4) (v2Velocity g2) branches

noncomputable def luttingerBosonizedHamiltonian (h M : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    A05.Operators σ h :=
  luttingerOscillatorOp h M vF g4 g2 branches +
    zeroModeEnergyOp h vF g4 g2 mu branches

noncomputable def luttingerChosenModel (h M : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    A05.Operators σ h :=
  freeSugawaraKinetic h M vF branches +
    A07Interactions.currentIntraBranch h M g4 branches +
    A07Interactions.pairingInterBranch h M g2 branches -
    chemicalPotentialOp h mu branches

noncomputable def luttingerFermionChosenModel (h M : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    A05.Operators σ h :=
  freeFermionKinetic h vF branches +
    A07Interactions.currentIntraBranch h M g4 branches +
    A07Interactions.pairingInterBranch h M g2 branches -
    chemicalPotentialOp h mu branches

theorem luttinger_chosen_eq_bosonized (h M : ℕ) (vF g4 g2 mu : ℝ)
    (branches : A06.Branches σ) :
    luttingerChosenModel h M vF g4 g2 mu branches =
      luttingerBosonizedHamiltonian h M vF g4 g2 mu branches := by
  have h1 : (((2 * Real.pi : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)) *
      (v1Velocity vF g4 : ℂ) =
      (((2 * Real.pi * vF : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)) +
        (g4 : ℂ) / ((2 * h : ℕ) : ℂ) := by
    unfold v1Velocity
    push_cast
    field_simp
  have h2 : (((2 * Real.pi : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)) *
      (v2Velocity g2 : ℂ) = (g2 : ℂ) / ((2 * h : ℕ) : ℂ) := by
    unfold v2Velocity
    push_cast
    field_simp
  unfold luttingerChosenModel luttingerBosonizedHamiltonian freeSugawaraKinetic
    A07Interactions.currentIntraBranch A07Interactions.speciesCurrentIntra
    A07Interactions.pairingInterBranch luttingerOscillatorOp zeroModeEnergyOp
    Ch16.sugawara A07Interactions.pairingMode
  simp only [smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
  simp_rw [h1, h2]
  simp only [add_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
  simp only [A06.speciesOf]
  module


lemma zero_mode_op_on_budget (h K : ℕ) (vF g4 g2 mu : ℝ)
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    zeroModeEnergyOp h vF g4 g2 mu branches v =
      (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v := by
  have hcharge (ν : σ) := A05.charge_budget h ν Ns K v hv
  unfold zeroModeEnergyOp chemicalPotentialOp
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, Module.End.one_apply, map_add, map_smul, hcharge]
  simp only [← add_smul, ← sub_smul, smul_smul]
  congr 1
  unfold zeroModeEnergyScalar
  push_cast
  ring

theorem free_fermion_eq_sugawara_on_budget (h M K : ℕ) (hh : 0 < h)
    (vF : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hSug : sugawaraMargin h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    freeFermionKinetic h vF branches v =
      freeSugawaraKinetic h M vF branches v := by sorry

theorem luttinger_hamiltonian_on_budget (h M K : ℕ) (hh : 0 < h)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hSug : sugawaraMargin h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    luttingerFermionChosenModel h M vF g4 g2 mu branches v =
      luttingerOscillatorOp h M vF g4 g2 branches v +
        (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v := by
  have hfree := free_fermion_eq_sugawara_on_budget h M K hh vF branches Ns hN hSug v hv
  calc
    _ = luttingerChosenModel h M vF g4 g2 mu branches v := by
      simp only [luttingerFermionChosenModel, luttingerChosenModel,
        LinearMap.add_apply, LinearMap.sub_apply, hfree]
    _ = _ := by
      rw [luttinger_chosen_eq_bosonized]
      simp only [luttingerBosonizedHamiltonian, LinearMap.add_apply,
        zero_mode_op_on_budget h K vF g4 g2 mu branches Ns v hv]

theorem luttinger_hamiltonian_canonical_mu_on_budget (h M K : ℕ) (hh : 0 < h)
    (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hSug : sugawaraMargin h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    luttingerFermionChosenModel h M vF g4 g2 (canonicalMu h vF) branches v =
      luttingerOscillatorOp h M vF g4 g2 branches v +
        (symmetricZeroModeScalar h vF g4 g2 branches Ns : ℂ) • v := by
  rw [luttinger_hamiltonian_on_budget h M K hh vF g4 g2 (canonicalMu h vF)
    branches Ns hN hSug v hv, zero_mode_scalar_canonical_mu]

theorem luttinger_raw_intra_on_budget (h M K : ℕ) (hh : 0 < h)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hSug : sugawaraMargin h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    (freeFermionKinetic h vF branches +
      A07Interactions.rawIntraBranch h M g4 branches +
      A07Interactions.pairingInterBranch h M g2 branches -
      chemicalPotentialOp h mu branches) v =
      luttingerOscillatorOp h M vF g4 g2 branches v +
        (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v -
        (((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
          (A07Interactions.seaWickCorrection h M branches.rightSpecies +
            A07Interactions.seaWickCorrection h M branches.leftSpecies)) v := by
  rw [A07Interactions.raw_intra_eq_current_sub_correction]
  have hmodel := luttinger_hamiltonian_on_budget h M K hh vF g4 g2 mu branches Ns hN hSug v hv
  have heq : freeFermionKinetic h vF branches +
      (A07Interactions.currentIntraBranch h M g4 branches -
        ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
          (A07Interactions.seaWickCorrection h M branches.rightSpecies +
           A07Interactions.seaWickCorrection h M branches.leftSpecies)) +
      A07Interactions.pairingInterBranch h M g2 branches - chemicalPotentialOp h mu branches =
      luttingerFermionChosenModel h M vF g4 g2 mu branches -
        ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
          (A07Interactions.seaWickCorrection h M branches.rightSpecies +
           A07Interactions.seaWickCorrection h M branches.leftSpecies) := by
    unfold luttingerFermionChosenModel
    abel
  rw [heq, LinearMap.sub_apply, hmodel]

theorem concrete_luttinger_witness :
    let Ns : Fin 2 → ℤ := fun _ => 0
    A05.admissible 8 Ns ∧
      A06.branchMargins 8 2 2 Ns Ch16.standardBranches ∧
      sugawaraMargin 8 2 2 Ns Ch16.standardBranches ∧
      A05.groundKet 8 Ns ∈ A05.jointBudget 8 Ns 2 ∧
      A05.groundKet 8 Ns ≠ 0 ∧
      luttingerBosonizedHamiltonian 8 2 1 (6 * Real.pi) (6 * Real.pi)
        (canonicalMu 8 1) Ch16.standardBranches (A05.groundKet 8 Ns) ≠ 0 := by
  have hnonzero {τ : Type} [Fintype τ] [LinearOrder τ]
      (h : ℕ) (hh : 8 ≤ h) (branches : A06.Branches τ) :
      luttingerBosonizedHamiltonian h 2 1 (6 * Real.pi) (6 * Real.pi)
        (canonicalMu h 1) branches (A05.groundKet h (fun _ : τ => 0)) ≠ 0 := by
    let Ns : τ → ℤ := fun _ => 0
    have hN : A05.admissible h Ns := by intro ν; simp only [Ch07.admissible, Ns]; omega
    have hg := A05.ground_mem_budget h (by omega) Ns hN 0
    let g := A05.groundKet h Ns
    let R : ℤ → A05.Operators (τ) h := A05.rho h branches.rightSpecies
    let L : ℤ → A05.Operators (τ) h := A05.rho h branches.leftSpecies
    have hkill (ν : τ) (m : ℕ) (hm : 1 ≤ m) :
        A05.rho h ν (-(m : ℤ)) g = 0 := by
      exact A05.rho_lowering_budget_zero h (by omega) ν m 0 (by omega) Ns g hg
    have hcross (a b : ℤ) : L a * R b = R b * L a := by
      have hc := A05.rho_cross_commute h branches.leftSpecies
        branches.rightSpecies branches.distinct.symm a b
      change L a * R b - R b * L a = 0 at hc
      exact sub_eq_zero.mp hc
    have hsingle (ν : τ) (m : ℕ) (hm : 1 ≤ m) (hm2 : m ≤ 2) :
        A05.rho h ν (-1) (A05.rho h ν (m : ℤ) g) =
          (if m = 1 then (1 : ℂ) else 0) • g := by
      have hc := A06.joint_signed_current_commutator h 0 (by omega) Ns ν (-1) (m : ℤ)
        (by simp only [Ns, abs_neg, abs_one, abs_of_nonneg (Int.natCast_nonneg m),
          Nat.cast_zero, abs_zero]; omega) g hg
      simp only [A02.commutator, Module.End.mul_apply, LinearMap.sub_apply,
        show A05.rho h ν (-1) g = 0 from hkill ν 1 (by omega), map_zero, sub_zero] at hc
      rw [hc]
      congr 1
      by_cases he : m = 1
      · simp [Ch10.schwingerCoefficient, he]
      · have hz : (-1 : ℤ) + (m : ℤ) ≠ 0 := by omega
        simp [Ch10.schwingerCoefficient, hz, he]
    have hd (m : ℕ) (hm : 1 ≤ m) (hm2 : m ≤ 2) :
        (R (-1) * L (-1)) ((R (m : ℤ) * L (m : ℤ) +
            R (-(m : ℤ)) * L (-(m : ℤ))) g) =
        (if m = 1 then (1 : ℂ) else 0) • g := by
      have hc := congrArg (fun T : A05.Operators (τ) h => T (L (m : ℤ) g))
        (hcross (-1) (m : ℤ))
      simp only [Module.End.mul_apply] at hc
      simp only [LinearMap.add_apply, Module.End.mul_apply, map_add]
      rw [hkill branches.leftSpecies m hm, map_zero, map_zero, map_zero, add_zero,
        hc, hsingle branches.leftSpecies m hm hm2]
      by_cases he : m = 1
      · simp only [he, ite_true, one_smul]
        simpa only [ite_true, one_smul] using hsingle branches.rightSpecies 1 (by omega) (by omega)
      · simp only [he, ite_false, zero_smul, map_zero]
    have hdiag (m : ℕ) (hm : 1 ≤ m) :
        (R (m : ℤ) * R (-(m : ℤ)) + L (m : ℤ) * L (-(m : ℤ))) g = 0 := by
      simp only [LinearMap.add_apply, Module.End.mul_apply, R, L]
      rw [hkill branches.rightSpecies m hm, hkill branches.leftSpecies m hm]
      simp only [map_zero, add_zero]
    have hmode (m : ℕ) (hm : 1 ≤ m) (hm2 : m ≤ 2) :
        (R (-1) * L (-1))
          (A07Interactions.pairingMode h m (v1Velocity 1 (6 * Real.pi))
            (v2Velocity (6 * Real.pi)) branches g) =
        (if m = 1 then (3 : ℂ) else 0) • g := by
      unfold A07Interactions.pairingMode
      change (R (-1) * L (-1))
        (((v1Velocity 1 (6 * Real.pi) : ℂ) •
            (R (m : ℤ) * R (-(m : ℤ)) + L (m : ℤ) * L (-(m : ℤ))) +
          (v2Velocity (6 * Real.pi) : ℂ) •
            (R (m : ℤ) * L (m : ℤ) + R (-(m : ℤ)) * L (-(m : ℤ)))) g) = _
      rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hdiag m hm]
      simp only [smul_zero, zero_add, map_smul]
      rw [hd m hm hm2, smul_smul]
      have hv : v2Velocity (6 * Real.pi) = 3 := by
        unfold v2Velocity
        field_simp
        norm_num
      rw [hv]
      by_cases he : m = 1 <;> simp [he]
    intro hz
    have hz' : luttingerBosonizedHamiltonian h 2 1 (6 * Real.pi) (6 * Real.pi)
        (canonicalMu h 1) branches g = 0 := by simpa only [g, Ns] using hz
    have he := congrArg (fun v : A05.FockSpace τ h => (R (-1) * L (-1)) v) hz'
    rw [map_zero] at he
    have hzero := zero_mode_op_on_budget h 2 1 (6 * Real.pi) (6 * Real.pi)
      (canonicalMu h 1) branches Ns g (A05.ground_mem_budget h (by omega) Ns hN 2)
    have hscalar : zeroModeEnergyScalar h 1 (6 * Real.pi) (6 * Real.pi)
        (canonicalMu h 1) branches Ns = 0 := by simp [zeroModeEnergyScalar, Ns]
    rw [hscalar, Complex.ofReal_zero, zero_smul] at hzero
    unfold luttingerBosonizedHamiltonian at he
    rw [LinearMap.add_apply, hzero, add_zero] at he
    unfold luttingerOscillatorOp at he
    simp only [LinearMap.smul_apply, map_smul, LinearMap.sum_apply, map_sum] at he
    have hsum : (∑ m ∈ Finset.Icc 1 2,
        (R (-1) * L (-1)) (A07Interactions.pairingMode h m
          (v1Velocity 1 (6 * Real.pi)) (v2Velocity (6 * Real.pi)) branches g)) = (3 : ℂ) • g := by
      rw [show Finset.Icc 1 2 = {1,2} by decide]
      simp only [Finset.sum_insert, Finset.mem_singleton, Finset.sum_singleton,
        show (1 : ℕ) ≠ 2 by omega, not_false_eq_true, hmode 1 (by omega) (by omega),
        hmode 2 (by omega) (by omega), ite_true, show ¬ (2 : ℕ) = 1 by omega,
        ite_false, zero_smul, add_zero]
    rw [hsum, smul_smul] at he
    have hc : (((2 * Real.pi : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)) * 3 ≠ 0 := by
      apply mul_ne_zero
      · apply div_ne_zero
        · exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
        · exact_mod_cast (show 2 * h ≠ 0 by omega)
      · norm_num
    exact (smul_eq_zero.mp he).elim hc (A05.ground_ne_zero h Ns)
  let Ns : Fin 2 → ℤ := fun _ => 0
  have hN : A05.admissible 8 Ns := by intro ν; norm_num [Ns, Ch07.admissible]
  have hb : A06.branchMargins 8 2 2 Ns Ch16.standardBranches := by
    norm_num [A06.branchMargins, A06.marginAt, Ns]
  have hs : sugawaraMargin 8 2 2 Ns Ch16.standardBranches := by
    norm_num [sugawaraMargin, Ns]
  exact ⟨hN, hb, hs, A05.ground_mem_budget 8 (by omega) Ns hN 2,
    A05.ground_ne_zero 8 Ns, hnonzero 8 (by omega) Ch16.standardBranches⟩


end LuttingerHamiltonians

end Bosonize.Ch17
