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
      symmetricZeroModeScalar h vF g4 g2 branches Ns := by sorry

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
      luttingerBosonizedHamiltonian h M vF g4 g2 mu branches := by sorry

lemma zero_mode_op_on_budget (h K : ℕ) (vF g4 g2 mu : ℝ)
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    zeroModeEnergyOp h vF g4 g2 mu branches v =
      (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v := by sorry

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
        (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v := by sorry

theorem luttinger_hamiltonian_canonical_mu_on_budget (h M K : ℕ) (hh : 0 < h)
    (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hSug : sugawaraMargin h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    luttingerFermionChosenModel h M vF g4 g2 (canonicalMu h vF) branches v =
      luttingerOscillatorOp h M vF g4 g2 branches v +
        (symmetricZeroModeScalar h vF g4 g2 branches Ns : ℂ) • v := by sorry

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
            A07Interactions.seaWickCorrection h M branches.leftSpecies)) v := by sorry

theorem concrete_luttinger_witness :
    let Ns : Fin 2 → ℤ := fun _ => 0
    A05.admissible 8 Ns ∧
      A06.branchMargins 8 2 2 Ns Ch16.standardBranches ∧
      sugawaraMargin 8 2 2 Ns Ch16.standardBranches ∧
      A05.groundKet 8 Ns ∈ A05.jointBudget 8 Ns 2 ∧
      A05.groundKet 8 Ns ≠ 0 ∧
      luttingerBosonizedHamiltonian 8 2 1 (6 * Real.pi) (6 * Real.pi)
        (canonicalMu 8 1) Ch16.standardBranches (A05.groundKet 8 Ns) ≠ 0 := by sorry

end LuttingerHamiltonians

end Bosonize.Ch17
