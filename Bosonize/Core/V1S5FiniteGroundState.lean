import Bosonize.Core.Ch17LuttingerModels
import Bosonize.Core.V1S5FiniteVectorStates

/-! S5 staging: the actual finite compressed Chapter 17 pairing Hamiltonian. -/
@[expose] public section
namespace Bosonize.V1S5
open scoped BigOperators

section PhysicalModel
variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable abbrev Budget (h : ℕ) (Ns : σ → ℤ) (K : ℕ) : Type _ := ↥(A05.jointBudget h Ns K)

noncomputable def inclusion (h : ℕ) (Ns : σ → ℤ) (K : ℕ) :
    Budget h Ns K →ₗ[ℂ] A05.FockSpace σ h := (A05.jointBudget h Ns K).subtype

/-- The accepted current-normal-ordered Chapter 17 pairing Hamiltonian,
including its full charge observable zero-mode operator and chemical potential.
There is no added vacuum/Bogoliubov constant. -/
noncomputable def ambientHamiltonian (h M : ℕ) (vF g4 g2 mu : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  Ch17.luttingerBosonizedHamiltonian h M vF g4 g2 mu branches

noncomputable def budgetHamiltonian (h M K : ℕ) (Ns : σ → ℤ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) : Module.End ℂ (Budget h Ns K) :=
  compression (E := Budget h Ns K) (F := A05.FockSpace σ h) (inclusion h Ns K) (ambientHamiltonian h M vF g4 g2 mu branches)

theorem budget_nontrivial (h K : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) : Nontrivial (Budget h Ns K) := by
  let v : Budget h Ns K := ⟨A05.groundKet h Ns, A05.ground_mem_budget h hh Ns hN K⟩
  have hv : v ≠ 0 := by
    intro hz
    exact A05.ground_ne_zero h Ns (congrArg Subtype.val hz)
  exact ⟨⟨v, 0, hv⟩⟩

theorem inclusion_isometric (h K : ℕ) (Ns : σ → ℤ) :
    ∀ v : Budget h Ns K, ‖inclusion h Ns K v‖ = ‖v‖ := by
  intro v
  rfl

set_option maxHeartbeats 2000000 in
theorem inclusion_adjoint_inclusion (h K : ℕ) (Ns : σ → ℤ) :
    (LinearMap.adjoint (𝕜 := ℂ) (E := Budget h Ns K) (F := A05.FockSpace σ h) (inclusion h Ns K)).comp (inclusion h Ns K) =
      LinearMap.id := by
  exact submodule_inclusion_adjoint (E := A05.FockSpace σ h) (A05.jointBudget h Ns K)

theorem inclusion_projection (h K : ℕ) (Ns : σ → ℤ) :
    (inclusion h Ns K).comp (LinearMap.adjoint (𝕜 := ℂ) (E := Budget h Ns K) (F := A05.FockSpace σ h) (inclusion h Ns K)) =
      A03.coordinateProjection {S | (∀ ν, Ch07.relativeCharge h
        (Ch07.speciesConfiguration h S ν) = Ns ν) ∧ Ch07.totalExcitation h S ≤ (K : ℤ)} := by
  let U := {S | (∀ ν, Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = Ns ν) ∧
    Ch07.totalExcitation h S ≤ (K : ℤ)}
  let P := A03.coordinateProjection U
  have hm (v : A05.FockSpace σ h) : P v ∈ A05.jointBudget h Ns K := by
    change P v ∈ A03.coordinateSpace U
    rw [← A03.projection_range]
    exact ⟨v, rfl⟩
  let r : A05.FockSpace σ h →ₗ[ℂ] Budget h Ns K := P.codRestrict _ hm
  have hr : r = LinearMap.adjoint (𝕜 := ℂ) (E := Budget h Ns K) (F := A05.FockSpace σ h) (inclusion h Ns K) := by
    apply (LinearMap.eq_adjoint_iff (𝕜 := ℂ) (E := A05.FockSpace σ h)
      (F := Budget h Ns K) r (inclusion h Ns K)).mpr
    intro v w
    change inner ℂ (P v) (inclusion h Ns K w) = inner ℂ v (inclusion h Ns K w)
    calc
      _ = inner ℂ ((LinearMap.adjoint P) v) (inclusion h Ns K w) := by
        rw [show LinearMap.adjoint P = P from A03.projection_adjoint U]
      _ = inner ℂ v (P (inclusion h Ns K w)) := LinearMap.adjoint_inner_left P _ _
      _ = _ := by
        congr 1
        exact (A03.projection_fixed_iff U _).mpr w.property
  rw [← hr]
  rfl


theorem ambient_hamiltonian_self_adjoint (h M : ℕ) (vF g4 g2 mu : ℝ)
    (branches : A06.Branches σ) :
    LinearMap.adjoint (ambientHamiltonian h M vF g4 g2 mu branches) =
      ambientHamiltonian h M vF g4 g2 mu branches := by
  let : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
  have hq (ν : σ) : LinearMap.adjoint (A05.chargeObservable h ν) = A05.chargeObservable h ν := by
    unfold A05.chargeObservable
    rw [A03.diagonal_adjoint]
    congr 1
    funext S
    simp
  have hc : A05.chargeObservable h branches.leftSpecies * A05.chargeObservable h branches.rightSpecies =
      A05.chargeObservable h branches.rightSpecies * A05.chargeObservable h branches.leftSpecies := by
    apply A02.end_ext_basis
    intro S
    simp [A05.chargeObservable, Module.End.mul_apply, A03.diagonal_ket, smul_smul, mul_comm]
  have hmul (X Y : A05.Operators σ h) :
      LinearMap.adjoint (X * Y) = LinearMap.adjoint Y * LinearMap.adjoint X :=
    LinearMap.adjoint_comp X Y
  have ho : LinearMap.adjoint (Ch17.luttingerOscillatorOp h M vF g4 g2 branches) =
      Ch17.luttingerOscillatorOp h M vF g4 g2 branches := by
    unfold Ch17.luttingerOscillatorOp
    simp only [map_smulₛₗ, map_sum, A07Interactions.pairing_mode_self_adjoint]
    simp only [map_div₀, map_natCast, Complex.conj_ofReal]
  have hz : LinearMap.adjoint (Ch17.zeroModeEnergyOp h vF g4 g2 mu branches) =
      Ch17.zeroModeEnergyOp h vF g4 g2 mu branches := by
    unfold Ch17.zeroModeEnergyOp Ch17.chemicalPotentialOp
    simp only [map_add, map_sub, map_smulₛₗ, hmul, hq, LinearMap.adjoint_one]
    simp only [map_div₀, map_mul, map_ofNat, map_natCast, map_inv₀, Complex.conj_ofReal, hc]
    noncomm_ring
  unfold ambientHamiltonian Ch17.luttingerBosonizedHamiltonian
  rw [map_add, ho, hz]


theorem budget_hamiltonian_symmetric (h M K : ℕ) (Ns : σ → ℤ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := Budget h Ns K) (budgetHamiltonian h M K Ns vF g4 g2 mu branches) := by
  apply compression_symmetric
  intro v w
  rw [← LinearMap.adjoint_inner_left]
  rw [ambient_hamiltonian_self_adjoint]

theorem physical_ground_exists (h M K : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    Nonempty (GroundVector (E := Budget h Ns K) (budgetHamiltonian h M K Ns vF g4 g2 mu branches)) := by
  let _ := budget_nontrivial h K hh Ns hN
  exact ground_vector_exists _ (budget_hamiltonian_symmetric h M K Ns vF g4 g2 mu branches)

end PhysicalModel
end Bosonize.V1S5
