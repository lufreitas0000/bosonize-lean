import Bosonize.Core.Ch17LuttingerModels
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! S5 staging: vector states of the actual finite compressed Chapter 17 model.
No ambient ground-state claim and no uniqueness assertion in degenerate sectors. -/
@[expose] public section
namespace Bosonize.V1S5
open scoped BigOperators

section FiniteState
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A selected pure ground state; the inequality holds for every vector. -/
structure GroundVector (H : Module.End ℂ E) where
  energy : ℝ
  ket : E
  unit : ‖ket‖ = 1
  eigen : H ket = (energy : ℂ) • ket
  minimal : ∀ v : E, energy * ‖v‖ ^ 2 ≤ (inner ℂ v (H v)).re

noncomputable def vectorState (v : E) : Module.End ℂ E →ₗ[ℂ] ℂ where
  toFun X := inner ℂ v (X v)
  map_add' X Y := by simp [inner_add_right]
  map_smul' a X := by simp [inner_smul_right]

theorem vector_state_one (v : E) (hv : ‖v‖ = 1) :
    vectorState v 1 = 1 := by sorry

theorem vector_state_positive (v : E) (X : Module.End ℂ E) :
    vectorState v (LinearMap.adjoint X * X) = (‖X v‖ ^ 2 : ℝ) := by sorry

theorem ground_vector_exists [Nontrivial E] (H : Module.End ℂ E)
    (hH : H.IsSymmetric) : Nonempty (GroundVector H) := by sorry

theorem ground_energy_evaluation (H : Module.End ℂ E) (g : GroundVector H) :
    vectorState g.ket H = (g.energy : ℂ) := by sorry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

noncomputable def compression (i : E →ₗ[ℂ] F) (X : Module.End ℂ F) :
    Module.End ℂ E := (LinearMap.adjoint i).comp (X.comp i)

noncomputable def extendedState (i : E →ₗ[ℂ] F) (v : E) :
    Module.End ℂ F →ₗ[ℂ] ℂ where
  toFun X := vectorState v (compression i X)
  map_add' X Y := by simp [vectorState, compression, inner_add_right]
  map_smul' a X := by simp [vectorState, compression, inner_smul_right]

theorem extended_state_vector (i : E →ₗ[ℂ] F) (v : E) (X : Module.End ℂ F) :
    extendedState i v X = vectorState (i v) X := by sorry

theorem extended_state_one (i : E →ₗ[ℂ] F) (hi : ∀ v, ‖i v‖ = ‖v‖)
    (v : E) (hv : ‖v‖ = 1) : extendedState i v 1 = 1 := by sorry

theorem extended_state_positive (i : E →ₗ[ℂ] F) (v : E) (X : Module.End ℂ F) :
    extendedState i v (LinearMap.adjoint X * X) = (‖X (i v)‖ ^ 2 : ℝ) := by sorry

theorem compression_symmetric (i : E →ₗ[ℂ] F) (X : Module.End ℂ F)
    (hX : X.IsSymmetric) : (compression i X).IsSymmetric := by sorry
end FiniteState

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
    (hN : A05.admissible h Ns) : Nontrivial (Budget h Ns K) := by sorry

theorem inclusion_isometric (h K : ℕ) (Ns : σ → ℤ) :
    ∀ v : Budget h Ns K, ‖inclusion h Ns K v‖ = ‖v‖ := by sorry

theorem inclusion_adjoint_inclusion (h K : ℕ) (Ns : σ → ℤ) :
    (LinearMap.adjoint (𝕜 := ℂ) (E := Budget h Ns K) (F := A05.FockSpace σ h) (inclusion h Ns K)).comp (inclusion h Ns K) =
      LinearMap.id := by sorry

theorem inclusion_projection (h K : ℕ) (Ns : σ → ℤ) :
    (inclusion h Ns K).comp (LinearMap.adjoint (𝕜 := ℂ) (E := Budget h Ns K) (F := A05.FockSpace σ h) (inclusion h Ns K)) =
      A03.coordinateProjection {S | (∀ ν, Ch07.relativeCharge h
        (Ch07.speciesConfiguration h S ν) = Ns ν) ∧ Ch07.totalExcitation h S ≤ (K : ℤ)} := by sorry

theorem ambient_hamiltonian_self_adjoint (h M : ℕ) (vF g4 g2 mu : ℝ)
    (branches : A06.Branches σ) :
    LinearMap.adjoint (ambientHamiltonian h M vF g4 g2 mu branches) =
      ambientHamiltonian h M vF g4 g2 mu branches := by sorry

theorem budget_hamiltonian_symmetric (h M K : ℕ) (Ns : σ → ℤ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := Budget h Ns K) (budgetHamiltonian h M K Ns vF g4 g2 mu branches) := by sorry

theorem physical_ground_exists (h M K : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    Nonempty (GroundVector (E := Budget h Ns K) (budgetHamiltonian h M K Ns vF g4 g2 mu branches)) := by sorry

end PhysicalModel
end Bosonize.V1S5
