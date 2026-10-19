module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! S5 staging: finite-dimensional selected ground vectors and positive vector states. -/
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

omit [FiniteDimensional ℂ E] in
theorem vector_state_one (v : E) (hv : ‖v‖ = 1) :
    vectorState v 1 = 1 := by
  simp [vectorState, inner_self_eq_norm_sq_to_K, hv]

theorem vector_state_positive (v : E) (X : Module.End ℂ E) :
    vectorState v (LinearMap.adjoint X * X) = (‖X v‖ ^ 2 : ℝ) := by
  simp [vectorState, Module.End.mul_apply, LinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]

theorem ground_vector_exists [Nontrivial E] (H : Module.End ℂ E)
    (hH : H.IsSymmetric) : Nonempty (GroundVector H) := by
  let _ := FiniteDimensional.complete ℂ E
  let T := (hH.toSelfAdjoint : E →L[ℂ] E)
  let e : ℝ := ⨅ x : {x : E // x ≠ 0}, (inner ℂ (H x) x).re / ‖(x : E)‖ ^ 2
  have hb : BddBelow (Set.range fun x : {x : E // x ≠ 0} =>
      (inner ℂ (H x) x).re / ‖(x : E)‖ ^ 2) := by
    refine ⟨-‖T‖, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (abs_le.mp (T.rayleighQuotient_le_norm x)).1
  obtain ⟨x, hx⟩ := hH.hasEigenvalue_iInf_of_finiteDimensional.exists_hasEigenvector
  have hx0 : x ≠ 0 := hx.2
  let v := ((‖x‖⁻¹ : ℝ) : ℂ) • x
  have hu : ‖v‖ = 1 := by
    simp [v, norm_smul, hx0]
  refine ⟨⟨e, v, hu, ?_, ?_⟩⟩
  · change H (((‖x‖⁻¹ : ℝ) : ℂ) • x) = _
    rw [map_smul, hx.apply_eq_smul]
    change ((‖x‖⁻¹ : ℝ) : ℂ) • ((e : ℂ) • x) = (e : ℂ) • _
    exact smul_comm _ _ _
  · intro w
    by_cases hw : w = 0
    · subst w; simp
    · have he := ciInf_le hb (⟨w, hw⟩ : {x : E // x ≠ 0})
      have hpos : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
      have hh := (le_div_iff₀ hpos).mp he
      calc
        _ ≤ (inner ℂ (H w) w).re := hh
        _ = (inner ℂ w (H w)).re := inner_re_symm (𝕜 := ℂ) (H w) w

omit [FiniteDimensional ℂ E] in
theorem ground_energy_evaluation (H : Module.End ℂ E) (g : GroundVector H) :
    vectorState g.ket H = (g.energy : ℂ) := by
  change inner ℂ g.ket (H g.ket) = _
  rw [g.eigen, inner_smul_right, inner_self_eq_norm_sq_to_K, g.unit]
  norm_num

theorem submodule_inclusion_adjoint (W : Submodule ℂ E) :
    (LinearMap.adjoint (𝕜 := ℂ) W.subtype).comp W.subtype =
      (LinearMap.id : Module.End ℂ W) := by
  apply LinearMap.ext
  intro v
  refine ext_inner_left ℂ (fun w : W => ?_)
  exact LinearMap.adjoint_inner_right (𝕜 := ℂ) W.subtype w (v : E)

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
    extendedState i v X = vectorState (i v) X := by
  simp [extendedState, vectorState, compression, LinearMap.adjoint_inner_right]

theorem extended_state_one (i : E →ₗ[ℂ] F) (hi : ∀ v, ‖i v‖ = ‖v‖)
    (v : E) (hv : ‖v‖ = 1) : extendedState i v 1 = 1 := by
  rw [extended_state_vector]
  exact vector_state_one _ ((hi v).trans hv)

theorem extended_state_positive (i : E →ₗ[ℂ] F) (v : E) (X : Module.End ℂ F) :
    extendedState i v (LinearMap.adjoint X * X) = (‖X (i v)‖ ^ 2 : ℝ) := by
  rw [extended_state_vector]
  exact vector_state_positive _ _

theorem compression_symmetric (i : E →ₗ[ℂ] F) (X : Module.End ℂ F)
    (hX : X.IsSymmetric) : (compression i X).IsSymmetric := by
  exact hX.adjoint_conj i
end FiniteState

end Bosonize.V1S5
