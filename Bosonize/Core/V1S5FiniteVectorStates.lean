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

omit [FiniteDimensional ℂ E] in
theorem finite_plane_rotation_orthonormal (v : Fin 8 → E) (hv : Orthonormal ℂ v) (t a : ℝ)
    (ha : a ^ 2 * (1 + t ^ 2) = 1) :
    Orthonormal ℂ (fun j : Fin 8 =>
      if j = 0 then (a : ℂ) • (v 0 - (t : ℂ) • v 5)
      else if j = 5 then (a : ℂ) • ((t : ℂ) • v 0 + v 5) else v j) := by
  have hc : (a : ℂ) ^ 2 * (1 + (t : ℂ) ^ 2) = 1 := by exact_mod_cast ha
  have hg := orthonormal_iff_ite.mp hv
  rw [orthonormal_iff_ite]
  intro i j
  have h05 : (0 : Fin 8) ≠ 5 := by decide
  by_cases hi0 : i = 0 <;>
    by_cases hi5 : i = 5 <;>
    by_cases hj0 : j = 0 <;>
    by_cases hj5 : j = 5
  all_goals simp_all only [Ne.symm h05, ite_true, ite_false, inner_sub_left,
    inner_sub_right, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, mul_zero, zero_add, add_zero, mul_one,
    sub_zero, sub_self, eq_self]
  all_goals try (have hn0 := Ne.symm hj0; have hn5 := Ne.symm hj5; simp only [hn0, hn5, ite_false, mul_zero, add_zero, sub_zero])
  all_goals first | ring1 | linear_combination hc

set_option maxHeartbeats 2000000 in
omit [FiniteDimensional ℂ E] in
theorem finite_plane_diagonalization (v : OrthonormalBasis (Fin 8) ℂ E) (A : Module.End ℂ E)
    (p t D a : ℝ) (ha : a^2*(1+t^2)=1)
    (ht : t*(17+D)=15) (ht' : 15*t=D-17)
    (hA : ∀ j, A (v j) = ∑ i : Fin 8,
      ((p : ℂ) * (if (i=0 ∧ j=5) ∨ (i=5 ∧ j=0) then 15 else if i=j then
      if i=0 then 0 else if i=1 ∨ i=2 then 17 else 34 else 0)) • v i) :
    ∃ b : OrthonormalBasis (Fin 8) ℂ E,
      b 0 = (a:ℂ) • (v 0 - (t:ℂ) • v 5) ∧
      ∀ j, A (b j) = ((p * (if j=0 then 17-D else if j=5 then 17+D else
        if j=1 ∨ j=2 then 17 else 34) : ℝ) : ℂ) • b j := by
  let w (j : Fin 8) := if j=0 then (a:ℂ) • (v 0 - (t:ℂ) • v 5)
    else if j=5 then (a:ℂ) • ((t:ℂ) • v 0 + v 5) else v j
  have hon : Orthonormal ℂ w := finite_plane_rotation_orthonormal v v.orthonormal t a ha
  have hdim : Module.finrank ℂ E = Fintype.card (Fin 8) := Module.finrank_eq_card_basis v.toBasis
  have hspan := hon.linearIndependent.span_eq_top_of_card_eq_finrank hdim.symm
  let b := OrthonormalBasis.mk hon hspan.ge
  refine ⟨b, ?_, ?_⟩
  · simp only [b, OrthonormalBasis.coe_mk, w, ite_true]
  intro j
  simp only [b, OrthonormalBasis.coe_mk]
  apply v.repr.injective
  ext k
  have hc : (t:ℂ)*(17+(D:ℂ))=15 := by exact_mod_cast ht
  have hc' : 15*(t:ℂ)=(D:ℂ)-17 := by exact_mod_cast ht'
  fin_cases j <;> fin_cases k <;>
    norm_num [w, map_smul, map_add, map_sub, hA, Fin.sum_univ_succ,
      OrthonormalBasis.repr_apply_apply, inner_smul_right, inner_smul_right_eq_smul, inner_sub_right, inner_add_right,
      inner_sum, orthonormal_iff_ite.mp v.orthonormal]
  all_goals first | linear_combination (p:ℂ)*(a:ℂ)*hc | linear_combination (p:ℂ)*(a:ℂ)*hc' | linear_combination -(p:ℂ)*(a:ℂ)*hc | linear_combination -(p:ℂ)*(a:ℂ)*hc'

theorem compression_inner (i : E →ₗ[ℂ] F) (X : Module.End ℂ F) (v w : E) :
    inner ℂ v (compression i X w) = inner ℂ (i v) (X (i w)) := by
  exact LinearMap.adjoint_inner_right i v (X (i w))

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
