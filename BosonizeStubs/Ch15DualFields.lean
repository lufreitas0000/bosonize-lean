import BosonizeStubs.A06ChiralFields

namespace Bosonize.Ch15

open scoped BigOperators

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def phiField (h M : ℕ) (ζ : ℂ)
    (branches : A06.Branches σ) (x : ZMod (2 * h)) : A05.Operators σ h :=
  A06.chiralField h M ζ branches .right x +
    A06.chiralField h M ζ branches .left x

noncomputable def thetaField (h M : ℕ) (ζ : ℂ)
    (branches : A06.Branches σ) (x : ZMod (2 * h)) : A05.Operators σ h :=
  A06.chiralField h M ζ branches .right x -
    A06.chiralField h M ζ branches .left x

lemma phi_adjoint (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ)
    (x : ZMod (2 * h)) :
    LinearMap.adjoint (phiField h M ζ branches x) =
      phiField h M ζ branches x := by
  unfold phiField
  rw [map_add, A06.chiral_adjoint h M ζ hζ branches .right x,
    A06.chiral_adjoint h M ζ hζ branches .left x]

lemma theta_adjoint (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ)
    (x : ZMod (2 * h)) :
    LinearMap.adjoint (thetaField h M ζ branches x) =
      thetaField h M ζ branches x := by
  unfold thetaField
  rw [map_sub, A06.chiral_adjoint h M ζ hζ branches .right x,
    A06.chiral_adjoint h M ζ hζ branches .left x]

lemma phi_self_commutator_on_budget (h M K : ℕ) (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (phiField h M ζ branches x)
      (phiField h M ζ branches y) v = 0 := by
  have _ := hM
  have _ := hNoAlias
  have hr := A06.chiral_same_commutator_on_budget h M K hh ζ hζ branches
    .right Ns hmargin.1 x y v hv
  have hl := A06.chiral_same_commutator_on_budget h M K hh ζ hζ branches
    .left Ns hmargin.2 x y v hv
  simp only [A06.orientationSign, Int.cast_one, Int.cast_neg, one_mul,
    neg_mul] at hr hl
  have hcross := A06.chiral_cross_commute h M ζ branches x y
  have hrev : A02.commutator (A06.chiralField h M ζ branches .left x)
      (A06.chiralField h M ζ branches .right y) = 0 := by
    have hc := A06.chiral_cross_commute h M ζ branches y x
    simp only [A02.commutator] at hc ⊢
    exact sub_eq_zero.mpr (sub_eq_zero.mp hc).symm
  have hbilinear (P Q R S : A05.Operators σ h) :
      A02.commutator (P + Q) (R + S) =
        A02.commutator P R + A02.commutator P S + A02.commutator Q R + A02.commutator Q S := by
    simp only [A02.commutator, add_mul, mul_add]
    abel
  unfold phiField
  rw [hbilinear]
  simp only [LinearMap.add_apply, hcross, hrev,
    LinearMap.zero_apply, hr, hl]
  module


lemma theta_self_commutator_on_budget (h M K : ℕ) (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (thetaField h M ζ branches x)
      (thetaField h M ζ branches y) v = 0 := by
  have _ := hM
  have _ := hNoAlias
  have hr := A06.chiral_same_commutator_on_budget h M K hh ζ hζ branches
    .right Ns hmargin.1 x y v hv
  have hl := A06.chiral_same_commutator_on_budget h M K hh ζ hζ branches
    .left Ns hmargin.2 x y v hv
  simp only [A06.orientationSign, Int.cast_one, Int.cast_neg, one_mul,
    neg_mul] at hr hl
  have hcross := A06.chiral_cross_commute h M ζ branches x y
  have hrev : A02.commutator (A06.chiralField h M ζ branches .left x)
      (A06.chiralField h M ζ branches .right y) = 0 := by
    have hc := A06.chiral_cross_commute h M ζ branches y x
    simp only [A02.commutator] at hc ⊢
    exact sub_eq_zero.mpr (sub_eq_zero.mp hc).symm
  have hbilinear (P Q R S : A05.Operators σ h) :
      A02.commutator (P - Q) (R - S) =
        A02.commutator P R - A02.commutator P S - A02.commutator Q R + A02.commutator Q S := by
    simp only [A02.commutator, sub_mul, mul_sub]
    abel
  unfold thetaField
  rw [hbilinear]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, hcross, hrev,
    LinearMap.zero_apply, hr, hl]
  module


lemma mixed_commutator_on_budget (h M K : ℕ) (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (phiField h M ζ branches x)
      (thetaField h M ζ branches y) v =
      (2 * A06.skewKernel h M ζ x y) • v := by
  have _ := hM
  have _ := hNoAlias
  have hr := A06.chiral_same_commutator_on_budget h M K hh ζ hζ branches
    .right Ns hmargin.1 x y v hv
  have hl := A06.chiral_same_commutator_on_budget h M K hh ζ hζ branches
    .left Ns hmargin.2 x y v hv
  simp only [A06.orientationSign, Int.cast_one, Int.cast_neg, one_mul,
    neg_mul] at hr hl
  have hcross := A06.chiral_cross_commute h M ζ branches x y
  have hrev : A02.commutator (A06.chiralField h M ζ branches .left x)
      (A06.chiralField h M ζ branches .right y) = 0 := by
    have hc := A06.chiral_cross_commute h M ζ branches y x
    simp only [A02.commutator] at hc ⊢
    exact sub_eq_zero.mpr (sub_eq_zero.mp hc).symm
  have hbilinear (P Q R S : A05.Operators σ h) :
      A02.commutator (P + Q) (R - S) =
        A02.commutator P R - A02.commutator P S + A02.commutator Q R - A02.commutator Q S := by
    simp only [A02.commutator, add_mul, mul_add, sub_mul, mul_sub]
    abel
  unfold phiField thetaField
  rw [hbilinear]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, hcross, hrev,
    LinearMap.zero_apply, hr, hl]
  module


lemma mixed_forward_diff_on_budget (h M K : ℕ) (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (phiField h M ζ branches x)
      (A06.opForwardDiff h (thetaField h M ζ branches) y) v =
      (2 * A06.opForwardDiff h (A06.skewKernel h M ζ x) y) • v := by
  have h₁ := mixed_commutator_on_budget h M K hh hM hNoAlias ζ hζ
    branches Ns hmargin x (y + 1) v hv
  have h₂ := mixed_commutator_on_budget h M K hh hM hNoAlias ζ hζ
    branches Ns hmargin x y v hv
  have hsub (A B C : A05.Operators σ h) :
      A02.commutator A (B - C) = A02.commutator A B - A02.commutator A C := by
    simp only [A02.commutator, mul_sub, sub_mul]
    abel
  unfold A06.opForwardDiff
  rw [hsub, LinearMap.sub_apply, h₁, h₂]
  rw [← sub_smul]
  congr 1
  ring

theorem zero_mode_obstruction_on_ground (h M K : ℕ)
    [NeZero (2 * h)] (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x : ZMod (2 * h)) (c : ℂ) (hc : c ≠ 0) :
    ¬ (∀ y : ZMod (2 * h),
      A02.commutator (phiField h M ζ branches x)
        (A06.opForwardDiff h (thetaField h M ζ branches) y)
          (A05.groundKet h Ns) =
        (c * A06.dirichletKernel h M ζ x y) • A05.groundKet h Ns) := by
  classical
  have hground := A05.ground_mem_budget h hh Ns hN K
  have hregime : 1 ≤ M ∧ A06.branchMargins h M K Ns branches := ⟨hM, hmargin⟩
  clear hground hregime
  intro hclaim
  let P := phiField h M ζ branches x
  let T := thetaField h M ζ branches
  let g := A05.groundKet h Ns
  have hdiff (y : ZMod (2 * h)) :
      A02.commutator P (A06.opForwardDiff h T y) g =
        A06.opForwardDiff h (fun z => A02.commutator P (T z) g) y := by
    simp only [A06.opForwardDiff, A02.commutator, mul_sub, sub_mul,
      LinearMap.sub_apply]
    abel
  have hsum : (∑ y : ZMod (2 * h),
      A02.commutator P (A06.opForwardDiff h T y) g) = 0 := by
    simp only [hdiff]
    exact A06.forward_diff_sum_zero h _
  have hscalar : (∑ y : ZMod (2 * h),
      A02.commutator P (A06.opForwardDiff h T y) g) = c • g := by
    simp only [P, T, g, hclaim]
    rw [← Finset.sum_smul, ← Finset.mul_sum,
      A06.dirichlet_spatial_sum h M ζ hζ hNoAlias x, mul_one]
  have hz : c • g = 0 := hscalar.symm.trans hsum
  exact (smul_eq_zero.mp hz).elim hc (A05.ground_ne_zero h Ns)


end Bosonize.Ch15
