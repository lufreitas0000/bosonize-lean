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
      phiField h M ζ branches x := by sorry

lemma theta_adjoint (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ)
    (x : ZMod (2 * h)) :
    LinearMap.adjoint (thetaField h M ζ branches x) =
      thetaField h M ζ branches x := by sorry

lemma phi_self_commutator_on_budget (h M K : ℕ) (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (phiField h M ζ branches x)
      (phiField h M ζ branches y) v = 0 := by sorry

lemma theta_self_commutator_on_budget (h M K : ℕ) (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (thetaField h M ζ branches x)
      (thetaField h M ζ branches y) v = 0 := by sorry

lemma mixed_commutator_on_budget (h M K : ℕ) (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (phiField h M ζ branches x)
      (thetaField h M ζ branches y) v =
      (2 * A06.skewKernel h M ζ x y) • v := by sorry

lemma mixed_forward_diff_on_budget (h M K : ℕ) (hh : 0 < h)
    (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (phiField h M ζ branches x)
      (A06.opForwardDiff h (thetaField h M ζ branches) y) v =
      (2 * A06.opForwardDiff h (A06.skewKernel h M ζ x) y) • v := by sorry

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
        (c * A06.dirichletKernel h M ζ x y) • A05.groundKet h Ns) := by sorry

end Bosonize.Ch15
