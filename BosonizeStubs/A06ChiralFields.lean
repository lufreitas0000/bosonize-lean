import Bosonize

namespace Bosonize.A06

open scoped BigOperators

inductive Orientation where
  | right
  | left
  deriving DecidableEq

def orientationSign : Orientation → ℤ
  | .right => 1
  | .left => -1

structure Branches (σ : Type*) where
  rightSpecies : σ
  leftSpecies : σ
  distinct : rightSpecies ≠ leftSpecies

def speciesOf {σ : Type*} (branches : Branches σ) : Orientation → σ
  | .right => branches.rightSpecies
  | .left => branches.leftSpecies

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

def marginAt (h M K : ℕ) (Ns : σ → ℤ) (ν : σ) : Prop :=
  2 * (M : ℤ) + (K : ℤ) + |Ns ν| ≤ (h : ℤ)

def branchMargins (h M K : ℕ) (Ns : σ → ℤ)
    (branches : Branches σ) : Prop :=
  marginAt h M K Ns branches.rightSpecies ∧
    marginAt h M K Ns branches.leftSpecies

noncomputable def latticeCharacter (h : ℕ) (ζ : ℂ) (k : ℤ)
    (x : ZMod (2 * h)) : ℂ :=
  A01.integerCharacter ζ k (x.val : ℤ)

noncomputable def skewKernel (h M : ℕ) (ζ : ℂ)
    (x y : ZMod (2 * h)) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    (latticeCharacter h ζ (m : ℤ) (x - y) -
      latticeCharacter h ζ (-(m : ℤ)) (x - y)) / (m : ℂ)

noncomputable def dirichletKernel (h M : ℕ) (ζ : ℂ)
    (x y : ZMod (2 * h)) : ℂ :=
  ((2 * h : ℕ) : ℂ)⁻¹ *
    ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      latticeCharacter h ζ m (x - y)

def opForwardDiff (h : ℕ) {V : Type*} [AddGroup V]
    (f : ZMod (2 * h) → V) : ZMod (2 * h) → V :=
  fun x => f (x + 1) - f x

def integerLift (h : ℕ) {V : Type*}
    (f : ZMod (2 * h) → V) (x : ℤ) : V :=
  f (x : ZMod (2 * h))

noncomputable def chiralField (h M : ℕ) (ζ : ℂ)
    (branches : Branches σ) (η : Orientation)
    (x : ZMod (2 * h)) : A05.Operators σ h :=
  ∑ m ∈ Finset.Icc 1 M,
    (Complex.I / (m : ℂ)) •
      ((latticeCharacter h ζ (orientationSign η * (m : ℤ)) x •
          A05.rho h (speciesOf branches η) (-(m : ℤ))) -
        (latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) x •
          A05.rho h (speciesOf branches η) (m : ℤ)))

noncomputable def chiralDifferenceExpansion (h M : ℕ) (ζ : ℂ)
    (branches : Branches σ) (η : Orientation)
    (x : ZMod (2 * h)) : A05.Operators σ h :=
  ∑ m ∈ Finset.Icc 1 M,
    (Complex.I / (m : ℂ)) •
      (((A01.integerCharacter ζ (orientationSign η * (m : ℤ)) 1 - 1) *
          latticeCharacter h ζ (orientationSign η * (m : ℤ)) x) •
          A05.rho h (speciesOf branches η) (-(m : ℤ)) -
        ((A01.integerCharacter ζ (-(orientationSign η * (m : ℤ))) 1 - 1) *
          latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) x) •
          A05.rho h (speciesOf branches η) (m : ℤ))

lemma lattice_character_shift (h : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (k : ℤ) (x : ZMod (2 * h)) :
    latticeCharacter h ζ k (x + 1) =
      A01.integerCharacter ζ k 1 * latticeCharacter h ζ k x := by sorry

lemma lattice_character_conj (h : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (k : ℤ) (x : ZMod (2 * h)) :
    star (latticeCharacter h ζ k x) = latticeCharacter h ζ (-k) x := by sorry

lemma integer_lift_periodic (h : ℕ) {V : Type*}
    (f : ZMod (2 * h) → V) (x : ℤ) :
    integerLift h f (x + (2 * h : ℕ)) = integerLift h f x := by sorry

lemma forward_diff_add (h : ℕ) {V : Type*} [AddCommGroup V]
    (f g : ZMod (2 * h) → V) (x : ZMod (2 * h)) :
    opForwardDiff h (fun y => f y + g y) x =
      opForwardDiff h f x + opForwardDiff h g x := by sorry

lemma forward_diff_smul (h : ℕ) {V : Type*} [AddCommGroup V]
    [Module ℂ V] (a : ℂ) (f : ZMod (2 * h) → V)
    (x : ZMod (2 * h)) :
    opForwardDiff h (fun y => a • f y) x =
      a • opForwardDiff h f x := by sorry

lemma forward_diff_sum_zero (h : ℕ) [NeZero (2 * h)]
    {V : Type*} [AddCommGroup V] (f : ZMod (2 * h) → V) :
    (∑ x : ZMod (2 * h), opForwardDiff h f x) = 0 := by sorry

lemma chiral_adjoint (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : Branches σ)
    (η : Orientation) (x : ZMod (2 * h)) :
    LinearMap.adjoint (chiralField h M ζ branches η x) =
      chiralField h M ζ branches η x := by sorry

lemma chiral_forward_diff (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : Branches σ)
    (η : Orientation) (x : ZMod (2 * h)) :
    opForwardDiff h (chiralField h M ζ branches η) x =
      chiralDifferenceExpansion h M ζ branches η x := by sorry

lemma joint_signed_current_commutator (h K : ℕ) (hh : 0 < h)
    (Ns : σ → ℤ) (ν : σ) (m n : ℤ)
    (hmargin : |m| + |n| + (K : ℤ) + |Ns ν| ≤ (h : ℤ))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (A05.rho h ν m) (A05.rho h ν n) v =
      Ch10.schwingerCoefficient m n • v := by sorry

lemma chiral_cross_commute (h M : ℕ) (ζ : ℂ)
    (branches : Branches σ) (x y : ZMod (2 * h)) :
    A02.commutator
      (chiralField h M ζ branches .right x)
      (chiralField h M ζ branches .left y) = 0 := by sorry

lemma chiral_same_commutator_on_budget (h M K : ℕ) (hh : 0 < h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : Branches σ) (η : Orientation)
    (Ns : σ → ℤ)
    (hmargin : marginAt h M K Ns (speciesOf branches η))
    (x y : ZMod (2 * h))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator
      (chiralField h M ζ branches η x)
      (chiralField h M ζ branches η y) v =
      ((orientationSign η : ℂ) * skewKernel h M ζ x y) • v := by sorry

lemma dirichlet_diagonal (h M : ℕ) (hh : 0 < h) (ζ : ℂ) :
    dirichletKernel h M ζ (0 : ZMod (2 * h)) 0 =
      ((2 * M + 1 : ℕ) : ℂ) / ((2 * h : ℕ) : ℂ) := by sorry

lemma dirichlet_spatial_sum (h M : ℕ) [NeZero (2 * h)]
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (hNoAlias : 2 * M < 2 * h) (x : ZMod (2 * h)) :
    (∑ y : ZMod (2 * h), dirichletKernel h M ζ x y) = 1 := by sorry

lemma skew_kernel_diff_sum_zero (h M : ℕ) [NeZero (2 * h)]
    (ζ : ℂ) (x : ZMod (2 * h)) :
    (∑ y : ZMod (2 * h),
      opForwardDiff h (skewKernel h M ζ x) y) = 0 := by sorry

lemma admissible_ground_nonzero (h K : ℕ) (hh : 0 < h)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns) :
    ∃ v : A05.FockSpace σ h,
      v ∈ A05.jointBudget h Ns K ∧ v ≠ 0 := by sorry

lemma concrete_two_branch_parameters :
    ∃ (h M K : ℕ) (Ns : Fin 2 → ℤ) (branches : Branches (Fin 2)),
      0 < h ∧ 1 ≤ M ∧ 2 * M < 2 * h ∧
      A05.admissible h Ns ∧ branchMargins h M K Ns branches ∧
      A05.groundKet h Ns ∈ A05.jointBudget h Ns K ∧
      A05.groundKet h Ns ≠ 0 := by sorry

end Bosonize.A06
