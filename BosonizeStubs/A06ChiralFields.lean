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
      A01.integerCharacter ζ k 1 * latticeCharacter h ζ k x := by
  have repr (z : ZMod (2 * h)) :
      latticeCharacter h ζ k z =
        A01.residueCharacter (2 * h) ζ (k : ZMod (2 * h)) z := by
    have hr := A01.residue_character_int_cast (2 * h) ζ hζ k (z.val : ℤ)
    simpa [latticeCharacter] using hr.symm
  calc
    latticeCharacter h ζ k (x + 1) =
        A01.residueCharacter (2 * h) ζ (k : ZMod (2 * h)) (x + 1) :=
          repr (x + 1)
    _ = A01.residueCharacter (2 * h) ζ (k : ZMod (2 * h)) x *
          A01.residueCharacter (2 * h) ζ (k : ZMod (2 * h)) 1 :=
            A01.residue_character_add_right (2 * h) ζ hζ _ x 1
    _ = A01.integerCharacter ζ k 1 * latticeCharacter h ζ k x := by
      have hone :
          A01.residueCharacter (2 * h) ζ (k : ZMod (2 * h)) 1 =
            A01.integerCharacter ζ k 1 := by
        simpa only [Int.cast_one] using A01.residue_character_int_cast (2 * h) ζ hζ k 1
      rw [← repr x, hone]
      exact mul_comm _ _


lemma lattice_character_conj (h : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (k : ℤ) (x : ZMod (2 * h)) :
    star (latticeCharacter h ζ k x) = latticeCharacter h ζ (-k) x := by
  change star (A01.integerCharacter ζ k (x.val : ℤ)) =
    A01.integerCharacter ζ (-k) (x.val : ℤ)
  exact A01.complex_character_conj (2 * h) ζ hζ k (x.val : ℤ)

lemma integer_lift_periodic (h : ℕ) {V : Type*}
    (f : ZMod (2 * h) → V) (x : ℤ) :
    integerLift h f (x + (2 * h : ℕ)) = integerLift h f x := by
  change f (((x + (2 * h : ℕ) : ℤ) : ZMod (2 * h))) = f (x : ZMod (2 * h))
  simp only [Int.cast_add, Int.cast_natCast]
  simp

lemma forward_diff_add (h : ℕ) {V : Type*} [AddCommGroup V]
    (f g : ZMod (2 * h) → V) (x : ZMod (2 * h)) :
    opForwardDiff h (fun y => f y + g y) x =
      opForwardDiff h f x + opForwardDiff h g x := by
  simp only [opForwardDiff]
  abel

lemma forward_diff_smul (h : ℕ) {V : Type*} [AddCommGroup V]
    [Module ℂ V] (a : ℂ) (f : ZMod (2 * h) → V)
    (x : ZMod (2 * h)) :
    opForwardDiff h (fun y => a • f y) x =
      a • opForwardDiff h f x := by
  simp only [opForwardDiff]
  exact (smul_sub a (f (x + 1)) (f x)).symm

lemma forward_diff_sum_zero (h : ℕ) [NeZero (2 * h)]
    {V : Type*} [AddCommGroup V] (f : ZMod (2 * h) → V) :
    (∑ x : ZMod (2 * h), opForwardDiff h f x) = 0 := by
  classical
  have hshift : (∑ x : ZMod (2 * h), f (x + 1)) =
      ∑ x : ZMod (2 * h), f x := by
    apply Finset.sum_bij (fun x _ => x + 1)
    · intro x hx
      exact Finset.mem_univ _
    · intro x y hx hy heq
      exact add_right_cancel heq
    · intro y hy
      refine ⟨y - 1, Finset.mem_univ _, ?_⟩
      simp
    · intro x hx
      rfl
  simp only [opForwardDiff, Finset.sum_sub_distrib]
  rw [hshift]
  exact sub_self _

lemma chiral_adjoint (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : Branches σ)
    (η : Orientation) (x : ZMod (2 * h)) :
    LinearMap.adjoint (chiralField h M ζ branches η x) =
      chiralField h M ζ branches η x := by
  classical
  unfold chiralField
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hc (k : ℤ) :
      star (latticeCharacter h ζ k x) = latticeCharacter h ζ (-k) x :=
    lattice_character_conj h ζ hζ k x
  change (LinearMap.adjoint : A05.Operators σ h ≃ₗ⋆[ℂ] A05.Operators σ h)
    ((Complex.I / (m : ℂ)) •
      (latticeCharacter h ζ (orientationSign η * (m : ℤ)) x •
          A05.rho h (speciesOf branches η) (-(m : ℤ)) -
       latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) x •
          A05.rho h (speciesOf branches η) (m : ℤ))) = _
  simp only [map_smulₛₗ, map_sub, A05.rho_adjoint,
    starRingEnd_apply]
  rw [hc (orientationSign η * (m : ℤ)),
      hc (-(orientationSign η * (m : ℤ)))]
  simp only [neg_neg, star_div₀, Complex.star_def, Complex.conj_I, map_natCast,
    neg_div, smul_sub, smul_smul]
  module


lemma chiral_forward_diff (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : Branches σ)
    (η : Orientation) (x : ZMod (2 * h)) :
    opForwardDiff h (chiralField h M ζ branches η) x =
      chiralDifferenceExpansion h M ζ branches η x := by
  classical
  unfold opForwardDiff chiralField chiralDifferenceExpansion
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [lattice_character_shift h ζ hζ
       (orientationSign η * (m : ℤ)) x,
      lattice_character_shift h ζ hζ
       (-(orientationSign η * (m : ℤ))) x]
  simp only [smul_sub, smul_smul]
  module


lemma joint_signed_current_commutator (h K : ℕ) (hh : 0 < h)
    (Ns : σ → ℤ) (ν : σ) (m n : ℤ)
    (hmargin : |m| + |n| + (K : ℤ) + |Ns ν| ≤ (h : ℤ))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (A05.rho h ν m) (A05.rho h ν n) v =
      Ch10.schwingerCoefficient m n • v := by
  let : DecidableEq (A05.Mode σ h) := fun a b => A05.localModeDecidableEq h a b
  change v ∈ A03.coordinateSpace _ at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨S, hS, rfl⟩ := hw
      change (∀ η, Ch07.relativeCharge h
          (Ch07.speciesConfiguration h S η) = Ns η) ∧
        Ch07.totalExcitation h S ≤ (K : ℤ) at hS
      let Ss : σ → Ch07.Occupation h :=
        fun η => Ch07.speciesConfiguration h S η
      let vs : σ → Ch07.FockSpace h := fun η => A02.ket (Ss η)
      have hnonneg (η : σ) : 0 ≤ Ch07.excitationEnergy h (Ss η) :=
        Ch07.excitation_nonneg h hh (Ss η)
      have hcomponent : Ch07.excitationEnergy h (Ss ν) ≤ (K : ℤ) := by
        have hsingle : Ch07.excitationEnergy h (Ss ν) ≤
            ∑ η : σ, Ch07.excitationEnergy h (Ss η) := by
          exact Finset.single_le_sum (s := Finset.univ)
            (f := fun η : σ => Ch07.excitationEnergy h (Ss η))
            (fun η _ => hnonneg η) (Finset.mem_univ ν)
        unfold Ch07.totalExcitation at hS
        exact le_trans hsingle hS.2
      have hsingle : vs ν ∈ Ch07.fixedBudget h (Ns ν) (K : ℤ) := by
        apply (Ch07.ket_mem_fixed_budget h (Ss ν) (Ns ν) (K : ℤ)).mpr
        exact ⟨hS.1 ν, hcomponent⟩
      have hccr := Ch10.rho_signed_ccr h hh m n (Ns ν) (K : ℤ)
        (by simpa [add_assoc] using hmargin) (vs ν) hsingle
      have hfactor (u : Ch07.FockSpace h) (T : A05.Occupation σ h) :
          (∏ η, (Function.update vs ν u) η
              (Ch07.speciesConfiguration h T η)) =
            u (Ch07.speciesConfiguration h T ν) *
              ∏ η ∈ (Finset.univ : Finset σ).erase ν,
                vs η (Ch07.speciesConfiguration h T η) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ν)]
        simp only [Function.update_self]
        congr 1
        apply Finset.prod_congr rfl
        intro η hη
        rw [Function.update_of_ne (Finset.mem_erase.mp hη).1]
      let T : Ch07.FockSpace h →ₗ[ℂ] A05.FockSpace σ h := {
        toFun := fun u => A05.tensorVector h (Function.update vs ν u)
        map_add' := by
          intro u w
          apply (A02.coordinates (A05.Mode σ h)).injective
          funext S'
          simp only [map_add, A05.tensorVector, LinearEquiv.apply_symm_apply,
            Pi.add_apply]
          rw [hfactor, hfactor, hfactor]
          simp only [PiLp.add_apply]
          ring
        map_smul' := by
          intro a u
          apply (A02.coordinates (A05.Mode σ h)).injective
          funext S'
          simp only [map_smul, A05.tensorVector, LinearEquiv.apply_symm_apply,
            Pi.smul_apply, smul_eq_mul]
          rw [hfactor, hfactor]
          simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring }
      have hket : (A02.ket S : A05.FockSpace σ h) = T (vs ν) := by
        change A02.ket S = A05.tensorVector h (Function.update vs ν (vs ν))
        have hu : Function.update vs ν (vs ν) = vs := by
          funext η
          by_cases he : η = ν
          · subst η
            simp
          · simp [Function.update_of_ne he]
        rw [hu, A05.tensor_kets, A05.joint_species_configuration]
      have hrho (p : ℤ) (u : Ch07.FockSpace h) :
          A05.rho h ν p (T u) = T (Ch09.rho h p u) := by
        change A05.rho h ν p
            (A05.tensorVector h (Function.update vs ν u)) =
          A05.tensorVector h
            (Function.update vs ν (Ch09.rho h p u))
        rw [A05.rho_tensor]
        simp
      rw [hket]
      change (A05.rho h ν m * A05.rho h ν n -
        A05.rho h ν n * A05.rho h ν m) (T (vs ν)) =
          Ch10.schwingerCoefficient m n • T (vs ν)
      calc
        (A05.rho h ν m * A05.rho h ν n -
            A05.rho h ν n * A05.rho h ν m) (T (vs ν)) =
          T ((Ch09.rho h m * Ch09.rho h n -
            Ch09.rho h n * Ch09.rho h m) (vs ν)) := by
              simp only [LinearMap.sub_apply, Module.End.mul_apply, hrho,
                ← map_sub]
        _ = Ch10.schwingerCoefficient m n • T (vs ν) := by
          rw [← map_smul]
          exact congrArg T hccr
  | zero =>
      simp
  | add u w hu hw ih_u ih_w =>
      simpa only [map_add, smul_add] using congrArg₂ (· + ·) ih_u ih_w
  | smul a u hu ih =>
      rw [map_smul, ih, smul_comm]

lemma chiral_cross_commute (h M : ℕ) (ζ : ℂ)
    (branches : Branches σ) (x y : ZMod (2 * h)) :
    A02.commutator
      (chiralField h M ζ branches .right x)
      (chiralField h M ζ branches .left y) = 0 := by
  classical
  let F : ℕ → A05.Operators σ h := fun m =>
    (Complex.I / (m : ℂ)) •
      ((latticeCharacter h ζ (orientationSign .right * (m : ℤ)) x •
          A05.rho h branches.rightSpecies (-(m : ℤ))) -
       (latticeCharacter h ζ (-(orientationSign .right * (m : ℤ))) x •
          A05.rho h branches.rightSpecies (m : ℤ)))
  let G : ℕ → A05.Operators σ h := fun n =>
    (Complex.I / (n : ℂ)) •
      ((latticeCharacter h ζ (orientationSign .left * (n : ℤ)) y •
          A05.rho h branches.leftSpecies (-(n : ℤ))) -
       (latticeCharacter h ζ (-(orientationSign .left * (n : ℤ))) y •
          A05.rho h branches.leftSpecies (n : ℤ)))
  have hpair (m n : ℕ) : A02.commutator (F m) (G n) = 0 := by
    have h₁ := A05.rho_cross_commute h branches.rightSpecies
      branches.leftSpecies branches.distinct (-(m : ℤ)) (-(n : ℤ))
    have h₂ := A05.rho_cross_commute h branches.rightSpecies
      branches.leftSpecies branches.distinct (-(m : ℤ)) (n : ℤ)
    have h₃ := A05.rho_cross_commute h branches.rightSpecies
      branches.leftSpecies branches.distinct (m : ℤ) (-(n : ℤ))
    have h₄ := A05.rho_cross_commute h branches.rightSpecies
      branches.leftSpecies branches.distinct (m : ℤ) (n : ℤ)
    simp only [A02.commutator] at h₁ h₂ h₃ h₄ ⊢
    dsimp [F, G]
    simp only [smul_sub, sub_mul, mul_sub, smul_mul_assoc,
      mul_smul_comm, smul_mul_assoc]
    have c₁ := sub_eq_zero.mp h₁
    have c₂ := sub_eq_zero.mp h₂
    have c₃ := sub_eq_zero.mp h₃
    have c₄ := sub_eq_zero.mp h₄
    simp only [c₁, c₂, c₃, c₄]
    module
  change A02.commutator (∑ m ∈ Finset.Icc 1 M, F m)
    (∑ n ∈ Finset.Icc 1 M, G n) = 0
  have hsum (s t : Finset ℕ) :
      A02.commutator (∑ m ∈ s, F m) (∑ n ∈ t, G n) =
        ∑ m ∈ s, ∑ n ∈ t, A02.commutator (F m) (G n) := by
    simp only [A02.commutator, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  rw [hsum]
  simp only [hpair, Finset.sum_const_zero]

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
      ((orientationSign η : ℂ) * skewKernel h M ζ x y) • v := by
  classical
  have hcurrent (p q : ℤ) (hp : |p| ≤ (M : ℤ))
      (hq : |q| ≤ (M : ℤ)) :
      A02.commutator (A05.rho h (speciesOf branches η) p)
          (A05.rho h (speciesOf branches η) q) v =
        Ch10.schwingerCoefficient p q • v := by
    apply joint_signed_current_commutator h K hh Ns
      (speciesOf branches η) p q
    · unfold marginAt at hmargin
      omega
    · exact hv
  have hpositive (m : ℕ) (hm : m ∈ Finset.Icc 1 M) :
      0 < m ∧ (m : ℤ) ≤ (M : ℤ) := by
    simp only [Finset.mem_Icc] at hm
    omega
  let ν := speciesOf branches η
  let F : ZMod (2 * h) → ℕ → A05.Operators σ h := fun z m =>
    (Complex.I / (m : ℂ)) •
      (latticeCharacter h ζ (orientationSign η * (m : ℤ)) z •
        A05.rho h ν (-(m : ℤ)) -
       latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) z •
        A05.rho h ν (m : ℤ))
  have hpair (m n : ℕ) (hm : m ∈ Finset.Icc 1 M)
      (hn : n ∈ Finset.Icc 1 M) :
      A02.commutator (F x m) (F y n) v =
        (if m = n then
          (latticeCharacter h ζ (orientationSign η * (m : ℤ)) x *
              latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) y -
            latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) x *
              latticeCharacter h ζ (orientationSign η * (m : ℤ)) y) /
            (m : ℂ) else 0) • v := by
    obtain ⟨hmp, hmM⟩ := hpositive m hm
    obtain ⟨hnp, hnM⟩ := hpositive n hn
    have hmabs : |(m : ℤ)| = (m : ℤ) := abs_of_nonneg (by omega)
    have hnabs : |(n : ℤ)| = (n : ℤ) := abs_of_nonneg (by omega)
    have hmnegabs : |(-(m : ℤ))| = (m : ℤ) := by simp [hmabs]
    have hnnegabs : |(-(n : ℤ))| = (n : ℤ) := by simp [hnabs]
    have h₁ := hcurrent (-(m : ℤ)) (-(n : ℤ))
      (by rw [hmnegabs]; exact hmM) (by rw [hnnegabs]; exact hnM)
    have h₂ := hcurrent (-(m : ℤ)) (n : ℤ)
      (by rw [hmnegabs]; exact hmM) (by rw [hnabs]; exact hnM)
    have h₃ := hcurrent (m : ℤ) (-(n : ℤ))
      (by rw [hmabs]; exact hmM) (by rw [hnnegabs]; exact hnM)
    have h₄ := hcurrent (m : ℤ) (n : ℤ)
      (by rw [hmabs]; exact hmM) (by rw [hnabs]; exact hnM)
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmp)
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnp)
    have hbilinear (a b c d t u : ℂ) (P Q R S : A05.Operators σ h) :
        A02.commutator (t • (a • P - b • Q)) (u • (c • R - d • S)) =
          (t * u * (a * c)) • A02.commutator P R -
          (t * u * (a * d)) • A02.commutator P S -
          (t * u * (b * c)) • A02.commutator Q R +
          (t * u * (b * d)) • A02.commutator Q S := by
      simp only [A02.commutator, smul_sub, sub_mul, mul_sub,
        smul_mul_assoc, mul_smul_comm, smul_smul]
      module
    dsimp only [F]
    rw [hbilinear]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
    rw [h₁, h₂, h₃, h₄]
    by_cases he : m = n
    · subst n
      have hpp : (m : ℤ) + (m : ℤ) ≠ 0 := by omega
      have hmm : -(m : ℤ) + -(m : ℤ) ≠ 0 := by omega
      simp only [Ch10.schwingerCoefficient, hpp, hmm, neg_add_cancel,
        add_neg_cancel, ite_true, ite_false, zero_smul, neg_neg,
        Int.cast_neg, Int.cast_natCast, smul_smul]
      simp only [smul_zero, zero_sub, add_zero, ← neg_smul, ← sub_smul]
      congr 1
      field_simp
      simp only [Complex.I_sq]
      ring
    · have hsumneg : (-(m : ℤ)) + (n : ℤ) ≠ 0 := by omega
      have hsumpos : (m : ℤ) + (-(n : ℤ)) ≠ 0 := by omega
      have hsumpp : (m : ℤ) + (n : ℤ) ≠ 0 := by omega
      have hsummm : (-(m : ℤ)) + (-(n : ℤ)) ≠ 0 := by omega
      simp only [Ch10.schwingerCoefficient, hsumneg, hsumpos,
        hsumpp, hsummm, ite_false, zero_smul, smul_zero, he,
        sub_self, add_zero]
  have hdouble :
      A02.commutator (chiralField h M ζ branches η x)
          (chiralField h M ζ branches η y) v =
        ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
          A02.commutator (F x m) (F y n) v := by
    change A02.commutator (∑ m ∈ Finset.Icc 1 M, F x m)
      (∑ n ∈ Finset.Icc 1 M, F y n) v = _
    simp only [A02.commutator, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_sub_distrib, LinearMap.sub_apply, LinearMap.sum_apply]
    rw [Finset.sum_comm]
  rw [hdouble]
  have hsums :
      (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        A02.commutator (F x m) (F y n) v) =
      (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        (if m = n then
          (latticeCharacter h ζ (orientationSign η * (m : ℤ)) x *
              latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) y -
            latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) x *
              latticeCharacter h ζ (orientationSign η * (m : ℤ)) y) /
            (m : ℂ) else 0) • v) := by
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    exact hpair m n hm hn
  rw [hsums]
  have hcollapse (m : ℕ) (hm : m ∈ Finset.Icc 1 M) :
      (∑ n ∈ Finset.Icc 1 M,
        (if m = n then
          (latticeCharacter h ζ (orientationSign η * (m : ℤ)) x *
              latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) y -
            latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) x *
              latticeCharacter h ζ (orientationSign η * (m : ℤ)) y) /
            (m : ℂ) else 0) • v) =
      ((latticeCharacter h ζ (orientationSign η * (m : ℤ)) x *
              latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) y -
            latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) x *
              latticeCharacter h ζ (orientationSign η * (m : ℤ)) y) /
            (m : ℂ)) • v := by
    rw [Finset.sum_eq_single m]
    · simp only [ite_true]
    · intro n hn hne
      simp only [Ne.symm hne, ite_false, zero_smul]
    · intro hnot
      exact (hnot hm).elim
  rw [Finset.sum_congr rfl hcollapse, ← Finset.sum_smul]
  congr 1
  let : NeZero (2 * h) := ⟨by omega⟩
  have hbridge (k : ℤ) (z : ZMod (2 * h)) :
      latticeCharacter h ζ k z = A01.residueCharacter (2 * h) ζ (k : ZMod (2 * h)) z := by
    have hc : ((z.val : ℤ) : ZMod (2 * h)) = z := by simp
    simpa only [hc, latticeCharacter] using
      (A01.residue_character_int_cast (2 * h) ζ hζ k (z.val : ℤ)).symm
  have hprod (k : ℤ) :
      latticeCharacter h ζ k x * latticeCharacter h ζ (-k) y =
      latticeCharacter h ζ k (x - y) := by
    have hc (z : ZMod (2 * h)) : ((z.val : ℤ) : ZMod (2 * h)) = z := by simp
    have hd : latticeCharacter h ζ k (x - y) =
        A01.integerCharacter ζ k ((x.val : ℤ) - (y.val : ℤ)) := by
      rw [hbridge]
      simpa only [Int.cast_sub, hc] using
        A01.residue_character_int_cast (2 * h) ζ hζ k ((x.val : ℤ) - (y.val : ℤ))
    rw [hd]
    simp only [latticeCharacter, A01.integerCharacter, mul_sub, neg_mul,
      zpow_sub₀ (A01.root_ne_zero (2 * h) ζ hζ), zpow_neg, div_eq_mul_inv]
  unfold skewKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hprod, show -(orientationSign η * (m : ℤ)) = - (orientationSign η * (m : ℤ)) from rfl]
  rw [show latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) x *
    latticeCharacter h ζ (orientationSign η * (m : ℤ)) y =
    latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) (x - y) by
      simpa only [neg_neg] using hprod (-(orientationSign η * (m : ℤ)))]
  cases η with
  | right => simp [orientationSign]
  | left =>
      simp [orientationSign]
      ring

lemma dirichlet_diagonal (h M : ℕ) (hh : 0 < h) (ζ : ℂ) :
    dirichletKernel h M ζ (0 : ZMod (2 * h)) 0 =
      ((2 * M + 1 : ℕ) : ℂ) / ((2 * h : ℕ) : ℂ) := by
  have hpos : 0 < 2 * h := by omega
  have hval (m : ℤ) : latticeCharacter h ζ m (0 : ZMod (2 * h)) = 1 := by
    simp [latticeCharacter, A01.integerCharacter]
  simp only [dirichletKernel, sub_self, hval]
  have hc : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
    simp [Int.card_Icc]
    omega
  rw [Finset.sum_const, hc]
  simp only [nsmul_eq_mul]
  push_cast
  have hden : ((2 * h : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

lemma dirichlet_spatial_sum (h M : ℕ) [NeZero (2 * h)]
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (hNoAlias : 2 * M < 2 * h) (x : ZMod (2 * h)) :
    (∑ y : ZMod (2 * h), dirichletKernel h M ζ x y) = 1 := by
  classical
  have hpos : 0 < 2 * h := Nat.pos_of_ne_zero (NeZero.ne (2 * h))
  have hrepr (m : ℤ) (z : ZMod (2 * h)) :
      latticeCharacter h ζ m z =
        A01.residueCharacter (2 * h) ζ (m : ZMod (2 * h)) z := by
    have hc := A01.residue_character_int_cast (2 * h) ζ hζ m (z.val : ℤ)
    simpa [latticeCharacter] using hc.symm
  have hsum (m : ℤ) :
      (∑ y : ZMod (2 * h), latticeCharacter h ζ m (x - y)) =
        if (m : ZMod (2 * h)) = 0 then ((2 * h : ℕ) : ℂ) else 0 := by
    simp_rw [hrepr]
    have hb := A01.character_sum (2 * h) ζ hζ (m : ZMod (2 * h))
    rw [← hb]
    apply Fintype.sum_equiv (Equiv.subLeft x)
    intro y
    rfl
  have hcast (m : ℤ) (hm : m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ)) :
      ((m : ZMod (2 * h)) = 0) ↔ m = 0 := by
    constructor
    · intro hz
      have hd : ((2 * h : ℕ) : ℤ) ∣ m :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd m (2 * h)).mp hz
      have hmrange := Finset.mem_Icc.mp hm
      have hmle : |m| ≤ (M : ℤ) := abs_le.mpr ⟨hmrange.1, hmrange.2⟩
      have hnat : m.natAbs < 2 * h := by
        have hbound : |m| < ((2 * h : ℕ) : ℤ) := by omega
        exact_mod_cast (show (m.natAbs : ℤ) < ((2 * h : ℕ) : ℤ) by
          simpa only [Int.natCast_natAbs] using hbound)
      have hmabs : m.natAbs < (((2 * h : ℕ) : ℤ)).natAbs := by
        simpa only [Int.natAbs_natCast] using hnat
      exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hmabs
    · intro hm0
      simp [hm0]
  unfold dirichletKernel
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hsum]
  have hzero : (0 : ℤ) ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) := by simp
  have hone :
      (∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        if (m : ZMod (2 * h)) = 0 then ((2 * h : ℕ) : ℂ) else 0) =
          ((2 * h : ℕ) : ℂ) := by
    calc
      _ = ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            if m = 0 then ((2 * h : ℕ) : ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro m hm
            by_cases hz : m = 0
            · subst m
              simp
            · have hnot : (m : ZMod (2 * h)) ≠ 0 :=
                fun he => hz ((hcast m hm).mp he)
              simp [hz, hnot]
      _ = ((2 * h : ℕ) : ℂ) := by simp [hzero]
  rw [hone]
  have hc : (((2 * h : ℕ) : ℂ) ≠ 0) := by exact_mod_cast hpos.ne'
  field_simp


lemma skew_kernel_diff_sum_zero (h M : ℕ) [NeZero (2 * h)]
    (ζ : ℂ) (x : ZMod (2 * h)) :
    (∑ y : ZMod (2 * h),
      opForwardDiff h (skewKernel h M ζ x) y) = 0 := by
  exact forward_diff_sum_zero h (skewKernel h M ζ x)

lemma admissible_ground_nonzero (h K : ℕ) (hh : 0 < h)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns) :
    ∃ v : A05.FockSpace σ h,
      v ∈ A05.jointBudget h Ns K ∧ v ≠ 0 := by
  exact ⟨A05.groundKet h Ns, A05.ground_mem_budget h hh Ns hN K,
    A05.ground_ne_zero h Ns⟩

lemma concrete_two_branch_parameters :
    ∃ (h M K : ℕ) (Ns : Fin 2 → ℤ) (branches : Branches (Fin 2)),
      0 < h ∧ 1 ≤ M ∧ 2 * M < 2 * h ∧
      A05.admissible h Ns ∧ branchMargins h M K Ns branches ∧
      A05.groundKet h Ns ∈ A05.jointBudget h Ns K ∧
      A05.groundKet h Ns ≠ 0 := by
  let Ns : Fin 2 → ℤ := fun _ => 0
  let branches : Branches (Fin 2) :=
    { rightSpecies := 0
      leftSpecies := 1
      distinct := by decide }
  have hN : A05.admissible 4 Ns := by
    intro ν
    simp [Ns, Ch07.admissible]
  have hmargin : branchMargins 4 1 0 Ns branches := by
    norm_num [branchMargins, marginAt, Ns, branches]
  refine ⟨4, 1, 0, Ns, branches, by omega, by omega,
    by omega, hN, hmargin, ?_, ?_⟩
  · exact A05.ground_mem_budget 4 (by omega) Ns hN 0
  · exact A05.ground_ne_zero 4 Ns

end Bosonize.A06
