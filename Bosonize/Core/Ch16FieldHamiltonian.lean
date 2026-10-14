import Bosonize.Core.A06ChiralFields
import Bosonize.Core.Ch15DualFields
import Bosonize.Core.Ch01LatticeBand
import Bosonize.Core.Ch02UmbralCalculus
import Bosonize.Core.A01FourierCharacters
import Bosonize.Core.Ch03Fourier
import Bosonize.Core.A02CARHilbert
import Bosonize.Core.Ch04CARFock
import Bosonize.Core.Ch05Fermions
import Bosonize.Core.Ch06LocalNet
import Bosonize.Core.Ch06Ext
import Bosonize.Core.A03EnergyBudgets
import Bosonize.Core.Ch07VacuumBudget
import Bosonize.Core.Ch08Boson
import Bosonize.Core.A05MultiSpecies
import Bosonize.Core.Ch13KleinFactors
import Bosonize.Core.A05FiniteExponentials
import Bosonize.Core.Ch14Mandelstam
import Bosonize.Core.A04DensityKinematics
import Bosonize.Core.Ch09DensityModes
import Bosonize.Core.A04CurrentMargins
import Bosonize.Core.Ch10Heisenberg
import Bosonize.Core.A04PartitionCombinatorics
import Bosonize.Core.Ch11HaldaneCompleteness
import Bosonize.Core.Ch12Sugawara
import Bosonize.Core.A07FiniteNormalOrdering

namespace Bosonize.Ch16

open scoped BigOperators

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

-- A sufficient right-suffix margin for an additional excursion.
def marginWithExcursion (h M K excursion : ℕ) (Ns : σ → ℤ)
    (branches : A06.Branches σ) : Prop :=
  ∀ η : A06.Orientation,
    2 * (M : ℤ) + (K : ℤ) + (excursion : ℤ) +
      |Ns (A06.speciesOf branches η)| ≤ (h : ℤ)

noncomputable def chiralSquare (h M : ℕ) (ζ : ℂ)
    (branches : A06.Branches σ) (η : A06.Orientation)
    (x : ZMod (2 * h)) : A05.Operators σ h :=
  A07.normalEvaluation h M branches
    (A07.squareSymbol (A07.chiralCoefficient h M ζ η x))

noncomputable def localFieldEnergy (h M : ℕ) (ζ : ℂ)
    (branches : A06.Branches σ)
    (x : ZMod (2 * h)) : A05.Operators σ h :=
  A07.normalEvaluation h M branches (A07.dualSquareSymbol h M ζ x)

noncomputable def fieldHamiltonian (h M : ℕ) [NeZero (2 * h)]
    (ζ : ℂ) (branches : A06.Branches σ) : A05.Operators σ h :=
  ∑ x : ZMod (2 * h), localFieldEnergy h M ζ branches x

noncomputable def epsilon (h : ℕ) (ζ : ℂ) (m : ℕ) : ℂ :=
  (((2 * h : ℕ) : ℂ) / (m : ℂ) ^ 2) *
    (A01.integerCharacter ζ (m : ℤ) 1 - 1) *
      (A01.integerCharacter ζ (-(m : ℤ)) 1 - 1)

noncomputable def referenceWeight (h : ℕ) (ζ : ℂ) : ℂ :=
  epsilon h ζ 1

noncomputable def sugawara (h M : ℕ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (∑ m ∈ Finset.Icc 1 M,
    A05.rho h (A06.speciesOf branches .right) (m : ℤ) *
      A05.rho h (A06.speciesOf branches .right) (-(m : ℤ))) +
  (∑ m ∈ Finset.Icc 1 M,
    A05.rho h (A06.speciesOf branches .left) (m : ℤ) *
      A05.rho h (A06.speciesOf branches .left) (-(m : ℤ)))

noncomputable def weightedEnergy (h M : ℕ) (ζ : ℂ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (∑ m ∈ Finset.Icc 1 M,
    epsilon h ζ m •
      (A05.rho h (A06.speciesOf branches .right) (m : ℤ) *
        A05.rho h (A06.speciesOf branches .right) (-(m : ℤ)))) +
  (∑ m ∈ Finset.Icc 1 M,
    epsilon h ζ m •
      (A05.rho h (A06.speciesOf branches .left) (m : ℤ) *
        A05.rho h (A06.speciesOf branches .left) (-(m : ℤ))))

noncomputable def weightedError (h M : ℕ) (ζ : ℂ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (∑ m ∈ Finset.Icc 1 M,
    (epsilon h ζ m - referenceWeight h ζ) •
      (A05.rho h (A06.speciesOf branches .right) (m : ℤ) *
        A05.rho h (A06.speciesOf branches .right) (-(m : ℤ)))) +
  (∑ m ∈ Finset.Icc 1 M,
    (epsilon h ζ m - referenceWeight h ζ) •
      (A05.rho h (A06.speciesOf branches .left) (m : ℤ) *
        A05.rho h (A06.speciesOf branches .left) (-(m : ℤ))))

noncomputable def errorOperator (h M : ℕ) [NeZero (2 * h)]
    (ζ : ℂ) (branches : A06.Branches σ) : A05.Operators σ h :=
  fieldHamiltonian h M ζ branches -
    ((4 : ℂ) * referenceWeight h ζ) • sugawara h M branches

noncomputable def excitedKet (h : ℕ) (Ns : σ → ℤ)
    (branches : A06.Branches σ) (η : A06.Orientation)
    (m : ℕ) : A05.FockSpace σ h :=
  A05.rho h (A06.speciesOf branches η) (m : ℤ) (A05.groundKet h Ns)

def standardBranches : A06.Branches (Fin 2) :=
  ⟨0, 1, by decide⟩

lemma field_chiral_identity (h M : ℕ) (ζ : ℂ)
    (branches : A06.Branches σ) (x : ZMod (2 * h)) :
    localFieldEnergy h M ζ branches x =
      (2 : ℂ) • (chiralSquare h M ζ branches .right x +
        chiralSquare h M ζ branches .left x) := by
  unfold localFieldEnergy chiralSquare
  rw [A07.dual_square_chiral_decomposition]
  rw [A07.normal_evaluation_smul, A07.normal_evaluation_add]

lemma chiral_spatial_collapse_on_budget (h M K : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (η : A06.Orientation)
    (Ns : σ → ℤ)
    (hmargin : A06.marginAt h M K Ns (A06.speciesOf branches η))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    (∑ x : ZMod (2 * h), chiralSquare h M ζ branches η x) v =
      ((2 : ℂ) •
        (∑ m ∈ Finset.Icc 1 M,
          epsilon h ζ m •
            (A05.rho h (A06.speciesOf branches η) (m : ℤ) *
              A05.rho h (A06.speciesOf branches η) (-(m : ℤ))))) v := by
  classical
  have _ := hh
  have _ := hM
  have _ := hmargin
  have _ := hv
  have horth (k : ℤ) (hk : |k| ≤ 2 * (M : ℤ)) :
      (∑ x : ZMod (2 * h), A06.latticeCharacter h ζ k x) =
        if k = 0 then ((2 * h : ℕ) : ℂ) else 0 := by
    have hb (x : ZMod (2 * h)) : A06.latticeCharacter h ζ k x =
        A01.residueCharacter (2 * h) ζ (k : ZMod (2 * h)) x := by
      simpa [A06.latticeCharacter] using
        (A01.residue_character_int_cast (2 * h) ζ hζ k (x.val : ℤ)).symm
    simp_rw [hb]
    rw [A01.character_sum (2 * h) ζ hζ]
    have hz : ((k : ZMod (2 * h)) = 0) ↔ k = 0 := by
      constructor
      · intro he
        have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd k (2 * h)).mp he
        have ha : k.natAbs < 2 * h := by
          have ht : (k.natAbs : ℤ) < ((2 * h : ℕ) : ℤ) := by
            rw [Int.natCast_natAbs]
            omega
          exact_mod_cast ht
        exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
          (by simpa only [Int.natAbs_natCast] using ha)
      · intro he
        simp [he]
    simp only [hz]
  have hmul (k l : ℤ) (x : ZMod (2 * h)) :
      A06.latticeCharacter h ζ k x * A06.latticeCharacter h ζ l x =
        A06.latticeCharacter h ζ (k + l) x := by
    simp only [A06.latticeCharacter, A01.integerCharacter, add_mul,
      zpow_add₀ (A01.root_ne_zero (2 * h) ζ hζ)]
  have hcoef (p q : A07.Letter M) :
      (∑ x : ZMod (2 * h),
        A07.chiralCoefficient h M ζ η x p * A07.chiralCoefficient h M ζ η x q) =
      if A07.orientation p.1 = η ∧ A07.orientation q.1 = η ∧
          p.2.1 = q.2.1 ∧ p.2.2 ≠ q.2.2 then epsilon h ζ (A07.natMode p) else 0 := by
    by_cases hp : A07.orientation p.1 = η
    · by_cases hq : A07.orientation q.1 = η
      · simp only [A07.chiralCoefficient, hp, hq, ite_true, true_and]
        let k : ℤ := A07.phaseSign p * A06.orientationSign η * (A07.natMode p : ℤ)
        let l : ℤ := A07.phaseSign q * A06.orientationSign η * (A07.natMode q : ℤ)
        let a : ℂ := ((A07.phaseSign p : ℂ) * Complex.I / (A07.natMode p : ℂ)) *
          (A01.integerCharacter ζ k 1 - 1)
        let b : ℂ := ((A07.phaseSign q : ℂ) * Complex.I / (A07.natMode q : ℂ)) *
          (A01.integerCharacter ζ l 1 - 1)
        have hex (x : ZMod (2 * h)) :
            A07.gradientCoefficient h M ζ x p * A07.gradientCoefficient h M ζ x q =
              (a * b) * A06.latticeCharacter h ζ (k + l) x := by
          dsimp [A07.gradientCoefficient, a, b, k, l]
          rw [hp, hq]
          rw [← hmul]
          ring
        simp_rw [hex]
        rw [← Finset.mul_sum]
        have hm : 0 < A07.natMode p ∧ A07.natMode p ≤ M := by unfold A07.natMode; omega
        have hn : 0 < A07.natMode q ∧ A07.natMode q ≤ M := by unfold A07.natMode; omega
        have hkl : |k + l| ≤ 2 * (M : ℤ) := by
          dsimp [k, l]
          cases η <;> cases hc : p.2.2 <;> cases hd : q.2.2 <;>
            simp only [A07.phaseSign, hc, hd, A06.orientationSign, Bool.false_eq_true, ite_true, ite_false, one_mul, neg_mul] <;>
              apply abs_le.mpr <;> constructor <;> omega
        rw [horth (k + l) hkl]
        have hz : k + l = 0 ↔ p.2.1 = q.2.1 ∧ p.2.2 ≠ q.2.2 := by
          dsimp [k, l]
          cases η <;> cases hc : p.2.2 <;> cases hd : q.2.2 <;>
            simp [A07.phaseSign, hc, hd, A06.orientationSign, A07.natMode, Fin.ext_iff] <;> omega
        simp only [hz]
        by_cases hd : p.2.1 = q.2.1 ∧ p.2.2 ≠ q.2.2
        · simp only [ite_eq_left hd]
          have he : A07.natMode p = A07.natMode q := by unfold A07.natMode; rw [hd.1]
          have hm0 : (A07.natMode p : ℂ) ≠ 0 := by exact_mod_cast hm.1.ne'
          dsimp [a, b, k, l]
          rw [← he]
          cases η <;> cases hc : p.2.2 <;> cases hcq : q.2.2 <;>
            simp only [A07.phaseSign, hc, hcq, Bool.false_eq_true, ite_false, ite_true,
              A06.orientationSign, Int.cast_one, Int.cast_neg, one_mul, neg_mul, neg_neg] at hd ⊢
          all_goals try { exact (hd.2 rfl).elim }
          all_goals
            unfold epsilon
            field_simp [hm0]
            simp only [Complex.I_sq]
            ring
        · simp only [ite_eq_right hd, mul_zero]
      · simp [A07.chiralCoefficient, hq]
    · simp [A07.chiralCoefficient, hp]
  have hop : (∑ x : ZMod (2 * h), chiralSquare h M ζ branches η x) =
      (2 : ℂ) • (∑ m ∈ Finset.Icc 1 M,
        epsilon h ζ m • (A05.rho h (A06.speciesOf branches η) (m : ℤ) *
          A05.rho h (A06.speciesOf branches η) (-(m : ℤ)))) := by
    unfold chiralSquare A07.normalEvaluation A07.squareSymbol
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    simp_rw [hcoef]
    have hreindex (f : ℕ → A05.Operators σ h) :
        (∑ i : Fin M, f (i.val + 1)) = ∑ m ∈ Finset.Icc 1 M, f m := by
      apply Finset.sum_bij (fun i _ => i.val + 1)
      · intro i hi
        simp only [Finset.mem_Icc]
        omega
      · intro i hi j hj he
        apply Fin.ext
        omega
      · intro m hm
        simp only [Finset.mem_Icc] at hm
        refine ⟨⟨m - 1, by omega⟩, Finset.mem_univ _, ?_⟩
        dsimp
        omega
      · intro i hi
        rfl
    have hsum (η : A06.Orientation) :
        (∑ i : Fin M, epsilon h ζ (i.val + 1) •
          (A05.rho h (A06.speciesOf branches η) ((i.val : ℤ) + 1) *
            A05.rho h (A06.speciesOf branches η) (-1 + -(i.val : ℤ)))) =
        ∑ m ∈ Finset.Icc 1 M, epsilon h ζ m •
          (A05.rho h (A06.speciesOf branches η) (m : ℤ) *
            A05.rho h (A06.speciesOf branches η) (-(m : ℤ))) := by
      simpa only [Nat.cast_add, Nat.cast_one, neg_add_rev] using
        hreindex (fun m => epsilon h ζ m •
          (A05.rho h (A06.speciesOf branches η) (m : ℤ) *
            A05.rho h (A06.speciesOf branches η) (-(m : ℤ))))
    unfold A07.Letter
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    cases η <;>
      simp [A07.orientation, A07.normalPair, A07.rawPair,
        A07.current, A07.signedMode, A07.natMode, Finset.sum_add_distrib,
        ite_smul, Finset.sum_ite_eq]
    all_goals
      rw [hsum]
      module
  exact congrArg (fun T : A05.Operators σ h => T v) hop

theorem field_weighted_on_budget (h M K : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    fieldHamiltonian h M ζ branches v =
      ((4 : ℂ) • weightedEnergy h M ζ branches) v := by
  have hr := chiral_spatial_collapse_on_budget h M K hh hM hNoAlias ζ hζ
    branches .right Ns hmargin.1 v hv
  have hl := chiral_spatial_collapse_on_budget h M K hh hM hNoAlias ζ hζ
    branches .left Ns hmargin.2 v hv
  unfold fieldHamiltonian
  simp_rw [field_chiral_identity]
  rw [← Finset.smul_sum, Finset.sum_add_distrib]
  simp only [LinearMap.smul_apply, LinearMap.add_apply] at hr hl ⊢
  rw [hr, hl]
  simp only [weightedEnergy, LinearMap.add_apply]
  module

theorem field_weighted_after_excursion (h M K excursion : ℕ)
    [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M)
    (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : marginWithExcursion h M K excursion Ns branches)
    (v : A05.FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns (K + excursion)) :
    fieldHamiltonian h M ζ branches v =
      ((4 : ℂ) • weightedEnergy h M ζ branches) v := by
  have hr := hmargin .right
  have hl := hmargin .left
  apply field_weighted_on_budget h M (K + excursion) hh hM hNoAlias ζ hζ
    branches Ns _ v hv
  constructor
  · simpa only [A06.marginAt, A06.speciesOf, Nat.cast_add, add_assoc] using hr
  · simpa only [A06.marginAt, A06.speciesOf, Nat.cast_add, add_assoc] using hl

lemma error_weighted_on_budget (h M K : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    errorOperator h M ζ branches v =
      ((4 : ℂ) • weightedError h M ζ branches) v := by
  have hfield := field_weighted_on_budget h M K hh hM hNoAlias ζ hζ
    branches Ns hmargin v hv
  have hweight : weightedError h M ζ branches = weightedEnergy h M ζ branches -
      referenceWeight h ζ • sugawara h M branches := by
    simp only [weightedError, weightedEnergy, sugawara, smul_add,
      Finset.smul_sum, sub_smul, Finset.sum_sub_distrib]
    abel
  unfold errorOperator
  rw [LinearMap.sub_apply, hfield, hweight]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply]
  module

lemma ground_error_zero (h M K : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hmargin : A06.branchMargins h M K Ns branches) :
    errorOperator h M ζ branches (A05.groundKet h Ns) = 0 := by
  rw [error_weighted_on_budget h M K hh hM hNoAlias ζ hζ branches Ns hmargin
    (A05.groundKet h Ns) (A05.ground_mem_budget h hh Ns hN K)]
  simp only [LinearMap.smul_apply]
  have hkill (ν : σ) (m : ℕ) (hm : m ∈ Finset.Icc 1 M) :
      A05.rho h ν (-(m : ℤ)) (A05.groundKet h Ns) = 0 := by
    apply A05.rho_lowering_budget_zero h hh ν m 0
    · have hp := (Finset.mem_Icc.mp hm).1
      omega
    · exact A05.ground_mem_budget h hh Ns hN 0
  have hs (ν : σ) :
      (∑ m ∈ Finset.Icc 1 M, (epsilon h ζ m - referenceWeight h ζ) •
        (A05.rho h ν (m : ℤ) * A05.rho h ν (-(m : ℤ))))
        (A05.groundKet h Ns) = 0 := by
    rw [LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro m hm
    simp only [LinearMap.smul_apply, Module.End.mul_apply]
    rw [hkill ν m hm, map_zero, smul_zero]
  unfold weightedError
  rw [LinearMap.add_apply, hs, hs, add_zero, smul_zero]

lemma excited_ket_mem_budget (h K m : ℕ) (hh : 0 < h)
    (hm : m ≤ K) (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (branches : A06.Branches σ) (η : A06.Orientation) :
    excitedKet h Ns branches η m ∈ A05.jointBudget h Ns K := by
  have hg := A05.ground_mem_budget h hh Ns hN 0
  have hr := A05.rho_budget_map h (A06.speciesOf branches η) (m : ℤ) Ns 0
    (A05.groundKet h Ns) hg
  have hmono : Ch07.speciesBudget h Ns (m : ℤ) ≤ Ch07.speciesBudget h Ns (K : ℤ) := by
    apply A03.coordinate_space_mono
    intro S hS
    exact ⟨hS.1, le_trans hS.2 (by exact_mod_cast hm)⟩
  apply hmono
  simpa only [Nat.cast_zero, zero_add, excitedKet] using hr

lemma excited_ket_nonzero (h M m : ℕ) (hh : 0 < h)
    (hm : 1 ≤ m) (hcut : m ≤ M)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (branches : A06.Branches σ) (η : A06.Orientation)
    (hmargin : A06.marginAt h M m Ns (A06.speciesOf branches η)) :
    excitedKet h Ns branches η m ≠ 0 := by
  intro hz
  have hg := A05.ground_mem_budget h hh Ns hN 0
  have hl := A05.rho_lowering_budget_zero h hh (A06.speciesOf branches η)
    m 0 (by omega) Ns (A05.groundKet h Ns) hg
  have hc := A06.joint_signed_current_commutator h 0 hh Ns
    (A06.speciesOf branches η) (-(m : ℤ)) (m : ℤ) (by
      unfold A06.marginAt at hmargin
      simp only [abs_neg, abs_of_nonneg (Int.natCast_nonneg m), Nat.cast_zero]
      omega) (A05.groundKet h Ns) hg
  simp only [A02.commutator, LinearMap.sub_apply, Module.End.mul_apply,
    Ch10.schwingerCoefficient, neg_add_cancel, ite_true, Int.cast_neg, neg_neg] at hc
  change A05.rho h (A06.speciesOf branches η) (m : ℤ) (A05.groundKet h Ns) = 0 at hz
  rw [hz, hl, map_zero, map_zero, sub_self] at hc
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  exact (smul_eq_zero.mp hc.symm).elim hm0 (A05.ground_ne_zero h Ns)

theorem single_mode_error_eigenvector (h M K m : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (hm : 1 ≤ m) (hcut : m ≤ M) (hK : m ≤ K)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (η : A06.Orientation)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (hmargin : A06.branchMargins h M K Ns branches) :
    errorOperator h M ζ branches (excitedKet h Ns branches η m) =
      ((4 : ℂ) * (m : ℂ) * (epsilon h ζ m - referenceWeight h ζ)) •
        excitedKet h Ns branches η m := by
  classical
  have hg := A05.ground_mem_budget h hh Ns hN 0
  have hexc := excited_ket_mem_budget h K m hh hK Ns hN branches η
  have hselected : A06.marginAt h M K Ns (A06.speciesOf branches η) := by
    cases η
    · exact hmargin.1
    · exact hmargin.2
  let g := A05.groundKet h Ns
  let w := excitedKet h Ns branches η m
  have hl (θ : A06.Orientation) (n : ℕ) (hn : 1 ≤ n) :
      A05.rho h (A06.speciesOf branches θ) (-(n : ℤ)) g = 0 :=
    A05.rho_lowering_budget_zero h hh (A06.speciesOf branches θ)
      n 0 (by omega) Ns g hg
  have hpair (θ : A06.Orientation) (n : ℕ) (hn : n ∈ Finset.Icc 1 M) :
      (A05.rho h (A06.speciesOf branches θ) (n : ℤ) *
        A05.rho h (A06.speciesOf branches θ) (-(n : ℤ))) w =
      if θ = η ∧ n = m then (m : ℂ) • w else 0 := by
    obtain ⟨hnpos, hncut⟩ := Finset.mem_Icc.mp hn
    by_cases hθη : θ = η
    · subst θ
      have hc := A06.joint_signed_current_commutator h 0 hh Ns
        (A06.speciesOf branches η) (-(n : ℤ)) (m : ℤ) (by
          unfold A06.marginAt at hselected
          simp only [abs_neg, abs_of_nonneg (Int.natCast_nonneg n),
            abs_of_nonneg (Int.natCast_nonneg m), Nat.cast_zero]
          omega) g hg
      have hcoeff : Ch10.schwingerCoefficient (-(n : ℤ)) (m : ℤ) =
          if n = m then (m : ℂ) else 0 := by
        by_cases he : n = m
        · subst n
          simp [Ch10.schwingerCoefficient]
        · have hnz : -(n : ℤ) + (m : ℤ) ≠ 0 := by omega
          simp only [Ch10.schwingerCoefficient, hnz, ite_false, he]
      rw [hcoeff] at hc
      simp only [A02.commutator, LinearMap.sub_apply, Module.End.mul_apply,
        hl η n hnpos, map_zero, sub_zero] at hc
      change A05.rho h (A06.speciesOf branches η) (n : ℤ)
        (A05.rho h (A06.speciesOf branches η) (-(n : ℤ))
          (A05.rho h (A06.speciesOf branches η) (m : ℤ) g)) = _
      rw [hc]
      by_cases he : n = m
      · subst n
        simp only [ite_true, map_smul, true_and]
        rfl
      · simp only [he, ite_false, zero_smul, map_zero, true_and]
    · have hspecies : A06.speciesOf branches θ ≠ A06.speciesOf branches η := by
        cases θ <;> cases η
        · exact False.elim (hθη rfl)
        · exact branches.distinct
        · exact branches.distinct.symm
        · exact False.elim (hθη rfl)
      have hc := congrArg (fun A : A05.Operators σ h => A g)
        (A05.rho_cross_commute h (A06.speciesOf branches θ)
          (A06.speciesOf branches η) hspecies (-(n : ℤ)) (m : ℤ))
      simp only [A02.commutator, LinearMap.sub_apply, Module.End.mul_apply,
        hl θ n hnpos, map_zero, LinearMap.zero_apply, sub_zero] at hc
      change A05.rho h (A06.speciesOf branches θ) (n : ℤ)
        (A05.rho h (A06.speciesOf branches θ) (-(n : ℤ))
          (A05.rho h (A06.speciesOf branches η) (m : ℤ) g)) = _
      rw [hc, map_zero]
      simp only [hθη, false_and, ite_false]
  have hsum (θ : A06.Orientation) :
      (∑ n ∈ Finset.Icc 1 M,
        (epsilon h ζ n - referenceWeight h ζ) •
          (A05.rho h (A06.speciesOf branches θ) (n : ℤ) *
            A05.rho h (A06.speciesOf branches θ) (-(n : ℤ)))) w =
      if θ = η then ((m : ℂ) * (epsilon h ζ m - referenceWeight h ζ)) • w else 0 := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    by_cases hθη : θ = η
    · rw [ite_eq_left hθη]
      calc
        _ = ∑ n ∈ Finset.Icc 1 M,
            if n = m then ((m : ℂ) * (epsilon h ζ m - referenceWeight h ζ)) • w else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hpair θ n hn]
          simp only [hθη, true_and]
          by_cases he : n = m
          · subst n
            rw [ite_eq_left rfl, ite_eq_left rfl, smul_smul, mul_comm]
          · rw [ite_eq_right he, ite_eq_right he, smul_zero]
        _ = _ := by
          rw [Finset.sum_eq_single m]
          · simp
          · intro n hn hnm
            simp [hnm]
          · intro hnot
            exact False.elim (hnot (Finset.mem_Icc.mpr ⟨hm, hcut⟩))
    · rw [ite_eq_right hθη]
      apply Finset.sum_eq_zero
      intro n hn
      rw [hpair θ n hn]
      simp only [hθη, false_and, ite_false, smul_zero]
  rw [error_weighted_on_budget h M K hh hM hNoAlias ζ hζ branches Ns
    hmargin _ hexc]
  change (4 : ℂ) • weightedError h M ζ branches w = _
  unfold weightedError
  rw [LinearMap.add_apply, hsum .right, hsum .left]
  cases η <;> simp only [reduceCtorEq, ite_true, ite_false, add_zero, zero_add, smul_smul]
  all_goals (congr 1; ring)

theorem first_mode_error_zero (h M K : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hK : 1 ≤ K)
    (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (η : A06.Orientation)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (hmargin : A06.branchMargins h M K Ns branches) :
    errorOperator h M ζ branches (excitedKet h Ns branches η 1) = 0 := by
  have he := single_mode_error_eigenvector h M K 1 hh hM hNoAlias
    (by omega) hM hK ζ hζ branches η Ns hN hmargin
  simpa only [referenceWeight, sub_self, mul_zero, zero_smul] using he

theorem error_nonzero_witness (h M K m : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (hm : 1 ≤ m) (hcut : m ≤ M) (hK : m ≤ K)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (hweight : epsilon h ζ m ≠ referenceWeight h ζ)
    (branches : A06.Branches σ) (η : A06.Orientation)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (hmargin : A06.branchMargins h M K Ns branches) :
    excitedKet h Ns branches η m ≠ 0 ∧
      errorOperator h M ζ branches (excitedKet h Ns branches η m) ≠ 0 := by
  have hselected : A06.marginAt h M K Ns (A06.speciesOf branches η) := by
    cases η
    · exact hmargin.1
    · exact hmargin.2
  have hmarg : A06.marginAt h M m Ns (A06.speciesOf branches η) := by
    unfold A06.marginAt at hselected ⊢
    omega
  have hv := excited_ket_nonzero h M m hh hm hcut Ns hN branches η hmarg
  refine ⟨hv, ?_⟩
  rw [single_mode_error_eigenvector h M K m hh hM hNoAlias hm hcut hK
    ζ hζ branches η Ns hN hmargin]
  exact smul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast (show m ≠ 0 by omega))) (sub_ne_zero.mpr hweight)) hv

theorem concrete_dispersion_gap :
    epsilon 8 (A01.canonicalRoot 16) 2 ≠
      referenceWeight 8 (A01.canonicalRoot 16) := by
  let z := A01.canonicalRoot 16
  have hp : IsPrimitiveRoot z 16 := A01.canonical_root_primitive 16
  have hz : z ≠ 0 := hp.ne_zero (by decide)
  have h1 : z ≠ 1 := hp.ne_one (by decide)
  intro he
  change epsilon 8 z 2 = epsilon 8 z 1 at he
  norm_num [epsilon, A01.integerCharacter, zpow_neg, zpow_natCast] at he
  have hpoly : (z - 1)^4 = 0 := by
    field_simp at he
    linear_combination -he / 4
  exact (pow_ne_zero 4 (sub_ne_zero.mpr h1)) hpoly

theorem concrete_excited_error_witness :
    A05.admissible 8 (fun _ : Fin 2 => 0) ∧
    A06.branchMargins 8 2 2 (fun _ : Fin 2 => 0) standardBranches ∧
    excitedKet 8 (fun _ : Fin 2 => 0) standardBranches .right 2 ≠ 0 ∧
    errorOperator 8 2 (A01.canonicalRoot 16) standardBranches
      (excitedKet 8 (fun _ : Fin 2 => 0) standardBranches .right 2) ≠ 0 := by
  have hN : A05.admissible 8 (fun _ : Fin 2 => 0) := by
    intro ν
    norm_num [Ch07.admissible]
  have hmarg : A06.branchMargins 8 2 2 (fun _ : Fin 2 => 0) standardBranches := by
    norm_num [A06.branchMargins, A06.marginAt]
  have hw := error_nonzero_witness 8 2 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (A01.canonicalRoot 16) (A01.canonical_root_primitive 16)
    concrete_dispersion_gap standardBranches .right (fun _ : Fin 2 => 0) hN hmarg
  exact ⟨hN, hmarg, hw.1, hw.2⟩

end Bosonize.Ch16
