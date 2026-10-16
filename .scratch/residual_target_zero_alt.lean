import Bosonize.Core.Ch14Mandelstam
import Bosonize.Core.Ch16FieldHamiltonian
import BosonizeStubs.Ch20CDW

open scoped BigOperators Classical
open Bosonize
namespace Bosonize.Ch20


def mn : Ch01.Band 4 := ⟨-1, by norm_num [Ch01.inBandPredicate]⟩
def m0 : Ch01.Band 4 := ⟨0, by norm_num [Ch01.inBandPredicate]⟩
def m1 : Ch01.Band 4 := ⟨1, by norm_num [Ch01.inBandPredicate]⟩
def m2 : Ch01.Band 4 := ⟨2, by norm_num [Ch01.inBandPredicate]⟩

noncomputable def residualOccupation (l : Ch01.Band 4) : A05.Occupation (Fin 2) 2 :=
  insert (0,l) ((A05.groundConfiguration 2 witnessZero).erase (1,mn))

private lemma ground_memX (h : ℕ) (Ns : Fin 2 → ℤ) (ν : Fin 2)
    (k : Ch01.Band (2*h)) :
    (ν,k) ∈ A05.groundConfiguration h Ns ↔ k.val ≤ Ns ν := by
  simp only [A05.groundConfiguration, A05.jointConfiguration,
    Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Ch07.groundConfiguration, Finset.mem_filter]
  aesop

private lemma speciesBridge (S : A05.Occupation (Fin 2) 2) (η : Fin 2)
    (q : Ch01.Band 4) :
    q ∈ Ch07.speciesConfiguration 2 S η ↔ (η,q) ∈ S := by
  simp only [Ch07.speciesConfiguration, Finset.mem_image, Finset.mem_filter]
  aesop

private lemma leftSpecies_residualOccupation (l : Ch01.Band 4) :
    Ch07.speciesConfiguration 2 (residualOccupation l) 1 = {m0} := by
  ext q
  rw [speciesBridge, Finset.mem_singleton]
  simp only [residualOccupation, Finset.mem_insert, Finset.mem_erase]
  have hs : (1 : Fin 2) ≠ 0 := by decide
  simp only [Prod.mk.injEq, hs, false_and, false_or]
  rw [ground_memX 2 witnessZero 1 q]
  simp only [witnessZero]
  constructor
  · rintro ⟨hn,hq⟩
    apply Subtype.ext
    have hb := q.property
    simp [Ch01.inBandPredicate] at hb
    have hneq : q.val ≠ -1 := by
      intro hv
      apply hn
      exact Prod.ext rfl (Subtype.ext hv)
    norm_num [m0]
    omega
  · intro hq
    have hv : q.val = 0 := congrArg Subtype.val hq
    constructor
    · intro he
      have hqmn : q = mn := by
        apply Subtype.ext
        exact congrArg Subtype.val (congrArg Prod.snd he)
      rw [hq] at hqmn
      have hv2 := congrArg Subtype.val hqmn
      norm_num [m0,mn] at hv2
    · simpa [witnessZero] using (show q.val ≤ 0 by omega)

private lemma leftSpecies_residual_excitation (l : Ch01.Band 4) :
    Ch07.excitationEnergy 2
      (Ch07.speciesConfiguration 2 (residualOccupation l) 1) = 1 := by
  rw [leftSpecies_residualOccupation]
  unfold Ch07.excitationEnergy Ch07.relativeEnergy Ch07.relativeCharge
  rw [Ch05.sea_energy_even 2 (by decide)]
  norm_num [Ch07.groundEnergy, Ch05.occupationEnergy, m0]

private lemma residualOccupation_totalExcitation_pos (l : Ch01.Band 4) :
    1 ≤ Ch07.totalExcitation 2 (residualOccupation l) := by
  rw [Ch07.totalExcitation]
  have hsingle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun ν : Fin 2 => Ch07.excitationEnergy 2
      (Ch07.speciesConfiguration 2 (residualOccupation l) ν))
    (fun ν hν => Ch07.excitation_nonneg 2 (by decide)
      (Ch07.speciesConfiguration 2 (residualOccupation l) ν))
    (Finset.mem_univ (1 : Fin 2))
  have hleft := leftSpecies_residual_excitation l
  omega

lemma residualOccupation_not_in_target_budget_zero (l : Ch01.Band 4) :
    residualOccupation l ∉
      Ch14.budgetSet 2 (cdwTarget Ch16.standardBranches witnessZero) 0 := by
  intro hb
  have htot := hb.2
  have hpos := residualOccupation_totalExcitation_pos l
  omega

end Bosonize.Ch20


namespace Bosonize.Ch20ResidualScratch
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [LinearOrder σ]
noncomputable local instance modeOrd (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
noncomputable local instance modeDecEq (h : ℕ) : DecidableEq (A05.Mode σ h) := A05.localModeDecidableEq h
lemma fieldKet (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (ν : σ) (x : ℤ) (S : A05.Occupation σ h) :
    A05.liftedAnnihilation h b ν x (A02.ket S) =
      (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h),
        if (ν,k) ∈ S then
          (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) S) •
            A02.ket (S.erase (ν,k))
        else 0 := by
  simp only [A05.liftedAnnihilation, LinearMap.smul_apply,
    LinearMap.sum_apply, A05.annihilation, Ch04.annihilation_ket]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · simp only [smul_smul]
  · simp
end Bosonize.Ch20ResidualScratch

namespace Bosonize.Ch20ResidualScratch
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [LinearOrder σ]
noncomputable local instance modeOrd2 (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
noncomputable local instance modeDecEq2 (h : ℕ) : DecidableEq (A05.Mode σ h) := A05.localModeDecidableEq h

lemma adjointLiftedKet (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (ν : σ) (x : ℤ) (S : A05.Occupation σ h) :
    LinearMap.adjoint (A05.liftedAnnihilation h b ν x) (A02.ket S) =
      star (A01.normalization (2*h) : ℂ) •
       ∑ k : Ch01.Band (2*h),
        star (Ch06Ext.twistedCharacter (2*h) (b ν) k x) •
          (if (ν,k) ∉ S then Ch04.fermionSign (ν,k) S • A02.ket (insert (ν,k) S) else 0) := by
  rw [← LinearMap.star_eq_adjoint]
  simp [A05.liftedAnnihilation, A05.annihilation, Ch04.annihilation_eq_adjoint,
    LinearMap.star_eq_adjoint, LinearMap.adjoint_adjoint, Ch04.creation_ket]

lemma oneSubProjectionKet (h : ℕ) (Ns : σ → ℤ) (K : ℕ)
    (S : A05.Occupation σ h) (c : ℂ) :
    (1 - Ch14.projection h Ns K) (c • A02.ket S) =
      if S ∈ Ch14.budgetSet h Ns K then 0 else c • A02.ket S := by
  rw [LinearMap.sub_apply, Module.End.one_apply, map_smul]
  simp only [Ch14.projection, A03.projection_ket]
  by_cases hs : S ∈ Ch14.budgetSet h Ns K <;> simp [hs]

end Bosonize.Ch20ResidualScratch

namespace Bosonize.Ch20ResidualScratch
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [LinearOrder σ]
noncomputable local instance modeOrd3 (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
noncomputable local instance modeDecEq3 (h : ℕ) : DecidableEq (A05.Mode σ h) := A05.localModeDecidableEq h

lemma projectedFieldKet (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (br : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ) (K : ℕ)
    (S : A05.Occupation σ h) :
    (1 - Ch14.projection h (Ch13.lowerCharge Ns br.leftSpecies) K)
       (A05.liftedAnnihilation h b br.leftSpecies x (A02.ket S)) =
      (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h),
        if (br.leftSpecies,k) ∈ S then
          if S.erase (br.leftSpecies,k) ∈
              Ch14.budgetSet h (Ch13.lowerCharge Ns br.leftSpecies) K then 0 else
            (Ch06Ext.twistedCharacter (2*h) (b br.leftSpecies) k x *
              Ch04.fermionSign (br.leftSpecies,k) S) •
              A02.ket (S.erase (br.leftSpecies,k))
        else 0 := by
  rw [fieldKet]
  simp only [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (br.leftSpecies,k) ∈ S
  · simp only [hk, ite_true]
    rw [oneSubProjectionKet]
  · simp [hk]

end Bosonize.Ch20ResidualScratch

namespace Bosonize.Ch20ResidualScratch
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [LinearOrder σ]
noncomputable local instance modeOrd4 (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
noncomputable local instance modeDecEq4 (h : ℕ) : DecidableEq (A05.Mode σ h) := A05.localModeDecidableEq h

lemma residualExpansionLeft (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (br : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ) (Km : ℕ)
    (S : A05.Occupation σ h) :
    Ch20.cdwResidualOp h b br x Ns Km (A02.ket S) =
      (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h),
        if (br.leftSpecies,k) ∈ S then
          (LinearMap.adjoint (Ch20.fieldOf h b br.rightSpecies x))
            ((1 - Ch14.projection h (Ch13.lowerCharge Ns br.leftSpecies) Km)
              ((Ch06Ext.twistedCharacter (2*h) (b br.leftSpecies) k x *
                Ch04.fermionSign (br.leftSpecies,k) S) •
                A02.ket (S.erase (br.leftSpecies,k))))
        else 0 := by
  simp only [Ch20.cdwResidualOp, Module.End.mul_apply, Ch20.fieldOf]
  rw [fieldKet]
  simp only [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (br.leftSpecies,k) ∈ S
  · simp only [hk, ite_true, map_smul]
  · simp only [hk, ite_false, map_zero]

end Bosonize.Ch20ResidualScratch

namespace Bosonize.Ch20ResidualScratch
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [LinearOrder σ]
noncomputable local instance modeOrd5 (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
noncomputable local instance modeDecEq5 (h : ℕ) : DecidableEq (A05.Mode σ h) := A05.localModeDecidableEq h

lemma residualDoubleExpansion (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (br : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ) (Km : ℕ)
    (S : A05.Occupation σ h) :
    Ch20.cdwResidualOp h b br x Ns Km (A02.ket S) =
      (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h),
        if (br.leftSpecies,k) ∈ S then
          if S.erase (br.leftSpecies,k) ∈
              Ch14.budgetSet h (Ch13.lowerCharge Ns br.leftSpecies) Km then 0 else
            (Ch06Ext.twistedCharacter (2*h) (b br.leftSpecies) k x *
              Ch04.fermionSign (br.leftSpecies,k) S) •
            (star (A01.normalization (2*h) : ℂ) • ∑ p : Ch01.Band (2*h),
              star (Ch06Ext.twistedCharacter (2*h) (b br.rightSpecies) p x) •
                (if (br.rightSpecies,p) ∉ S.erase (br.leftSpecies,k) then
                  Ch04.fermionSign (br.rightSpecies,p) (S.erase (br.leftSpecies,k)) •
                    A02.ket (insert (br.rightSpecies,p) (S.erase (br.leftSpecies,k)))
                 else 0))
        else 0 := by
  simp only [Ch20.cdwResidualOp, Module.End.mul_apply, Ch20.fieldOf]
  rw [projectedFieldKet]
  simp only [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (br.leftSpecies,k) ∈ S
  · simp only [hk, ite_true]
    by_cases hb : S.erase (br.leftSpecies,k) ∈
        Ch14.budgetSet h (Ch13.lowerCharge Ns br.leftSpecies) Km
    · simp [hb]
    · simp only [hb, ite_false, map_smul]
      rw [adjointLiftedKet]
  · simp only [hk, ite_false, map_zero]

end Bosonize.Ch20ResidualScratch

namespace Bosonize.Ch20
open scoped BigOperators Classical
noncomputable local instance targetKillModeDecEq : DecidableEq (A05.Mode (Fin 2) 2) := fun a b => A05.localModeDecidableEq 2 a b
noncomputable local instance targetModeOrder (h : ℕ) : LinearOrder (A05.Mode (Fin 2) h) := A05.speciesOrder h
noncomputable local instance targetModeLT (h : ℕ) : LT (A05.Mode (Fin 2) h) := (A05.speciesOrder h).toLT
noncomputable local instance targetModeLE (h : ℕ) : LE (A05.Mode (Fin 2) h) := (A05.speciesOrder h).toLE
noncomputable local instance targetModeDecEq (h : ℕ) : DecidableEq (A05.Mode (Fin 2) h) := (A05.speciesOrder h).toDecidableEq
lemma targetZero_candidate :
    Ch14.projectedMap 2 witnessZero (cdwTarget Ch16.standardBranches witnessZero)
        0 0 (cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
          Ch16.standardBranches 1 witnessZero 0)
        (Ch14.groundVector 2 (by decide) witnessZero witnessZero_admissible 0) = 0 := by
  classical
  apply Subtype.ext
  change Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 0
    ((cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
      Ch16.standardBranches 1 witnessZero 0) (A05.groundKet 2 witnessZero)) = 0
  change Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 0
    ((cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4) Ch16.standardBranches 1 witnessZero 0)
      (A02.ket (A05.groundConfiguration 2 witnessZero))) = 0
  rw [Ch20ResidualScratch.residualDoubleExpansion]
  simp only [map_smul, map_sum]
  apply (smul_eq_zero).2
  right
  apply Finset.sum_eq_zero
  intro x hx
  fin_cases x
  all_goals norm_num [Ch16.standardBranches, ground_memX, Ch01.inBandPredicate, witnessZero]
end Bosonize.Ch20

namespace Bosonize.Ch20
noncomputable local instance targetKillModeDecEq2 : DecidableEq (A05.Mode (Fin 2) 2) := fun a b => A05.localModeDecidableEq 2 a b
noncomputable local instance targetKillModeOrder2 : LinearOrder (A05.Mode (Fin 2) 2) := A05.speciesOrder 2
noncomputable local instance targetKillModeLT2 : LT (A05.Mode (Fin 2) 2) := (A05.speciesOrder 2).toLT
noncomputable local instance targetKillModeLE2 : LE (A05.Mode (Fin 2) 2) := (A05.speciesOrder 2).toLE
lemma targetProjKill (l : Ch01.Band 4) :
  Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 0
    (A02.ket (residualOccupation l)) = 0 := by
  classical
  rw [Ch14.projection, A03.projection_ket]
  have hbad : residualOccupation l ∉ Ch14.budgetSet 2 (cdwTarget Ch16.standardBranches witnessZero) 0 := by
    intro hb
    have hpos := residualOccupation_totalExcitation_pos l
    have ht := hb.2
    omega
  simp only [ite_eq_right hbad]
end Bosonize.Ch20

namespace Bosonize.Ch20
noncomputable local instance projSumModeDecEq : DecidableEq (A05.Mode (Fin 2) 2) := fun a b => A05.localModeDecidableEq 2 a b
noncomputable local instance projSumModeOrder : LinearOrder (Fin 2 × Ch01.Band 4) := A05.speciesOrder 2
noncomputable local instance projSumModeLT : LT (A05.Mode (Fin 2) 2) := (A05.speciesOrder 2).toLT
noncomputable local instance projSumModeLE : LE (A05.Mode (Fin 2) 2) := (A05.speciesOrder 2).toLE
lemma projectResidualSum (l : Ch01.Band 4) :
    Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 0
      ((A01.normalization 4 : ℂ) • ∑ p : Ch01.Band 4,
        star (Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) p 1) •
          (if (0,p) ∉ (A05.groundConfiguration 2 witnessZero).erase (1,mn) then
            Ch04.fermionSign (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,mn)) •
              A02.ket (insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,mn)))
           else 0)) = 0 := by
  classical
  rw [map_smul, map_sum]
  apply (smul_eq_zero).2
  right
  apply Finset.sum_eq_zero
  intro p hp
  by_cases h : (0,p) ∉ (A05.groundConfiguration 2 witnessZero).erase (1,mn)
  · simp [h, residualOccEq, targetProjKill, map_smul]
  · simp [h]
end Bosonize.Ch20

namespace Bosonize.Ch20
noncomputable local instance eqModeDecEq : DecidableEq (A05.Mode (Fin 2) 2) := fun a b => A05.localModeDecidableEq 2 a b
noncomputable local instance eqModeOrder : LinearOrder (A05.Mode (Fin 2) 2) := A05.speciesOrder 2
lemma residualOccEq (l : Ch01.Band 4) : residualOccupation l = insert (0,l) ((A05.groundConfiguration 2 witnessZero).erase (1,mn)) := by
  ext z
  simp [residualOccupation]
end Bosonize.Ch20
