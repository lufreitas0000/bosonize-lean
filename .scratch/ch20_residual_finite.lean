import Bosonize.Core.Ch14Mandelstam
import Bosonize.Core.Ch16FieldHamiltonian
import BosonizeStubs.Ch20CDW

open scoped BigOperators Classical
open Bosonize

noncomputable local instance fixedModeOrder : LinearOrder (A05.Mode (Fin 2) 2) := A05.localModeLinearOrder (σ:=Fin 2) 2
noncomputable local instance fixedModeLT : LT (A05.Mode (Fin 2) 2) := A05.localModeLT (σ:=Fin 2) 2
noncomputable local instance fixedModeLE : LE (A05.Mode (Fin 2) 2) := A05.localModeLE (σ:=Fin 2) 2
noncomputable local instance fixedModeDecEq : DecidableEq (A05.Mode (Fin 2) 2) :=
  fun a b => A05.localModeDecidableEq (σ:=Fin 2) 2 a b
noncomputable local instance fixedPairOrder : LinearOrder (Fin 2 × Ch01.Band 4) := A05.localModeLinearOrder (σ:=Fin 2) 2
noncomputable local instance fixedPairLT : LT (Fin 2 × Ch01.Band 4) := A05.localModeLT (σ:=Fin 2) 2
noncomputable local instance fixedPairLE : LE (Fin 2 × Ch01.Band 4) := A05.localModeLE (σ:=Fin 2) 2
noncomputable local instance fixedPairDecEq : DecidableEq (Fin 2 × Ch01.Band 4) := A05.localModeDecidableEq (σ:=Fin 2) 2

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
noncomputable local instance modeOrd (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.localModeLinearOrder h
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
noncomputable local instance modeOrd2 (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.localModeLinearOrder h
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
noncomputable local instance modeOrd3 (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.localModeLinearOrder h
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
noncomputable local instance modeOrd4 (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.localModeLinearOrder h
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
noncomputable local instance modeOrd5 (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.localModeLinearOrder h
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
open Classical
lemma erase_m0_eq_lower_ground :
    (A05.groundConfiguration 2 witnessZero).erase (1,m0) =
      A05.groundConfiguration 2 (Ch13.lowerCharge witnessZero 1) := by
  ext z
  obtain ⟨η,q⟩ := z
  rw [Finset.mem_erase, ground_memX 2 witnessZero η q,
    ground_memX 2 (Ch13.lowerCharge witnessZero 1) η q]
  by_cases hη : η = 1
  · subst η
    simp only [Ch13.lowerCharge, Function.update_self, witnessZero]
    constructor
    · rintro ⟨hne, hle⟩
      have hq : q.val ≠ 0 := by
        intro hv
        apply hne
        exact Prod.ext rfl (Subtype.ext (by simpa [m0] using hv))
      omega
    · intro hle
      constructor
      · intro he
        have hv := congrArg Subtype.val (congrArg Prod.snd he)
        norm_num [m0] at hv
        omega
      · omega
  · simp [Ch13.lowerCharge, witnessZero, hη]
end Bosonize.Ch20

namespace Bosonize.Ch20
lemma ground_mem_witnessLeft (x : Ch01.Band 4) :
    (1,x) ∈ A05.groundConfiguration 2 witnessZero ↔ x.val ≤ 0 := by
  simp only [A05.groundConfiguration, A05.jointConfiguration, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image, Ch07.groundConfiguration,
    Finset.mem_filter]
  simp [witnessZero]

lemma lower_witness_admissible : A05.admissible 2 (Ch13.lowerCharge witnessZero 1) := by
  intro ν
  fin_cases ν <;> simp [Ch07.admissible, Ch13.lowerCharge, witnessZero, Function.update]

lemma erase_m0_mem_mid_budget :
    (A05.groundConfiguration 2 witnessZero).erase (1,m0) ∈
      Ch14.budgetSet 2 (Ch13.lowerCharge witnessZero 1) 0 := by
  rw [erase_m0_eq_lower_ground]
  rw [Ch14.budgetSet]
  have hmem := A05.ground_mem_budget 2 (by decide)
    (Ch13.lowerCharge witnessZero 1) lower_witness_admissible 0
  have hmem' : A02.ket (A05.groundConfiguration 2 (Ch13.lowerCharge witnessZero 1)) ∈
      Ch07.speciesBudget 2 (Ch13.lowerCharge witnessZero 1) 0 := by
    change A05.groundKet 2 (Ch13.lowerCharge witnessZero 1) ∈
      A05.jointBudget 2 (Ch13.lowerCharge witnessZero 1) 0
    exact hmem
  exact (Ch07.species_budget_ket 2
    (A05.groundConfiguration 2 (Ch13.lowerCharge witnessZero 1))
    (Ch13.lowerCharge witnessZero 1) 0).mp hmem' 
end Bosonize.Ch20

namespace Bosonize.Ch20
open Classical
lemma erased_mn_species_one_eq :
    Ch07.speciesConfiguration 2
      ((A05.groundConfiguration 2 witnessZero).erase (1,mn)) 1 = {m0} := by
  have hcfg : Ch07.speciesConfiguration 2
      ((A05.groundConfiguration 2 witnessZero).erase (1,mn)) 1 =
      Ch07.speciesConfiguration 2 (residualOccupation m0) 1 := by
    ext q
    rw [speciesBridge, speciesBridge]
    simp [residualOccupation, Finset.mem_erase]
  rw [hcfg, leftSpecies_residualOccupation]

lemma erased_mn_total_excitation_ge_one :
    1 ≤ Ch07.totalExcitation 2 ((A05.groundConfiguration 2 witnessZero).erase (1,mn)) := by
  rw [Ch07.totalExcitation]
  have hsingle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun ν : Fin 2 => Ch07.excitationEnergy 2
      (Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 witnessZero).erase (1,mn)) ν))
    (fun ν hν => Ch07.excitation_nonneg 2 (by decide)
      (Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 witnessZero).erase (1,mn)) ν))
    (Finset.mem_univ (1 : Fin 2))
  have hleft : Ch07.excitationEnergy 2
      (Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 witnessZero).erase (1,mn)) 1) = 1 := by
    rw [erased_mn_species_one_eq]
    exact leftSpecies_residual_excitation m0
  omega

lemma erase_mn_not_mid_budget :
    (A05.groundConfiguration 2 witnessZero).erase (1,mn) ∉
      Ch14.budgetSet 2 (Ch13.lowerCharge witnessZero 1) 0 := by
  intro hb
  have htot := hb.2
  have hpos := erased_mn_total_excitation_ge_one
  omega
end Bosonize.Ch20


namespace Bosonize.Ch20
open scoped BigOperators Classical
lemma targetProjKill (l : Ch01.Band 4) :
    Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 0
      (A02.ket (residualOccupation l)) = 0 := by
  rw [Ch14.projection, A03.projection_ket]
  have hbad : residualOccupation l ∉
      Ch14.budgetSet 2 (cdwTarget Ch16.standardBranches witnessZero) 0 := by
    intro hb
    have hpos := residualOccupation_totalExcitation_pos l
    have ht := hb.2
    omega
  simp only [ite_eq_right hbad]
lemma residualOccEq (l : Ch01.Band 4) :
    insert (0,l) ((A05.groundConfiguration 2 witnessZero).erase (1,mn)) =
      residualOccupation l := rfl
lemma target_projection_created_sum (c : ℂ) :
    Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 0
      (c •
        ∑ p : Ch01.Band 4,
          if (0,p) ∈ A05.groundConfiguration 2 witnessZero then 0 else
            star (Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) p 1) •
              Ch04.fermionSign (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,mn)) •
                A02.ket (insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,mn)))
        ) = 0 := by
  simp only [map_smul, map_sum]
  apply (smul_eq_zero).2
  right
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : (0,p) ∈ A05.groundConfiguration 2 witnessZero
  · simp [hp]
  · have hp' : (0,p) ∉ (A05.groundConfiguration 2 witnessZero).erase (1,mn) := by
      intro he
      exact hp (Finset.mem_erase.mp he).2
    simp only [hp, ite_false]
    simp only [LinearMap.map_smul, residualOccEq, targetProjKill, smul_zero]
    

lemma targetZero_candidate :
    Ch14.projectedMap 2 witnessZero (cdwTarget Ch16.standardBranches witnessZero)
        0 0 (cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
          Ch16.standardBranches 1 witnessZero 0)
        (Ch14.groundVector 2 (by decide) witnessZero witnessZero_admissible 0) = 0 := by
  apply Subtype.ext
  change Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 0
    ((cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
      Ch16.standardBranches 1 witnessZero 0) (A05.groundKet 2 witnessZero)) = 0
  change Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 0
    ((cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
      Ch16.standardBranches 1 witnessZero 0)
      (@A02.ket (A05.Mode (Fin 2) 2) _
        (A05.localModeDecidableEq (σ:=Fin 2) 2)
        (A05.groundConfiguration 2 witnessZero))) = 0
  rw [Ch20ResidualScratch.residualDoubleExpansion]
  simp only [map_smul, map_sum]
  apply (smul_eq_zero).2
  right
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hmem : (1,x) ∈ A05.groundConfiguration 2 witnessZero
  · have hv := (ground_memX 2 witnessZero 1 x).mp hmem
    simp [witnessZero] at hv
    have hband : -1 ≤ x.val ∧ x.val ≤ 2 := by
      have h := x.property
      dsimp [Ch01.inBandPredicate] at h
      omega
    have hvals : x.val = -1 ∨ x.val = 0 := by omega
    rcases hvals with hneg | hzero
    · have heq : x = mn := by
        apply Subtype.ext
        simpa [mn] using hneg
      subst x
      have hsrc : (Ch16.standardBranches.leftSpecies,mn) ∈ A05.groundConfiguration 2 witnessZero := by
        simpa [Ch16.standardBranches] using hmem
      simp [Ch16.standardBranches]
      have hmid : (A05.groundConfiguration 2 witnessZero).erase (1,mn) ∉
          Ch14.budgetSet 2 (Ch13.lowerCharge witnessZero 1) 0 := by
        exact erase_mn_not_mid_budget
      simp only [ite_eq_left hmem, ite_eq_right hmid]
      have hkill := target_projection_created_sum (A01.normalization 4 : ℂ)
      simp only [LinearMap.map_smul]
      change (Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) mn 1 *
          Ch04.fermionSign (1,mn) (A05.groundConfiguration 2 witnessZero)) •
        (Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 0)
          (A01.normalization 4 •
            ∑ p : Ch01.Band 4,
              if (0,p) ∈ A05.groundConfiguration 2 witnessZero then 0 else
                star (Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) p 1) •
                  Ch04.fermionSign (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,mn)) •
                  A02.ket (insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,mn)))) = 0
      exact (congrArg (fun z =>
        (Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) mn 1 *
          Ch04.fermionSign (1,mn) (A05.groundConfiguration 2 witnessZero)) • z) hkill).trans
          (by simp)
    · have heq : x = m0 := by
        apply Subtype.ext
        simpa [m0] using hzero
      subst x
      have hsrc : (Ch16.standardBranches.leftSpecies,m0) ∈ A05.groundConfiguration 2 witnessZero := by
        simpa [Ch16.standardBranches] using hmem
      have hmid : (A05.groundConfiguration 2 witnessZero).erase
          (Ch16.standardBranches.leftSpecies,m0) ∈
          Ch14.budgetSet 2 (Ch13.lowerCharge witnessZero Ch16.standardBranches.leftSpecies) 0 := by
        simpa [Ch16.standardBranches] using erase_m0_mem_mid_budget
      simp only [ite_eq_left hmid]
      simp [Ch16.standardBranches, hmem]
  · simp [Ch16.standardBranches, hmem]
end Bosonize.Ch20

namespace Bosonize.Ch20
open Classical
lemma erasedSpeciesBridge (S : A05.Occupation (Fin 2) 2) (η ν : Fin 2)
    (q k : Ch01.Band 4) :
    q ∈ Ch07.speciesConfiguration 2 (S.erase (ν,k)) η ↔
      q ∈ Ch07.speciesConfiguration 2 S η ∧ (η ≠ ν ∨ q ≠ k) := by
  rw [speciesBridge, speciesBridge]
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hne, hm⟩
    refine ⟨hm, ?_⟩
    by_cases hη : η = ν
    · right
      intro hq
      apply hne
      exact Prod.ext hη hq
    · exact Or.inl hη
  · rintro ⟨hm, hneq⟩
    refine ⟨?_, hm⟩
    intro hp
    have hparts := Prod.mk.inj hp
    rcases hneq with hη | hq
    · exact hη hparts.1
    · exact hq hparts.2
end Bosonize.Ch20

