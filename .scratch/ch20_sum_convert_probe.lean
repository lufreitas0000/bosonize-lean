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
  letI : DecidableEq (A05.Mode (Fin 2) 2) := A05.localModeDecidableEq (σ:=Fin 2) 2
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
noncomputable local instance modeLinearOrder : LinearOrder (A05.Mode (Fin 2) 2) := A05.localModeLinearOrder (σ:=Fin 2) 2
noncomputable local instance modeLT : LT (A05.Mode (Fin 2) 2) := A05.localModeLT (σ:=Fin 2) 2
noncomputable local instance modeLE : LE (A05.Mode (Fin 2) 2) := A05.localModeLE (σ:=Fin 2) 2
noncomputable local instance modeDecEq : DecidableEq (A05.Mode (Fin 2) 2) := A05.localModeDecidableEq (σ:=Fin 2) 2
noncomputable local instance fixedModeOrder : LinearOrder (Fin 2 × Ch01.Band 4) := A05.localModeLinearOrder (σ:=Fin 2) 2
noncomputable local instance fixedModeLT : LT (Fin 2 × Ch01.Band 4) := A05.localModeLT (σ:=Fin 2) 2
noncomputable local instance fixedModeLE : LE (Fin 2 × Ch01.Band 4) := A05.localModeLE (σ:=Fin 2) 2
noncomputable local instance fixedModeDecEq : DecidableEq (Fin 2 × Ch01.Band 4) := A05.localModeDecidableEq (σ:=Fin 2) 2

lemma speciesEraseBridge (S : A05.Occupation (Fin 2) 2) (η ν : Fin 2)
    (q k : Ch01.Band 4) :
    q ∈ Ch07.speciesConfiguration 2 (S.erase (ν,k)) η ↔
      q ∈ Ch07.speciesConfiguration 2 S η ∧ (η ≠ ν ∨ q ≠ k) := by
  rw [speciesBridge, speciesBridge]
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hne,hm⟩
    refine ⟨hm, ?_⟩
    by_cases hη : η = ν
    · right
      intro hq
      apply hne
      exact Prod.ext hη hq
    · exact Or.inl hη
  · rintro ⟨hm,hneq⟩
    refine ⟨?_,hm⟩
    intro hp
    have hp' := Prod.mk.inj hp
    rcases hneq with hη | hq
    · exact hη hp'.1
    · exact hq hp'.2

lemma speciesInsertBridge (S : A05.Occupation (Fin 2) 2) (η ν : Fin 2)
    (q k : Ch01.Band 4) :
    q ∈ Ch07.speciesConfiguration 2 (insert (ν,k) S) η ↔
      q ∈ Ch07.speciesConfiguration 2 S η ∨ (η = ν ∧ q = k) := by
  rw [speciesBridge, speciesBridge]
  simp only [Finset.mem_insert]
  constructor
  · rintro (h | h)
    · exact Or.inr (Prod.mk.inj h)
    · exact Or.inl h
  · rintro (h | ⟨hη,hq⟩)
    · exact Or.inr h
    · subst η
      subst q
      exact Or.inl rfl

lemma residual_m1_pair_unique (k p : Ch01.Band 4)
    (heq : insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) =
      residualOccupation m1) : k = mn ∧ p = m1 := by
  have hsL := congrArg (fun S => Ch07.speciesConfiguration 2 S 1) heq
  have hsR := congrArg (fun S => Ch07.speciesConfiguration 2 S 0) heq
  have hL0 : m0 ∈ Ch07.speciesConfiguration 2
      (insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k))) 1 := by
    rw [hsL, leftSpecies_residualOccupation]
    simp
  have hsrcmn : mn ∈ Ch07.speciesConfiguration 2
      (A05.groundConfiguration 2 witnessZero) 1 := by
    rw [speciesBridge, ground_memX]
    simp [witnessZero,mn]
  have hk : k ≠ m0 := by
    intro h
    subst k
    have hL0' : m0 ∈ Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 witnessZero).erase (1,m0)) 1 := by
      rw [speciesInsertBridge] at hL0
      simpa using hL0
    have hnot : m0 ∉ Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 witnessZero).erase (1,m0)) 1 := by
      rw [speciesEraseBridge]
      simp
    exact hnot hL0'
  have hkn : k = mn := by
    have hmnAbsent : mn ∉ Ch07.speciesConfiguration 2
        (insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k))) 1 := by
      rw [hsL, leftSpecies_residualOccupation]
      simp only [Finset.mem_singleton]
      intro heq
      have hv := congrArg Subtype.val heq
      norm_num [mn,m0] at hv
    have heraseAbsent : mn ∉ Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 witnessZero).erase (1,k)) 1 := by
      rw [speciesInsertBridge] at hmnAbsent
      intro hm
      exact hmnAbsent (Or.inl hm)
    by_contra hnot
    have hmnErase : mn ∈ Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 witnessZero).erase (1,k)) 1 := by
      apply (speciesEraseBridge _ _ _ _ _).mpr
      refine ⟨hsrcmn, Or.inr ?_⟩
      intro heq
      exact hnot heq.symm
    exact heraseAbsent hmnErase
  refine ⟨hkn, ?_⟩
  subst k
  have hR1 : m1 ∈ Ch07.speciesConfiguration 2
      (insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,mn))) 0 := by
    rw [hsR]
    rw [speciesBridge]
    simp [residualOccupation, m1]
  have hsource1 : m1 ∉ Ch07.speciesConfiguration 2
      ((A05.groundConfiguration 2 witnessZero).erase (1,mn)) 0 := by
    rw [speciesEraseBridge, speciesBridge, ground_memX]
    simp [witnessZero,m1,mn]
  rw [speciesInsertBridge] at hR1
  rcases hR1 with hbad | ⟨_,hp⟩
  · exact (hsource1 hbad).elim
  · exact hp.symm



lemma rightSpecies_residual_m1 :
    Ch07.speciesConfiguration 2 (residualOccupation m1) 0 =
      Ch07.groundConfiguration 2 1 := by
  ext q
  rw [speciesBridge]
  simp only [residualOccupation, Finset.mem_insert, Finset.mem_erase]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  simp only [Prod.mk.injEq, h01, false_and, false_or]
  rw [ground_memX 2 witnessZero 0 q]
  simp only [Ch07.groundConfiguration, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [witnessZero]
  constructor
  · rintro (hq | ⟨hneq, hsrc⟩)
    · have hv := congrArg Subtype.val hq
      norm_num [m1] at hv; omega
    · have hb := q.2
      dsimp [Ch01.inBandPredicate] at hb
      omega
  · intro hq
    by_cases hv : q.val = 1
    · left
      exact Subtype.ext hv
    · right
      constructor
      · intro he
        have hs := Prod.mk.inj he
        norm_num at hs
      · have hb := q.2
        dsimp [Ch01.inBandPredicate] at hb
        omega


lemma target_one_admissible : A05.admissible 2 (cdwTarget Ch16.standardBranches witnessZero) := by
  intro ν
  fin_cases ν <;> simp [Ch07.admissible, cdwTarget, Ch13.lowerCharge,
    raiseCharge, witnessZero, Ch16.standardBranches, Function.update]

lemma residual_m1_target_budget :
    residualOccupation m1 ∈ Ch14.budgetSet 2
      (cdwTarget Ch16.standardBranches witnessZero) 1 := by
  rw [Ch14.budgetSet]
  constructor
  · intro ν
    fin_cases ν
    · change Ch07.relativeCharge 2
        (Ch07.speciesConfiguration 2 (residualOccupation m1) 0) = 1
      rw [rightSpecies_residual_m1]
      exact Ch07.ground_configuration_charge 2 (by decide) 1 (by norm_num [Ch07.admissible])
    · change Ch07.relativeCharge 2
        (Ch07.speciesConfiguration 2 (residualOccupation m1) 1) = -1
      rw [leftSpecies_residualOccupation]
      norm_num [Ch07.relativeCharge]
  · rw [Ch07.totalExcitation]
    simp only [Fin.sum_univ_two]
    rw [leftSpecies_residualOccupation, rightSpecies_residual_m1]
    have hleft : Ch07.excitationEnergy 2 {m0} = 1 := by
      unfold Ch07.excitationEnergy Ch07.relativeEnergy Ch07.relativeCharge
      rw [Ch05.sea_energy_even 2 (by decide)]
      norm_num [Ch07.groundEnergy, Ch05.occupationEnergy, m0]
    have hright : Ch07.excitationEnergy 2
        (Ch07.groundConfiguration 2 1) = 0 :=
      Ch07.ground_configuration_excitation 2 (by decide) 1 (by norm_num [Ch07.admissible])
    rw [hleft, hright]
    norm_num

lemma mapIf {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (f : E →ₗ[ℂ] E) (P : Prop) [Decidable P] (x y : E) :
    f (if P then x else y) = if P then f x else f y := by
  split_ifs <;> rfl

private lemma inner_fsumX {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι]
    (f : ι → E) (x : E) :
    inner ℂ x (∑ i, f i) = ∑ i, inner ℂ x (f i) := by
  rw [← innerₛₗ_apply_apply]
  rw [map_sum]
  simp only [innerₛₗ_apply_apply]

private lemma inner_if_zeroX {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (x v : E) (p : Prop) [Decidable p] :
    inner ℂ x (if p then v else 0) = if p then inner ℂ x v else 0 := by
  split_ifs <;> simp

private lemma inner_zero_ifX {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (x v : E) (p : Prop) [Decidable p] :
    inner ℂ x (if p then 0 else v) = if p then 0 else inner ℂ x v := by
  split_ifs <;> simp

private lemma sum_single_pairX {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [LinearOrder ι] [LinearOrder κ]
    (a : ι) (b : κ) (f : ι → κ → ℂ)
    (g : ι → κ → Prop) [DecidableRel g]
    (ha : ∀ i j, g i j → i = a ∧ j = b)
    (hab : g a b) :
    (∑ i, ∑ j, if g i j then f i j else 0) = f a b := by
  classical
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro j _ hj
      have : ¬ g a j := by intro h; exact hj ((ha a j h).2)
      simp [this]
    · simp
  · intro i _ hi
    have hzero : ∀ j, ¬ g i j := by
      intro j h
      exact hi ((ha i j h).1)
    simp [hzero]
  · simp

private def residual_m1_g (k p : Ch01.Band 4) : Prop :=
  (1,k) ∈ A05.groundConfiguration 2 witnessZero ∧
  (A05.groundConfiguration 2 witnessZero).erase (1,k) ∉
    Ch14.budgetSet 2 (Ch13.lowerCharge witnessZero 1) 0 ∧
  (0,p) ∉ (A05.groundConfiguration 2 witnessZero).erase (1,k) ∧
  insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) ∈
    Ch14.budgetSet 2 (cdwTarget Ch16.standardBranches witnessZero) 1 ∧
  insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) = residualOccupation m1

private noncomputable def residual_m1_f (k p : Ch01.Band 4) : ℂ :=
  Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) k 1 *
    Ch04.fermionSign (1,k) (A05.groundConfiguration 2 witnessZero) *
    star (A01.normalization 4 : ℂ) *
    star (Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) p 1) *
    Ch04.fermionSign (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k))

lemma residual_m1_inner_expand :
    inner ℂ (A02.ket (residualOccupation m1))
      (Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 1
        (cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
          Ch16.standardBranches 1 witnessZero 0
          (@A02.ket (A05.Mode (Fin 2) 2) (inferInstance)
            (A05.localModeDecidableEq (σ:=Fin 2) 2)
            (A05.groundConfiguration 2 witnessZero)))) =
    (A01.normalization 4 : ℂ) *
      ∑ k : Ch01.Band 4, ∑ p : Ch01.Band 4,
        if residual_m1_g k p then residual_m1_f k p else 0 := by
  simp only [Ch16.standardBranches]
  rw [Ch20ResidualScratch.residualDoubleExpansion]
  simp only [Ch14.projection, mapIf, map_zero, map_smul, map_sum]
  rw [inner_smul_right]
  rw [inner_fsumX]
  simp_rw [inner_if_zeroX]
  simp_rw [inner_zero_ifX]
  simp_rw [inner_smul_right]
  simp_rw [inner_fsumX]
  simp_rw [A03.projection_ket]
  simp_rw [inner_smul_right]
  simp_rw [inner_if_zeroX]
  simp_rw [inner_smul_right]
  simp_rw [inner_if_zeroX]
  simp_rw [A02.ket_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (1,k) ∈ A05.groundConfiguration 2 witnessZero
  · simp only [hk, ite_true]
    by_cases hmid : (A05.groundConfiguration 2 witnessZero).erase (1,k) ∈
        Ch14.budgetSet 2 (Ch13.lowerCharge witnessZero 1) 0
    · simp [hmid, residual_m1_g]
    · simp only [hmid, ite_false]
      rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : (0,p) ∈ (A05.groundConfiguration 2 witnessZero).erase (1,k)
      · simp [hp, residual_m1_g]
      · simp only [hp, not_false_eq_true, ite_true]
        by_cases ht : insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) ∈
            Ch14.budgetSet 2 (cdwTarget Ch16.standardBranches witnessZero) 1
        · by_cases heq : insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) =
              residualOccupation m1
          · simp [Ch16.standardBranches, residual_m1_g, residual_m1_f, hk, hmid, hp,
              heq, mul_assoc, mul_left_comm, mul_comm]
          · have hneq : residualOccupation m1 ≠
                insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) :=
              fun h => heq h.symm
            simp [Ch16.standardBranches, residual_m1_g, hk, hmid, hp, heq, hneq]
        · by_cases heq : insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) =
              residualOccupation m1
          · have hIns : insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) ∈
                Ch14.budgetSet 2 (cdwTarget Ch16.standardBranches witnessZero) 1 := by
              rw [heq]
              exact residual_m1_target_budget
            exact (ht hIns).elim
          · have hneq : residualOccupation m1 ≠
                insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) :=
              fun h => heq h.symm
            simp [Ch16.standardBranches, residual_m1_g, hk, hmid, hp, heq, hneq]
  · simp [hk, residual_m1_g]


end Bosonize.Ch20
