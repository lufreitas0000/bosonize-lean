import Bosonize.Core.Ch14Mandelstam
import Bosonize.Core.Ch16FieldHamiltonian
import Bosonize.Core.Ch17LuttingerModels
import Bosonize.Core.Ch18Bogoliubov

namespace Bosonize.Ch20

open scoped BigOperators Classical

section FiniteCAR

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

/-- Raise one source charge, without changing any other species. -/
noncomputable def raiseCharge (Ns : σ → ℤ) (ν : σ) : σ → ℤ :=
  Function.update Ns ν (Ns ν + 1)

/-- Reflect only the left charge label; this is not a Fock-space operator. -/
noncomputable def reflectLeft (branches : A06.Branches σ) (Ns : σ → ℤ) : σ → ℤ :=
  Function.update Ns branches.leftSpecies (-(Ns branches.leftSpecies))

noncomputable def cdwTarget (branches : A06.Branches σ) (Ns : σ → ℤ) : σ → ℤ :=
  raiseCharge (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies

noncomputable def scTarget (branches : A06.Branches σ) (Ns : σ → ℤ) : σ → ℤ :=
  Ch13.lowerCharge (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies

noncomputable def cdwShift (branches : A06.Branches σ) (ν : σ) : ℤ :=
  (if ν = branches.rightSpecies then (1 : ℤ) else 0) -
    (if ν = branches.leftSpecies then (1 : ℤ) else 0)

noncomputable def scShift (branches : A06.Branches σ) (ν : σ) : ℤ :=
  -(if ν = branches.rightSpecies then (1 : ℤ) else 0) -
    (if ν = branches.leftSpecies then (1 : ℤ) else 0)

omit [Fintype σ] in
lemma lowerCharge_raiseCharge (Ns : σ → ℤ) (ν : σ) :
    Ch13.lowerCharge (raiseCharge Ns ν) ν = Ns := by
  funext γ
  by_cases hγ : γ = ν <;> simp [Ch13.lowerCharge, raiseCharge, hγ]

omit [Fintype σ] in
lemma raiseCharge_lowerCharge (Ns : σ → ℤ) (ν : σ) :
    raiseCharge (Ch13.lowerCharge Ns ν) ν = Ns := by
  funext γ
  by_cases hγ : γ = ν <;> simp [Ch13.lowerCharge, raiseCharge, hγ]

omit [Fintype σ] in
lemma cdwTarget_apply (branches : A06.Branches σ) (Ns : σ → ℤ) (ν : σ) :
    cdwTarget branches Ns ν = Ns ν + cdwShift branches ν := by
  unfold cdwTarget cdwShift raiseCharge Ch13.lowerCharge
  by_cases hR : ν = branches.rightSpecies
  · subst ν
    by_cases hEq : branches.rightSpecies = branches.leftSpecies
    · simp [Function.update, hEq]
    · simp [Function.update, hEq]
  · by_cases hL : ν = branches.leftSpecies
    · have hLR : branches.leftSpecies ≠ branches.rightSpecies := by
        intro he
        exact hR (hL.trans he)
      simp [Function.update, hL, hLR]
      ring
    · simp [Function.update, hR, hL]

omit [Fintype σ] in
lemma scTarget_apply (branches : A06.Branches σ) (Ns : σ → ℤ) (ν : σ) :
    scTarget branches Ns ν = Ns ν + scShift branches ν := by
  unfold scTarget scShift Ch13.lowerCharge
  by_cases hR : ν = branches.rightSpecies <;>
    by_cases hL : ν = branches.leftSpecies
  · exact False.elim (branches.distinct (hR.symm.trans hL))
  · have hRL : branches.rightSpecies ≠ branches.leftSpecies := by
      intro he
      exact hL (hR.trans he)
    subst ν
    simp [Function.update, hRL]
    ring
  · have hLR : branches.leftSpecies ≠ branches.rightSpecies := branches.distinct.symm
    subst ν
    simp [Function.update, hLR]
    ring
  · simp [Function.update, hR, hL]

omit [Fintype σ] in
lemma reflectLeft_involutive (branches : A06.Branches σ) (Ns : σ → ℤ) :
    reflectLeft branches (reflectLeft branches Ns) = Ns := by
  funext γ
  by_cases hγ : γ = branches.leftSpecies <;> simp [reflectLeft, hγ]

omit [Fintype σ] in
lemma cdwTarget_lower_right (branches : A06.Branches σ) (Ns : σ → ℤ) :
    Ch13.lowerCharge (cdwTarget branches Ns) branches.rightSpecies =
      Ch13.lowerCharge Ns branches.leftSpecies := by
  simp [cdwTarget, lowerCharge_raiseCharge]

/-- The actual A05 position annihilator; creation is its true adjoint. -/
noncomputable def fieldOf (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (ν : σ) (x : ℤ) : A05.Operators σ h :=
  A05.liftedAnnihilation h b ν x

noncomputable def orderCDW (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) : A05.Operators σ h :=
  LinearMap.adjoint (fieldOf h b branches.rightSpecies x) *
    fieldOf h b branches.leftSpecies x

noncomputable def orderSC (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) : A05.Operators σ h :=
  fieldOf h b branches.rightSpecies x * fieldOf h b branches.leftSpecies x

/-- The discarded intermediate channel is a genuine ambient CAR operator. -/
noncomputable def cdwResidualOp (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ) (Km : ℕ) :
    A05.Operators σ h :=
  LinearMap.adjoint (fieldOf h b branches.rightSpecies x) *
    (1 - Ch14.projection h (Ch13.lowerCharge Ns branches.leftSpecies) Km) *
    fieldOf h b branches.leftSpecies x

noncomputable def scResidualOp (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ) (Km : ℕ) :
    A05.Operators σ h :=
  fieldOf h b branches.rightSpecies x *
    (1 - Ch14.projection h (Ch13.lowerCharge Ns branches.leftSpecies) Km) *
    fieldOf h b branches.leftSpecies x

/-- Global CAR charge law; no budget or spurious cutoff assumption. -/
lemma orderCDW_charge_commutator (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (ν : σ) :
    A02.commutator (A05.chargeObservable h ν) (orderCDW h b branches x) =
      ((cdwShift branches ν : ℤ) : ℂ) • orderCDW h b branches x := by
  let : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
  let : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
  have hdiag : A07Interactions.seaNormalRho h ν 0 =
      ∑ k : Ch01.Band (2 * h), A07Interactions.seaSubtractedNumber h ν k := by
    unfold A07Interactions.seaNormalRho
    have hPairDiag (z : Ch01.Band (2 * h) × Ch01.Band (2 * h))
        (hz : z ∈ A04.validPairs (2 * h) 0) : z.1 = z.2 := by
      have he := (A04.mem_valid_pairs (2 * h) 0 z.1 z.2).mp hz
      apply Subtype.ext
      omega
    apply Finset.sum_bij (fun z _ => z.1)
    · intro z hz
      exact Finset.mem_univ _
    · intro z hZ w hW he
      apply Prod.ext
      · exact he
      · exact (hPairDiag z hZ).symm.trans (he.trans (hPairDiag w hW))
    · intro k hk
      refine ⟨(k, k), ?_, rfl⟩
      apply (A04.mem_valid_pairs (2 * h) 0 k k).mpr
      simp
    · intro z hZ
      rw [hPairDiag z hZ]
      simp only [A07Interactions.seaNormalBilinear,
        A07Interactions.seaSubtractedNumber, A07Interactions.numberOp,
        ite_true, A05.creation, A05.annihilation]
  have hcharge : A05.chargeObservable h ν =
      ∑ k : Ch01.Band (2 * h), A07Interactions.seaSubtractedNumber h ν k :=
    (A07Interactions.sea_normal_rho_zero h ν).symm.trans hdiag
  have hanna (η : σ) (k : Ch01.Band (2 * h)) :
      A02.commutator (A05.chargeObservable h ν) (A05.annihilation h η k) =
        -(if ν = η then (1 : ℂ) else 0) • A05.annihilation h η k := by
    rw [hcharge]
    simp only [A02.commutator, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    change (∑ j : Ch01.Band (2 * h),
        A02.commutator (A07Interactions.seaSubtractedNumber h ν j)
          (A05.annihilation h η k)) = _
    have hnum (j : Ch01.Band (2 * h)) :
        A02.commutator (A07Interactions.numberOp h ν j) (A05.annihilation h η k) =
          -(if (ν, j) = (η, k) then (1 : ℂ) else 0) • A05.annihilation h η k := by
      simpa [A07Interactions.numberOp, A05.creation, A05.annihilation, Ch04.number] using
        (Ch04.number_annihilation_commutator (ν, j) (η, k))
    have hterm (j : Ch01.Band (2 * h)) :
        A02.commutator (A07Interactions.seaSubtractedNumber h ν j)
          (A05.annihilation h η k) =
          -(if (ν, j) = (η, k) then (1 : ℂ) else 0) • A05.annihilation h η k := by
      unfold A07Interactions.seaSubtractedNumber
      simp only [A02.commutator, sub_mul, mul_sub, smul_mul_assoc,
        mul_smul_comm, one_mul, mul_one]
      calc
        _ = A02.commutator (A07Interactions.numberOp h ν j)
              (A05.annihilation h η k) := by
          simp only [A02.commutator]
          noncomm_ring
        _ = _ := hnum j
    simp_rw [hterm]
    by_cases hνη : ν = η
    · subst η
      simp
    · simp [hνη]
  have hfield (η : σ) :
      A02.commutator (A05.chargeObservable h ν) (A05.liftedAnnihilation h b η x) =
        -(if ν = η then (1 : ℂ) else 0) • A05.liftedAnnihilation h b η x := by
    unfold A05.liftedAnnihilation
    simp only [A02.commutator, smul_mul_assoc, mul_smul_comm]
    rw [Finset.mul_sum, Finset.sum_mul, ← smul_sub, ← Finset.sum_sub_distrib]
    simp_rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
    change (A01.normalization (2 * h) : ℂ) •
      ∑ k : Ch01.Band (2 * h),
        Ch06Ext.twistedCharacter (2 * h) (b η) k x •
          A02.commutator (A05.chargeObservable h ν) (A05.annihilation h η k) = _
    simp_rw [hanna]
    simp [Finset.smul_sum, smul_smul]
  have hQadj : LinearMap.adjoint (A05.chargeObservable h ν) = A05.chargeObservable h ν := by
    unfold A05.chargeObservable
    rw [A03.diagonal_adjoint]
    congr 1
    funext S
    simp
  have hQ : star (A05.chargeObservable h ν) = A05.chargeObservable h ν := by
    rw [LinearMap.star_eq_adjoint, hQadj]
  have hadjfield (η : σ) :
      A02.commutator (A05.chargeObservable h ν)
          (LinearMap.adjoint (A05.liftedAnnihilation h b η x)) =
        (if ν = η then (1 : ℂ) else 0) •
          LinearMap.adjoint (A05.liftedAnnihilation h b η x) := by
    have hs := congrArg star (hfield η)
    simp only [A02.commutator, star_sub, star_mul, hQ, star_smul] at hs
    rw [← LinearMap.star_eq_adjoint]
    unfold A02.commutator
    calc
      _ = -(star (A05.liftedAnnihilation h b η x) * A05.chargeObservable h ν -
          A05.chargeObservable h ν * star (A05.liftedAnnihilation h b η x)) := by
        noncomm_ring
      _ = -(star (-(if ν = η then (1 : ℂ) else 0) : ℂ) •
          star (A05.liftedAnnihilation h b η x)) := by rw [hs]
      _ = _ := by simp
  let R := LinearMap.adjoint (A05.liftedAnnihilation h b branches.rightSpecies x)
  let L := A05.liftedAnnihilation h b branches.leftSpecies x
  have hprod : A02.commutator (A05.chargeObservable h ν) (R * L) =
      A02.commutator (A05.chargeObservable h ν) R * L +
        R * A02.commutator (A05.chargeObservable h ν) L := by
    simp only [A02.commutator]
    noncomm_ring
  unfold orderCDW fieldOf
  change A02.commutator (A05.chargeObservable h ν) (R * L) = _
  rw [hprod]
  dsimp [R, L]
  rw [hadjfield, hfield]
  simp only [cdwShift]
  simp only [mul_smul_comm, smul_mul_assoc, Int.cast_sub]
  module

lemma orderSC_charge_commutator (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (ν : σ) :
    A02.commutator (A05.chargeObservable h ν) (orderSC h b branches x) =
      ((scShift branches ν : ℤ) : ℂ) • orderSC h b branches x := by
  let : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
  let : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
  have hdiag : A07Interactions.seaNormalRho h ν 0 =
      ∑ k : Ch01.Band (2 * h), A07Interactions.seaSubtractedNumber h ν k := by
    unfold A07Interactions.seaNormalRho
    have hPairDiag (z : Ch01.Band (2 * h) × Ch01.Band (2 * h))
        (hz : z ∈ A04.validPairs (2 * h) 0) : z.1 = z.2 := by
      have he := (A04.mem_valid_pairs (2 * h) 0 z.1 z.2).mp hz
      apply Subtype.ext
      omega
    apply Finset.sum_bij (fun z _ => z.1)
    · intro z hz
      exact Finset.mem_univ _
    · intro z hZ w hW he
      apply Prod.ext
      · exact he
      · exact (hPairDiag z hZ).symm.trans (he.trans (hPairDiag w hW))
    · intro k hk
      refine ⟨(k, k), ?_, rfl⟩
      apply (A04.mem_valid_pairs (2 * h) 0 k k).mpr
      simp
    · intro z hZ
      rw [hPairDiag z hZ]
      simp only [A07Interactions.seaNormalBilinear,
        A07Interactions.seaSubtractedNumber, A07Interactions.numberOp,
        ite_true, A05.creation, A05.annihilation]
  have hcharge : A05.chargeObservable h ν =
      ∑ k : Ch01.Band (2 * h), A07Interactions.seaSubtractedNumber h ν k :=
    (A07Interactions.sea_normal_rho_zero h ν).symm.trans hdiag
  have hanna (η : σ) (k : Ch01.Band (2 * h)) :
      A02.commutator (A05.chargeObservable h ν) (A05.annihilation h η k) =
        -(if ν = η then (1 : ℂ) else 0) • A05.annihilation h η k := by
    rw [hcharge]
    simp only [A02.commutator, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    change (∑ j : Ch01.Band (2 * h),
        A02.commutator (A07Interactions.seaSubtractedNumber h ν j)
          (A05.annihilation h η k)) = _
    have hnum (j : Ch01.Band (2 * h)) :
        A02.commutator (A07Interactions.numberOp h ν j) (A05.annihilation h η k) =
          -(if (ν, j) = (η, k) then (1 : ℂ) else 0) • A05.annihilation h η k := by
      simpa [A07Interactions.numberOp, A05.creation, A05.annihilation, Ch04.number] using
        (Ch04.number_annihilation_commutator (ν, j) (η, k))
    have hterm (j : Ch01.Band (2 * h)) :
        A02.commutator (A07Interactions.seaSubtractedNumber h ν j)
          (A05.annihilation h η k) =
          -(if (ν, j) = (η, k) then (1 : ℂ) else 0) • A05.annihilation h η k := by
      unfold A07Interactions.seaSubtractedNumber
      simp only [A02.commutator, sub_mul, mul_sub, smul_mul_assoc,
        mul_smul_comm, one_mul, mul_one]
      calc
        _ = A02.commutator (A07Interactions.numberOp h ν j)
              (A05.annihilation h η k) := by
          simp only [A02.commutator]
          noncomm_ring
        _ = _ := hnum j
    simp_rw [hterm]
    by_cases hνη : ν = η
    · subst η
      simp
    · simp [hνη]
  have hfield (η : σ) :
      A02.commutator (A05.chargeObservable h ν) (A05.liftedAnnihilation h b η x) =
        -(if ν = η then (1 : ℂ) else 0) • A05.liftedAnnihilation h b η x := by
    unfold A05.liftedAnnihilation
    simp only [A02.commutator, smul_mul_assoc, mul_smul_comm]
    rw [Finset.mul_sum, Finset.sum_mul, ← smul_sub, ← Finset.sum_sub_distrib]
    simp_rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
    change (A01.normalization (2 * h) : ℂ) •
      ∑ k : Ch01.Band (2 * h),
        Ch06Ext.twistedCharacter (2 * h) (b η) k x •
          A02.commutator (A05.chargeObservable h ν) (A05.annihilation h η k) = _
    simp_rw [hanna]
    simp [Finset.smul_sum, smul_smul]
  let R := A05.liftedAnnihilation h b branches.rightSpecies x
  let L := A05.liftedAnnihilation h b branches.leftSpecies x
  have hprod : A02.commutator (A05.chargeObservable h ν) (R * L) =
      A02.commutator (A05.chargeObservable h ν) R * L +
        R * A02.commutator (A05.chargeObservable h ν) L := by
    simp only [A02.commutator]
    noncomm_ring
  unfold orderSC fieldOf
  change A02.commutator (A05.chargeObservable h ν) (R * L) = _
  rw [hprod]
  dsimp [R, L]
  rw [hfield, hfield]
  simp only [scShift]
  simp only [mul_smul_comm, smul_mul_assoc, Int.cast_neg, Int.cast_sub]
  module

/-- Insert `Pm + (1 - Pm)` *between* the two actual field factors. -/
lemma ambient_cdw_residual (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ)
    (Ks Km Kt : ℕ) :
    Ch14.projection h (cdwTarget branches Ns) Kt * orderCDW h b branches x *
        Ch14.projection h Ns Ks =
      Ch14.projection h (cdwTarget branches Ns) Kt *
        LinearMap.adjoint (fieldOf h b branches.rightSpecies x) *
        Ch14.projection h (Ch13.lowerCharge Ns branches.leftSpecies) Km *
        fieldOf h b branches.leftSpecies x * Ch14.projection h Ns Ks +
      Ch14.projection h (cdwTarget branches Ns) Kt *
        cdwResidualOp h b branches x Ns Km * Ch14.projection h Ns Ks := by
  simp only [orderCDW, cdwResidualOp]
  noncomm_ring

lemma ambient_sc_residual (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ)
    (Ks Km Kt : ℕ) :
    Ch14.projection h (scTarget branches Ns) Kt * orderSC h b branches x *
        Ch14.projection h Ns Ks =
      Ch14.projection h (scTarget branches Ns) Kt *
        fieldOf h b branches.rightSpecies x *
        Ch14.projection h (Ch13.lowerCharge Ns branches.leftSpecies) Km *
        fieldOf h b branches.leftSpecies x * Ch14.projection h Ns Ks +
      Ch14.projection h (scTarget branches Ns) Kt *
        scResidualOp h b branches x Ns Km * Ch14.projection h Ns Ks := by
  simp only [orderSC, scResidualOp]
  noncomm_ring

/-- Source → intermediate → CDW target, plus a typed retained residual. -/
lemma projected_cdw_residual (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ)
    (Ks Km Kt : ℕ) :
    Ch14.projectedMap h Ns (cdwTarget branches Ns) Ks Kt (orderCDW h b branches x) =
      (Ch14.projectedMap h (Ch13.lowerCharge Ns branches.leftSpecies)
          (cdwTarget branches Ns) Km Kt
          (LinearMap.adjoint (fieldOf h b branches.rightSpecies x))).comp
        (Ch14.projectedMap h Ns (Ch13.lowerCharge Ns branches.leftSpecies) Ks Km
          (fieldOf h b branches.leftSpecies x)) +
      Ch14.projectedMap h Ns (cdwTarget branches Ns) Ks Kt
        (cdwResidualOp h b branches x Ns Km) := by
  let : DecidableEq (A05.Mode σ h) := fun a b => A05.localModeDecidableEq h a b
  ext v : 1
  apply Subtype.ext
  have hv : Ch14.projection h Ns Ks v.val = v.val :=
    (A03.projection_fixed_iff _ _).mpr v.property
  have heq := congrArg (fun A : A05.Operators σ h => A v.val)
    (ambient_cdw_residual h b branches x Ns Ks Km Kt)
  rw [Ch14.projected_map_apply]
  simpa only [LinearMap.add_apply, LinearMap.comp_apply,
    Ch14.projected_map_apply, Module.End.mul_apply, Submodule.coe_add, hv] using heq

lemma projected_sc_residual (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ)
    (Ks Km Kt : ℕ) :
    Ch14.projectedMap h Ns (scTarget branches Ns) Ks Kt (orderSC h b branches x) =
      (Ch14.projectedMap h (Ch13.lowerCharge Ns branches.leftSpecies)
          (scTarget branches Ns) Km Kt
          (fieldOf h b branches.rightSpecies x)).comp
        (Ch14.projectedMap h Ns (Ch13.lowerCharge Ns branches.leftSpecies) Ks Km
          (fieldOf h b branches.leftSpecies x)) +
      Ch14.projectedMap h Ns (scTarget branches Ns) Ks Kt
        (scResidualOp h b branches x Ns Km) := by
  let : DecidableEq (A05.Mode σ h) := fun a b => A05.localModeDecidableEq h a b
  ext v : 1
  apply Subtype.ext
  have hv : Ch14.projection h Ns Ks v.val = v.val :=
    (A03.projection_fixed_iff _ _).mpr v.property
  have heq := congrArg (fun A : A05.Operators σ h => A v.val)
    (ambient_sc_residual h b branches x Ns Ks Km Kt)
  rw [Ch14.projected_map_apply]
  simpa only [LinearMap.add_apply, LinearMap.comp_apply,
    Ch14.projected_map_apply, Module.End.mul_apply, Submodule.coe_add, hv] using heq

/-- The CDW creation factor is the reversed-carrier adjoint, not a label. -/
lemma cdw_creation_factor_eq_budgetAdjoint (h : ℕ)
    (b : σ → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches σ) (x : ℤ) (Ns : σ → ℤ)
    (Km Kt : ℕ) :
    Ch14.projectedMap h (Ch13.lowerCharge Ns branches.leftSpecies)
        (cdwTarget branches Ns) Km Kt
        (LinearMap.adjoint (fieldOf h b branches.rightSpecies x)) =
      Ch14.budgetAdjoint h (cdwTarget branches Ns)
        (Ch13.lowerCharge Ns branches.leftSpecies) Kt Km
        (Ch14.projectedMap h (cdwTarget branches Ns)
          (Ch13.lowerCharge Ns branches.leftSpecies) Kt Km
          (fieldOf h b branches.rightSpecies x)) := by
  rw [← Ch14.projected_map_adjoint]

/-- Source-charge phase and the *ordered* Klein factors, in the periodic gauge. -/
noncomputable def cdwChargeCoeff (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (x : ℤ) : ℂ :=
  A01.integerCharacter (A01.canonicalRoot (2 * h))
      (Ns branches.leftSpecies - Ns branches.rightSpecies - 1) x *
    (Ch13.kleinPhase h Ns branches.leftSpecies *
      Ch13.kleinPhase h (cdwTarget branches Ns) branches.rightSpecies)

noncomputable def scChargeCoeff (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (x : ℤ) : ℂ :=
  A01.integerCharacter (A01.canonicalRoot (2 * h))
      (Ns branches.rightSpecies + Ns branches.leftSpecies) x *
    (Ch13.kleinPhase h Ns branches.leftSpecies *
      Ch13.kleinPhase h (Ch13.lowerCharge Ns branches.leftSpecies)
        branches.rightSpecies)

section CDWGroundCoeffProofHelpers

noncomputable local instance localModeLinearOrderCDW (h : ℕ) :
    LinearOrder (A05.Mode σ h) := A05.speciesOrder h
noncomputable local instance localModeLTCDW (h : ℕ) :
    LT (A05.Mode σ h) := (A05.speciesOrder h).toLT
noncomputable local instance localModeLECDW (h : ℕ) :
    LE (A05.Mode σ h) := (A05.speciesOrder h).toLE
noncomputable local instance localModeDecidableEqCDW (h : ℕ) :
    DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq

private lemma sum_single_pairCDW {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [AddCommMonoid R]
    (a₀ : α) (b₀ : β) (f : α → β → R) :
    ∑ b : β, ∑ a : α, (if (a = a₀ ∧ b = b₀) then f a b else 0) = f a₀ b₀ := by
  classical
  rw [Finset.sum_eq_single b₀]
  · rw [Finset.sum_eq_single a₀]
    · simp
    · intro a ha hne
      simp [hne]
    · intro hnot
      exact (hnot (Finset.mem_univ a₀)).elim
  · intro b hb hne
    apply Finset.sum_eq_zero
    intro a ha
    simp [hne]
  · intro hnot
    exact (hnot (Finset.mem_univ b₀)).elim



private lemma ground_memCDWX (h : ℕ) (Ns : σ → ℤ) (ν : σ) (k : Ch01.Band (2*h)) :
    (ν,k) ∈ A05.groundConfiguration h Ns ↔ k.val ≤ Ns ν := by
  simp only [A05.groundConfiguration, A05.jointConfiguration,
    Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Ch07.groundConfiguration, Finset.mem_filter]
  aesop

private lemma cdw_config_forwardX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
    (heq : insert (branches.rightSpecies,p)
      ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) =
        A05.groundConfiguration h (cdwTarget branches Ns))
    (hk : (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns)
    (hp : (branches.rightSpecies,p) ∉
      (A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) :
    k.val = Ns branches.leftSpecies ∧ p.val = Ns branches.rightSpecies + 1 := by
  have hleft_not : (branches.leftSpecies,k) ∉
      A05.groundConfiguration h (cdwTarget branches Ns) := by
    rw [← heq]
    simp only [Finset.mem_insert, Prod.mk.injEq]
    have hne : branches.leftSpecies ≠ branches.rightSpecies := branches.distinct.symm
    simp [hne, Finset.mem_erase, hk]
  have hleft := (ground_memCDWX h (cdwTarget branches Ns)
      branches.leftSpecies k).not.mp hleft_not
  rw [cdwTarget_apply] at hleft
  simp [cdwShift] at hleft
  have hkval := (ground_memCDWX h Ns branches.leftSpecies k).mp hk
  have hpleft : (branches.rightSpecies,p) ∈
      A05.groundConfiguration h (cdwTarget branches Ns) := by
    rw [← heq]
    simp
  have hpval := (ground_memCDWX h (cdwTarget branches Ns)
      branches.rightSpecies p).mp hpleft
  rw [cdwTarget_apply] at hpval
  simp [cdwShift] at hpval
  have hnotSrc : (branches.rightSpecies,p) ∉
      A05.groundConfiguration h Ns := by
    intro hpSrc
    apply hp
    simp [Finset.mem_erase, hpSrc, branches.distinct]
  have hpgt : Ns branches.rightSpecies < p.val := by
    have hnr := (ground_memCDWX h Ns branches.rightSpecies p).not.mp hnotSrc
    omega
  omega

private lemma cdw_config_reverseX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
    (hkval : k.val = Ns branches.leftSpecies)
    (hpval : p.val = Ns branches.rightSpecies + 1) :
    insert (branches.rightSpecies,p)
      ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) =
        A05.groundConfiguration h (cdwTarget branches Ns) := by
  ext z
  obtain ⟨η,l⟩ := z
  have hne : branches.leftSpecies ≠ branches.rightSpecies := branches.distinct.symm
  have htL : cdwTarget branches Ns branches.leftSpecies =
      Ns branches.leftSpecies - 1 := by
    rw [cdwTarget_apply]; simp [cdwShift, hne]; ring
  have htR : cdwTarget branches Ns branches.rightSpecies =
      Ns branches.rightSpecies + 1 := by
    rw [cdwTarget_apply]; simp [cdwShift, branches.distinct]
  have hmemS : (η,l) ∈ A05.groundConfiguration h Ns ↔ l.val ≤ Ns η :=
    ground_memCDWX h Ns η l
  have hmemT : (η,l) ∈ A05.groundConfiguration h (cdwTarget branches Ns) ↔
      l.val ≤ cdwTarget branches Ns η := ground_memCDWX h _ η l
  rw [Finset.mem_insert, Finset.mem_erase, hmemS, hmemT]
  by_cases hηL : η = branches.leftSpecies
  · subst η
    rw [htL]
    have hneq : l ≠ k ↔ l.val ≠ Ns branches.leftSpecies := by
      simp [Subtype.ext_iff, hkval]
    simp only [Prod.mk.injEq]
    simp [hneq, hne]
    omega
  · by_cases hηR : η = branches.rightSpecies
    · subst η
      rw [htR]
      have hpEq : l = p ↔ l.val = Ns branches.rightSpecies + 1 := by
        simp [Subtype.ext_iff, hpval]
      simp only [Prod.mk.injEq]
      simp [hpEq, branches.distinct]
      omega
    · have htarget : cdwTarget branches Ns η = Ns η := by
        rw [cdwTarget_apply]; simp [cdwShift, hηL, hηR]
      rw [htarget]
      simp [hηL, hηR]

private lemma cdw_pair_support_iffX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
    (hk : (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns)
    (hp : (branches.rightSpecies,p) ∈ A05.groundConfiguration h
      (cdwTarget branches Ns)) :
    (A05.groundConfiguration h (cdwTarget branches Ns)).erase
        (branches.rightSpecies,p) =
      (A05.groundConfiguration h Ns).erase (branches.leftSpecies,k) ↔
        k.val = Ns branches.leftSpecies ∧
          p.val = Ns branches.rightSpecies + 1 := by
  constructor
  · intro he
    have hpErase : (branches.rightSpecies,p) ∉
        (A05.groundConfiguration h Ns).erase (branches.leftSpecies,k) := by
      rw [← he]
      simp
    have heq : insert (branches.rightSpecies,p)
        ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) =
        A05.groundConfiguration h (cdwTarget branches Ns) := by
      rw [← he]
      exact Finset.insert_erase hp
    exact cdw_config_forwardX h branches Ns k p heq hk hpErase
  · rintro ⟨hkval,hpval⟩
    have heq := cdw_config_reverseX h branches Ns k p hkval hpval
    have hpErase : (branches.rightSpecies,p) ∉
        (A05.groundConfiguration h Ns).erase (branches.leftSpecies,k) := by
      have hpSrc : (branches.rightSpecies,p) ∉ A05.groundConfiguration h Ns := by
        intro hpSrc
        have hpvalSrc := (ground_memCDWX h Ns branches.rightSpecies p).mp hpSrc
        have hpvalT := (ground_memCDWX h (cdwTarget branches Ns)
          branches.rightSpecies p).mp hp
        rw [cdwTarget_apply] at hpvalT
        simp [cdwShift, branches.distinct] at hpvalT
        omega
      exact fun hmem => hpSrc (Finset.mem_of_mem_erase hmem)
    have hErase : (A05.groundConfiguration h (cdwTarget branches Ns)).erase
        (branches.rightSpecies,p) =
        ((insert (branches.rightSpecies,p)
          ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k))).erase
            (branches.rightSpecies,p)) := by rw [heq]
    rw [hErase]
    simp [hpErase]

private lemma cdwTopWitnessX (h : ℕ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (hR : Ns branches.rightSpecies < (h : ℤ))
    (hL : -(h : ℤ) < Ns branches.leftSpecies) :
    ∃ k p : Ch01.Band (2*h),
      k.val = Ns branches.leftSpecies ∧
      p.val = Ns branches.rightSpecies + 1 ∧
      (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns ∧
      (branches.rightSpecies,p) ∈
        A05.groundConfiguration h (cdwTarget branches Ns) := by
  obtain ⟨hllo,hlu⟩ := hN branches.leftSpecies
  obtain ⟨hrlo,hru⟩ := hN branches.rightSpecies
  let k : Ch01.Band (2*h) := ⟨Ns branches.leftSpecies, by
    unfold Ch01.inBandPredicate
    push_cast
    constructor <;> omega⟩
  let p : Ch01.Band (2*h) := ⟨Ns branches.rightSpecies + 1, by
    unfold Ch01.inBandPredicate
    push_cast
    constructor <;> omega⟩
  refine ⟨k,p,rfl,rfl,?_,?_⟩
  · apply (ground_memCDWX h Ns branches.leftSpecies k).2
    dsimp [k]
    omega
  · apply (ground_memCDWX h (cdwTarget branches Ns) branches.rightSpecies p).2
    rw [cdwTarget_apply]
    simp [cdwShift, branches.distinct]
    dsimp [p]
    omega

private lemma ground_top_signX (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (ν : σ)
    (hν : -(h : ℤ)+1 ≤ Ns ν) (k : Ch01.Band (2*h))
    (hk : k.val = Ns ν) :
    Ch04.fermionSign (ν,k) (A05.groundConfiguration h Ns) =
      Ch13.kleinPhase h Ns ν := by
  have hlow : Ch07.admissible h (Ns ν-1) := by
    obtain ⟨hl, hu⟩ := hN ν
    constructor <;> omega
  have hcomp (η : σ) :
      Ch07.speciesConfiguration h (A05.groundConfiguration h Ns) η =
        Ch07.groundConfiguration h (Ns η) :=
    A05.species_joint_configuration h _ η
  have ht : (Ch07.groundConfiguration h (Ns ν)).filter (· < k) =
      Ch07.groundConfiguration h (Ns ν-1) := by
    ext l
    simp only [Ch07.groundConfiguration, Finset.mem_filter, Finset.mem_univ, true_and]
    change (l.val ≤ Ns ν ∧ l.val < k.val) ↔ l.val ≤ Ns ν-1
    rw [hk]
    omega
  have hc : ((Ch04.precedingCount (ν,k) (A05.groundConfiguration h Ns) : ℕ) : ℤ) =
      Ch13.phaseExponent h Ns ν := by
    rw [A05.preceding_count_split]
    simp only [hcomp, Nat.cast_add, Nat.cast_sum]
    simp_rw [Ch07.ground_configuration_card h hh _ (hN _)]
    unfold Ch04.precedingCount
    rw [ht, Ch07.ground_configuration_card h hh _ hlow]
    simp only [Ch13.phaseExponent]
    ring
  unfold Ch04.fermionSign Ch13.kleinPhase
  rw [← zpow_natCast, hc]

private lemma cdw_pair_condition_iffX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k₀ p₀ k p : Ch01.Band (2*h))
    (hk₀ : (branches.leftSpecies,k₀) ∈ A05.groundConfiguration h Ns)
    (hp₀ : (branches.rightSpecies,p₀) ∈
      A05.groundConfiguration h (cdwTarget branches Ns))
    (hkval : k₀.val = Ns branches.leftSpecies)
    (hpval : p₀.val = Ns branches.rightSpecies + 1) :
    ((branches.rightSpecies,p) ∈ A05.groundConfiguration h
        (cdwTarget branches Ns) ∧
      (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns ∧
      (A05.groundConfiguration h (cdwTarget branches Ns)).erase
        (branches.rightSpecies,p) =
        (A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) ↔
      k = k₀ ∧ p = p₀ := by
  constructor
  · rintro ⟨hp,hk,he⟩
    have hval := (cdw_pair_support_iffX h branches Ns k p hk hp).mp he
    constructor
    · apply Subtype.ext
      exact hval.1.trans hkval.symm
    · apply Subtype.ext
      exact hval.2.trans hpval.symm
  · intro heq
    rcases heq with ⟨hkEq,hpEq⟩
    rw [hkEq,hpEq]
    exact ⟨hp₀,hk₀,(cdw_pair_support_iffX h branches Ns k₀ p₀ hk₀ hp₀).mpr
      ⟨hkval,hpval⟩⟩

private lemma fieldKetCDWX (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (S : A05.Occupation σ h) (ν : σ) (x : ℤ) :
    A05.liftedAnnihilation h b ν x (A02.ket S) =
      (A01.normalization (2*h) : ℂ) •
        ∑ k : Ch01.Band (2*h),
          if (ν,k) ∈ S then
            (Ch06Ext.twistedCharacter (2*h) (b ν) k x *
              Ch04.fermionSign (ν,k) S) • A02.ket (S.erase (ν,k))
          else 0 := by
  simp only [A05.liftedAnnihilation, LinearMap.smul_apply,
    LinearMap.sum_apply, A05.annihilation, Ch04.annihilation_ket]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · simp only [smul_smul]
  · simp

private lemma hole_pair_innerX {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (S T : A02.Occupation ι) (a b : ℂ) :
    inner ℂ (if i ∈ T then a • A02.ket (T.erase i) else 0)
      (if j ∈ S then b • A02.ket (S.erase j) else 0) =
    if i ∈ T ∧ j ∈ S ∧ T.erase i = S.erase j then
      star a * b else 0 := by
  by_cases hi : i ∈ T
  · by_cases hj : j ∈ S
    · by_cases he : T.erase i = S.erase j
      · simp [hi, hj, he, inner_smul_left, inner_smul_right, A02.ket_norm]
        ring
      · simp [hi, hj, he, inner_smul_left, inner_smul_right, A02.ket_inner]
    · simp [hi, hj]
  · simp [hi]

private lemma inner_sum_rightCDWX {ι E : Type*} [Fintype ι]
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (y : E) (f : ι → E) :
    inner ℂ y (∑ i, f i) = ∑ i, inner ℂ y (f i) := by
  rw [inner_sum (s := Finset.univ)]

private lemma inner_sum_leftCDWX {ι E : Type*} [Fintype ι]
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : ι → E) (y : E) :
    inner ℂ (∑ i, f i) y = ∑ i, inner ℂ (f i) y := by
  rw [← inner_conj_symm]
  rw [inner_sum (s := Finset.univ)]
  change star (∑ i, inner ℂ y (f i)) = ∑ i, inner ℂ (f i) y
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact inner_conj_symm (f i) y

private lemma scalar_top_pair (h : ℕ) (hh : 0 < h) (Ns T : σ → ℤ)
    (l r : σ) (x : ℤ) (hT : T r = Ns r + 1) :
    star ((A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h T r *
      A01.integerCharacter (A01.canonicalRoot (2*h)) (T r) x) *
      ((A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h Ns l *
      A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns l) x) =
      (((2*h : ℕ) : ℂ)⁻¹) *
        (A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns l - Ns r - 1) x *
          (Ch13.kleinPhase h Ns l * Ch13.kleinPhase h T r)) := by
  let _ : NeZero (2*h) := ⟨by omega⟩
  have hnorm := A01.normalization_square_complex (2*h)
  have hroot := A01.canonical_root_primitive (2*h)
  simp only [star_mul, A01.normalization_conj]
  rw [show star (Ch13.kleinPhase h T r) = Ch13.kleinPhase h T r by
    simp [Ch13.kleinPhase]]
  rw [A01.complex_character_conj (2*h) (A01.canonicalRoot (2*h)) hroot (T r) x]
  simp_rw [hT]
  simp only [A01.integerCharacter]
  let z := A01.canonicalRoot (2*h)
  have hpow : z ^ (-(Ns r + 1) * x) * z ^ (Ns l * x) =
      z ^ ((Ns l - Ns r - 1) * x) := by
    rw [← zpow_add₀ (A01.root_ne_zero (2*h) z hroot)]
    congr 1
    ring
  have hprod :
      z ^ (-(Ns r + 1) * x) * (Ch13.kleinPhase h T r *
        (A01.normalization (2*h) : ℂ)) *
        ((A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h Ns l *
          z ^ (Ns l * x)) =
      (A01.normalization (2*h) : ℂ)^2 *
        (Ch13.kleinPhase h Ns l * Ch13.kleinPhase h T r) *
        (z ^ (-(Ns r + 1) * x) * z ^ (Ns l * x)) := by ring
  rw [hprod, hpow]
  have hn : (A01.normalization (2*h) : ℂ)^2 = ((2*h : ℕ) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_right hnorm
  rw [hn]
  ring

omit [Fintype σ] in
private lemma cdw_admissibleX (h : ℕ) (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (hR : Ns branches.rightSpecies < (h : ℤ))
    (hL : -(h : ℤ) < Ns branches.leftSpecies) :
    A05.admissible h (cdwTarget branches Ns) := by
  intro ν
  rw [cdwTarget_apply]
  by_cases hνR : ν = branches.rightSpecies
  · subst ν
    obtain ⟨hlo,hhi⟩ := hN branches.rightSpecies
    have hne : branches.rightSpecies ≠ branches.leftSpecies := branches.distinct
    simp [cdwShift, hne]
    constructor <;> omega
  · by_cases hνL : ν = branches.leftSpecies
    · subst ν
      obtain ⟨hlo,hhi⟩ := hN branches.leftSpecies
      have hne : branches.leftSpecies ≠ branches.rightSpecies := branches.distinct.symm
      simp [cdwShift, hne]
      constructor <;> omega
    · obtain ⟨hlo,hhi⟩ := hN ν
      simp [cdwShift, hνR, hνL]
      constructor <;> omega

end CDWGroundCoeffProofHelpers

/-- Matrix coefficient of actual CAR fields; not a bosonized-vertex identity. -/
lemma orderCDW_ground_coeff (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hR : Ns branches.rightSpecies < (h : ℤ))
    (hL : -(h : ℤ) < Ns branches.leftSpecies) (x : ℤ) :
    inner ℂ (A05.groundKet h (cdwTarget branches Ns))
      (orderCDW h (fun _ => Ch06Ext.periodicTwist (2 * h)) branches x
        (A05.groundKet h Ns)) =
      (((2 * h : ℕ) : ℂ)⁻¹) * cdwChargeCoeff h branches Ns x := by
  let _ : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
  let _ : LT (A05.Mode σ h) := (A05.speciesOrder h).toLT
  let _ : LE (A05.Mode σ h) := (A05.speciesOrder h).toLE
  let _ : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
  let T := cdwTarget branches Ns
  let b : σ → Ch06Ext.BoundaryTwist (2*h) := fun _ => Ch06Ext.periodicTwist (2*h)
  have hNT : A05.admissible h T := by
    exact cdw_admissibleX h branches Ns hN hR hL
  obtain ⟨k₀,p₀,hkval,hpval,hk₀,hp₀⟩ := cdwTopWitnessX h branches Ns hN hR hL
  have hLtop : -(h : ℤ)+1 ≤ Ns branches.leftSpecies := by omega
  have hTtop : T branches.rightSpecies = Ns branches.rightSpecies + 1 := by
    dsimp [T]
    rw [cdwTarget_apply]
    simp [cdwShift, branches.distinct]
  have hRtop : -(h : ℤ)+1 ≤ T branches.rightSpecies := by
    rw [hTtop]
    obtain ⟨hl,hu⟩ := hN branches.rightSpecies
    omega
  have hsignS := ground_top_signX h hh Ns hN branches.leftSpecies hLtop k₀ hkval
  have hsignT := ground_top_signX h hh T hNT branches.rightSpecies hRtop p₀
    (hpval.trans hTtop.symm)
  change inner ℂ (A05.groundKet h T)
    ((LinearMap.adjoint (A05.liftedAnnihilation h b branches.rightSpecies x))
      (A05.liftedAnnihilation h b branches.leftSpecies x (A05.groundKet h Ns))) = _
  rw [LinearMap.adjoint_inner_right (𝕜 := ℂ)]
  change inner ℂ
    (A05.liftedAnnihilation h b branches.rightSpecies x (A02.ket (A05.groundConfiguration h T)))
    (A05.liftedAnnihilation h b branches.leftSpecies x (A02.ket (A05.groundConfiguration h Ns))) = _
  rw [fieldKetCDWX h b (A05.groundConfiguration h T) branches.rightSpecies x,
    fieldKetCDWX h b (A05.groundConfiguration h Ns) branches.leftSpecies x]
  rw [inner_smul_left, inner_smul_right]
  simp_rw [inner_sum_leftCDWX]
  simp_rw [inner_sum_rightCDWX]
  simp_rw [hole_pair_innerX (ι := A05.Mode σ h)]
  dsimp only [T]
  simp_rw [cdw_pair_condition_iffX h branches Ns k₀ p₀ _ _ hk₀ hp₀ hkval hpval]
  rw [sum_single_pairCDW k₀ p₀ (fun k p =>
    star (Ch06Ext.twistedCharacter (2*h) (b branches.rightSpecies) p x *
      Ch04.fermionSign (branches.rightSpecies,p) (A05.groundConfiguration h T)) *
    (Ch06Ext.twistedCharacter (2*h) (b branches.leftSpecies) k x *
      Ch04.fermionSign (branches.leftSpecies,k) (A05.groundConfiguration h Ns)))]
  rw [hsignT, hsignS]
  unfold cdwChargeCoeff
  have hcharT : Ch06Ext.twistedCharacter (2*h) (b branches.rightSpecies) p₀ x =
      A01.integerCharacter (A01.canonicalRoot (2*h)) (T branches.rightSpecies) x := by
    simp [Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, b, Ch06Ext.periodicTwist,
      hpval, hTtop]
  have hcharS : Ch06Ext.twistedCharacter (2*h) (b branches.leftSpecies) k₀ x =
      A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns branches.leftSpecies) x := by
    simp [Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, b, Ch06Ext.periodicTwist,
      hkval]
  rw [hcharT, hcharS, ← scalar_top_pair h hh Ns T branches.leftSpecies
    branches.rightSpecies x hTtop]
  simp only [star_mul]
  rw [show star (Ch13.kleinPhase h T branches.rightSpecies) =
      Ch13.kleinPhase h T branches.rightSpecies by simp [Ch13.kleinPhase]]
  have hnconj1 : star (A01.normalization (2*h) : ℂ) =
      (A01.normalization (2*h) : ℂ) := A01.normalization_conj (2*h)
  have hnconj2 : star (A01.normalization (h*2) : ℂ) =
      (A01.normalization (h*2) : ℂ) := A01.normalization_conj (h*2)
  simp
  ring

section GroundCoeffProofHelpers

noncomputable local instance localModeLinearOrder (h : ℕ) :
    LinearOrder (A05.Mode σ h) := A05.speciesOrder h
noncomputable local instance localModeLT (h : ℕ) :
    LT (A05.Mode σ h) := (A05.speciesOrder h).toLT
noncomputable local instance localModeLE (h : ℕ) :
    LE (A05.Mode σ h) := (A05.speciesOrder h).toLE
noncomputable local instance localModeDecidableEq (h : ℕ) :
    DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq

private lemma ground_memX (h : ℕ) (Ns : σ → ℤ) (ν : σ)
    (k : Ch01.Band (2*h)) :
    (ν,k) ∈ A05.groundConfiguration h Ns ↔ k.val ≤ Ns ν := by
  simp only [A05.groundConfiguration, A05.jointConfiguration,
    Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Ch07.groundConfiguration, Finset.mem_filter]
  aesop

private lemma sc_pair_forwardX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
    (heq : ((A05.groundConfiguration h Ns).erase
        (branches.leftSpecies,k)).erase (branches.rightSpecies,p) =
      A05.groundConfiguration h (scTarget branches Ns))
    (hk : (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns)
    (hp : (branches.rightSpecies,p) ∈ A05.groundConfiguration h Ns) :
    k.val = Ns branches.leftSpecies ∧ p.val = Ns branches.rightSpecies := by
  have hLnot : (branches.leftSpecies,k) ∉
      A05.groundConfiguration h (scTarget branches Ns) := by
    rw [← heq]
    simp
  have hRnot : (branches.rightSpecies,p) ∉
      A05.groundConfiguration h (scTarget branches Ns) := by
    rw [← heq]
    simp
  have hLlo := (ground_memX h Ns branches.leftSpecies k).mp hk
  have hLhi := (ground_memX h (scTarget branches Ns)
      branches.leftSpecies k).not.mp hLnot
  have hRlo := (ground_memX h Ns branches.rightSpecies p).mp hp
  have hRhi := (ground_memX h (scTarget branches Ns)
      branches.rightSpecies p).not.mp hRnot
  rw [scTarget_apply] at hLhi hRhi
  have hne : branches.leftSpecies ≠ branches.rightSpecies :=
    branches.distinct.symm
  simp [scShift, hne, branches.distinct] at hLhi hRhi
  omega

private lemma sc_pair_reverseX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
    (hkval : k.val = Ns branches.leftSpecies)
    (hpval : p.val = Ns branches.rightSpecies) :
    ((A05.groundConfiguration h Ns).erase
        (branches.leftSpecies,k)).erase (branches.rightSpecies,p) =
      A05.groundConfiguration h (scTarget branches Ns) := by
  ext z
  obtain ⟨η,l⟩ := z
  have hne : branches.leftSpecies ≠ branches.rightSpecies :=
    branches.distinct.symm
  rw [Finset.mem_erase, Finset.mem_erase]
  rw [ground_memX h Ns η l, ground_memX h (scTarget branches Ns) η l]
  rw [scTarget_apply]
  by_cases hL : η = branches.leftSpecies
  · subst η
    have hkEq : l = k ↔ l.val = Ns branches.leftSpecies := by
      constructor
      · intro e
        rw [e, hkval]
      · intro e
        apply Subtype.ext
        exact e.trans hkval.symm
    simp [scShift, hne, hkEq]
    omega
  · by_cases hR : η = branches.rightSpecies
    · subst η
      have hpEq : l = p ↔ l.val = Ns branches.rightSpecies := by
        constructor
        · intro e
          rw [e, hpval]
        · intro e
          apply Subtype.ext
          exact e.trans hpval.symm
      simp [scShift, branches.distinct, hpEq]
      omega
    · simp [scShift, hL, hR]

private lemma sc_pair_support_iffX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
    (hk : (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns)
    (hp : (branches.rightSpecies,p) ∈ A05.groundConfiguration h Ns) :
    ((A05.groundConfiguration h Ns).erase
        (branches.leftSpecies,k)).erase (branches.rightSpecies,p) =
      A05.groundConfiguration h (scTarget branches Ns) ↔
        k.val = Ns branches.leftSpecies ∧
          p.val = Ns branches.rightSpecies := by
  constructor
  · intro heq
    exact sc_pair_forwardX h branches Ns k p heq hk hp
  · rintro ⟨hkval,hpval⟩
    exact sc_pair_reverseX h branches Ns k p hkval hpval

private lemma sc_ground_pair_cond_iffX (h : ℕ) (branches : A06.Branches σ)
    (Ns : σ → ℤ) (k p : Ch01.Band (2*h))
    (hk : (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns)
    (hp : (branches.rightSpecies,p) ∈ A05.groundConfiguration h Ns) :
    ((branches.rightSpecies,p) ∈ A05.groundConfiguration h Ns ∧
      (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns ∧
      (branches.rightSpecies = branches.leftSpecies → p ≠ k) ∧
      A05.groundConfiguration h (scTarget branches Ns) =
        Finset.erase (Finset.erase (A05.groundConfiguration h Ns)
          (branches.leftSpecies,k)) (branches.rightSpecies,p)) ↔
      k.val = Ns branches.leftSpecies ∧ p.val = Ns branches.rightSpecies := by
  constructor
  · rintro ⟨_,_,_,heq⟩
    exact (sc_pair_support_iffX h branches Ns k p hk hp).mp heq.symm
  · rintro ⟨hkval,hpval⟩
    refine ⟨hp,hk,?_,?_⟩
    · intro heq
      exact (branches.distinct heq).elim
    · have heq := (sc_pair_support_iffX h branches Ns k p hk hp).mpr
        ⟨hkval,hpval⟩
      exact heq.symm


private lemma fieldKetX (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (S : A05.Occupation σ h) (ν : σ) (x : ℤ) :
    A05.liftedAnnihilation h b ν x (A02.ket S) =
      (A01.normalization (2*h) : ℂ) •
        ∑ k : Ch01.Band (2*h),
          if (ν,k) ∈ S then
            (Ch06Ext.twistedCharacter (2*h) (b ν) k x *
              Ch04.fermionSign (ν,k) S) • A02.ket (S.erase (ν,k))
          else 0 := by
  simp only [A05.liftedAnnihilation, LinearMap.smul_apply,
    LinearMap.sum_apply, A05.annihilation, Ch04.annihilation_ket]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · simp only [smul_smul]
  · simp


private lemma scalar_top_pair_sc (h : ℕ) (hh : 0 < h) (Ns T : σ → ℤ)
    (l r : σ) (x : ℤ) (hT : T r = Ns r) :
    ((A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h T r *
      A01.integerCharacter (A01.canonicalRoot (2*h)) (T r) x) *
      ((A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h Ns l *
      A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns l) x) =
      (((2*h : ℕ) : ℂ)⁻¹) *
        (A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns r + Ns l) x *
          (Ch13.kleinPhase h Ns l * Ch13.kleinPhase h T r)) := by
  let _ : NeZero (2*h) := ⟨by omega⟩
  have hnorm := A01.normalization_square_complex (2*h)
  have hroot := A01.canonical_root_primitive (2*h)
  simp_rw [hT]
  simp only [A01.integerCharacter]
  let z := A01.canonicalRoot (2*h)
  have hpow : z ^ (Ns r * x) * z ^ (Ns l * x) = z ^ ((Ns r + Ns l) * x) := by
    rw [← zpow_add₀ (A01.root_ne_zero (2*h) z hroot)]
    congr 1
    ring
  have hprod :
      (A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h T r * z ^ (Ns r * x) *
        ((A01.normalization (2*h) : ℂ) * Ch13.kleinPhase h Ns l * z ^ (Ns l * x)) =
      (A01.normalization (2*h) : ℂ)^2 *
        (Ch13.kleinPhase h Ns l * Ch13.kleinPhase h T r) *
        (z ^ (Ns r * x) * z ^ (Ns l * x)) := by ring
  rw [hprod, hpow]
  have hn : (A01.normalization (2*h) : ℂ)^2 = ((2*h : ℕ) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_right hnorm
  rw [hn]
  ring

private lemma sc_pair_sign_kleinX (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hR : -(h : ℤ) < Ns branches.rightSpecies)
    (hL : -(h : ℤ) < Ns branches.leftSpecies)
    (k p : Ch01.Band (2*h)) (hk : k.val = Ns branches.leftSpecies)
    (hp : p.val = Ns branches.rightSpecies) :
    Ch04.fermionSign (branches.rightSpecies,p)
      ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) *
      Ch04.fermionSign (branches.leftSpecies,k)
        (A05.groundConfiguration h Ns) =
      Ch13.kleinPhase h Ns branches.leftSpecies *
        Ch13.kleinPhase h (Ch13.lowerCharge Ns branches.leftSpecies)
          branches.rightSpecies := by
  have hNsL := hN branches.leftSpecies
  have hNsR := hN branches.rightSpecies
  have hNsLlow : -(h : ℤ) + 1 ≤ Ns branches.leftSpecies := by omega
  have hNsRlow : -(h : ℤ) + 1 ≤ Ns branches.rightSpecies := by omega
  have hNlower : A05.admissible h (Ch13.lowerCharge Ns branches.leftSpecies) := by
    intro η
    by_cases he : η = branches.leftSpecies
    · subst η
      simp only [Ch13.lowerCharge, Function.update_self]
      constructor
      · have hlo := hL
        omega
      · have hu := hNsL.2
        omega
    · have hη := hN η
      simp only [Ch13.lowerCharge, Function.update_of_ne he]
      exact hη
  have hRlower : -(h : ℤ) + 1 ≤
      Ch13.lowerCharge Ns branches.leftSpecies branches.rightSpecies := by
    rw [Ch13.lowerCharge, Function.update_of_ne branches.distinct]
    exact hNsRlow
  have hleft := Ch13.ground_top_annihilation h hh Ns hN
    branches.leftSpecies hNsLlow k hk
  have hright := Ch13.ground_top_annihilation h hh
    (Ch13.lowerCharge Ns branches.leftSpecies) hNlower
    branches.rightSpecies hRlower p (by
      rw [Ch13.lowerCharge, Function.update_of_ne branches.distinct]
      exact hp)
  have hkmem : (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns :=
    (ground_memX h Ns branches.leftSpecies k).mpr (le_of_eq hk)
  have hpmem : (branches.rightSpecies,p) ∈ A05.groundConfiguration h Ns :=
    (ground_memX h Ns branches.rightSpecies p).mpr (le_of_eq hp)
  have hpairne : (branches.rightSpecies,p) ≠ (branches.leftSpecies,k) := by
    intro he
    have hs := congrArg Prod.fst he
    exact branches.distinct hs
  have hpErase : (branches.rightSpecies,p) ∈
      (A05.groundConfiguration h Ns).erase (branches.leftSpecies,k) :=
    Finset.mem_erase.mpr ⟨hpairne, hpmem⟩
  have hcfg := sc_pair_reverseX h branches Ns k p hk hp
  have hraw : A05.annihilation h branches.rightSpecies p
      (A05.annihilation h branches.leftSpecies k (A05.groundKet h Ns)) =
      (Ch04.fermionSign (branches.rightSpecies,p)
        ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) *
       Ch04.fermionSign (branches.leftSpecies,k)
        (A05.groundConfiguration h Ns)) •
        A05.groundKet h (Ch13.lowerCharge
          (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies) := by
    unfold A05.annihilation A05.groundKet
    rw [Ch04.annihilation_ket, ite_eq_left hkmem, map_smul,
      Ch04.annihilation_ket, ite_eq_left hpErase]
    rw [hcfg]
    simp [smul_smul, scTarget, Ch13.lowerCharge, mul_comm]
  have htop : A05.annihilation h branches.rightSpecies p
      (A05.annihilation h branches.leftSpecies k (A05.groundKet h Ns)) =
      (Ch13.kleinPhase h Ns branches.leftSpecies *
        Ch13.kleinPhase h (Ch13.lowerCharge Ns branches.leftSpecies)
          branches.rightSpecies) •
        A05.groundKet h (Ch13.lowerCharge
          (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies) := by
    rw [hleft, map_smul, hright]
    simp [smul_smul]
  have hs := congrArg (fun v => inner ℂ
      (A05.groundKet h (Ch13.lowerCharge
        (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies)) v)
      (hraw.symm.trans htop)
  have hnorm : inner ℂ
      (A05.groundKet h (Ch13.lowerCharge
        (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies))
      (A05.groundKet h (Ch13.lowerCharge
        (Ch13.lowerCharge Ns branches.leftSpecies) branches.rightSpecies)) = 1 := by
    simp [A05.groundKet, A02.ket_norm]
  simp only [inner_smul_right, hnorm, mul_one] at hs
  exact hs


private lemma map_if_zeroX {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    [Module ℂ V] [Module ℂ W] (f : V →ₗ[ℂ] W) (p : Prop) [Decidable p] (v : V) :
    f (if p then v else 0) = if p then f v else 0 := by
  split_ifs <;> simp

private lemma orderSC_expandX (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (br : A06.Branches σ) (x : ℤ) (S : A05.Occupation σ h) :
    orderSC h b br x (A02.ket S) =
      ((A01.normalization (2*h) : ℂ)^2) •
        ∑ k : Ch01.Band (2*h), ∑ p : Ch01.Band (2*h),
          if (br.leftSpecies,k) ∈ S ∧
             (br.rightSpecies,p) ∈ S.erase (br.leftSpecies,k) then
            ((Ch06Ext.twistedCharacter (2*h) (b br.rightSpecies) p x *
               Ch04.fermionSign (br.rightSpecies,p) (S.erase (br.leftSpecies,k))) *
             (Ch06Ext.twistedCharacter (2*h) (b br.leftSpecies) k x *
               Ch04.fermionSign (br.leftSpecies,k) S)) •
              A02.ket ((S.erase (br.leftSpecies,k)).erase (br.rightSpecies,p))
          else 0 := by
  unfold orderSC
  simp only [Module.End.mul_apply, fieldOf]
  rw [fieldKetX h b S br.leftSpecies x]
  simp only [map_smul, map_sum]
  simp_rw [map_if_zeroX, map_smul, fieldKetX]
  simp_rw [smul_smul, Finset.smul_sum]
  congr 1
  funext k
  by_cases hk : (br.leftSpecies,k) ∈ S
  · simp only [ite_eq_left hk]
    rw [Finset.smul_sum]
    congr 1
    funext p
    by_cases hp : (br.rightSpecies,p) ∈ S.erase (br.leftSpecies,k)
    · rw [ite_eq_left hp, ite_eq_left ⟨hk,hp⟩]
      simp only [smul_smul]
      congr 1
      ring
    · rw [ite_eq_right hp, ite_eq_right (by simp [hk,hp])]
      simp
  · simp [hk]


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
      have : ¬ g a j := by
        intro h
        exact hj ((ha a j h).2)
      simp [this]
    · simp
  · intro i _ hi
    have hzero : ∀ j, ¬ g i j := by
      intro j h
      exact hi ((ha i j h).1)
    simp [hzero]
  · simp


private lemma orderSC_inner_expandX (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (br : A06.Branches σ) (x : ℤ) (S T : A05.Occupation σ h) :
    inner ℂ (A02.ket T) (orderSC h b br x (A02.ket S)) =
      ((A01.normalization (2*h) : ℂ)^2) *
        ∑ k : Ch01.Band (2*h), ∑ p : Ch01.Band (2*h),
          if (br.rightSpecies,p) ∈ S ∧ (br.leftSpecies,k) ∈ S ∧
             (br.rightSpecies = br.leftSpecies → p ≠ k) ∧
             T = (S.erase (br.leftSpecies,k)).erase (br.rightSpecies,p) then
            Ch04.fermionSign (br.rightSpecies,p) (S.erase (br.leftSpecies,k)) *
              (Ch04.fermionSign (br.leftSpecies,k) S *
                (Ch06Ext.twistedCharacter (2*h) (b br.rightSpecies) p x *
                  Ch06Ext.twistedCharacter (2*h) (b br.leftSpecies) k x))
          else 0 := by
  rw [orderSC_expandX]
  rw [inner_smul_right]
  rw [inner_fsumX]
  simp_rw [inner_fsumX]
  simp_rw [inner_if_zeroX, inner_smul_right, A02.ket_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro p _
  by_cases hR : (br.rightSpecies,p) ∈ S <;>
    by_cases hL : (br.leftSpecies,k) ∈ S <;>
    by_cases hD : br.rightSpecies = br.leftSpecies → p ≠ k <;>
    by_cases hE : T = (S.erase (br.leftSpecies,k)).erase (br.rightSpecies,p) <;>
    simp [hR,hL,hD,hE, Finset.mem_erase,
      mul_assoc, mul_comm, mul_left_comm]

end GroundCoeffProofHelpers

lemma orderSC_ground_coeff (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hR : -(h : ℤ) < Ns branches.rightSpecies)
    (hL : -(h : ℤ) < Ns branches.leftSpecies) (x : ℤ) :
    inner ℂ (A05.groundKet h (scTarget branches Ns))
      (orderSC h (fun _ => Ch06Ext.periodicTwist (2 * h)) branches x
        (A05.groundKet h Ns)) =
      (((2 * h : ℕ) : ℂ)⁻¹) * scChargeCoeff h branches Ns x := by
  let _ : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
  let _ : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
  let k0 : Ch01.Band (2*h) := ⟨Ns branches.leftSpecies, by
    unfold Ch01.inBandPredicate
    obtain ⟨_,hu⟩ := hN branches.leftSpecies
    push_cast
    constructor <;> omega⟩
  let p0 : Ch01.Band (2*h) := ⟨Ns branches.rightSpecies, by
    unfold Ch01.inBandPredicate
    obtain ⟨_,hu⟩ := hN branches.rightSpecies
    push_cast
    constructor <;> omega⟩
  have hk0 : k0.val = Ns branches.leftSpecies := rfl
  have hp0 : p0.val = Ns branches.rightSpecies := rfl
  have hkmem : (branches.leftSpecies,k0) ∈ A05.groundConfiguration h Ns :=
    (ground_memX h Ns branches.leftSpecies k0).mpr (le_of_eq hk0)
  have hpmem : (branches.rightSpecies,p0) ∈ A05.groundConfiguration h Ns :=
    (ground_memX h Ns branches.rightSpecies p0).mpr (le_of_eq hp0)
  let g (k : Ch01.Band (2*h)) (p : Ch01.Band (2*h)) : Prop :=
    (branches.rightSpecies,p) ∈ A05.groundConfiguration h Ns ∧
      (branches.leftSpecies,k) ∈ A05.groundConfiguration h Ns ∧
      (branches.rightSpecies = branches.leftSpecies → p ≠ k) ∧
      A05.groundConfiguration h (scTarget branches Ns) =
        Finset.erase (Finset.erase (A05.groundConfiguration h Ns)
          (branches.leftSpecies,k)) (branches.rightSpecies,p)
  let f (k : Ch01.Band (2*h)) (p : Ch01.Band (2*h)) : ℂ :=
    Ch04.fermionSign (branches.rightSpecies,p)
        ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k)) *
      (Ch04.fermionSign (branches.leftSpecies,k)
        (A05.groundConfiguration h Ns) *
        (Ch06Ext.twistedCharacter (2*h)
          (Ch06Ext.periodicTwist (2*h)) p x *
         Ch06Ext.twistedCharacter (2*h)
          (Ch06Ext.periodicTwist (2*h)) k x))
  have hsupport : g k0 p0 := by
    apply (sc_ground_pair_cond_iffX h branches Ns k0 p0 hkmem hpmem).2
    exact ⟨hk0,hp0⟩
  have huniq : ∀ k p, g k p → k = k0 ∧ p = p0 := by
    intro k p hg
    have hv := (sc_ground_pair_cond_iffX h branches Ns k p
      hg.2.1 hg.1).mp hg
    constructor
    · apply Subtype.ext
      exact hv.1.trans hk0.symm
    · apply Subtype.ext
      exact hv.2.trans hp0.symm
  rw [A05.groundKet, A05.groundKet, orderSC_inner_expandX]
  change ((A01.normalization (2*h) : ℂ)^2) *
      (∑ k : Ch01.Band (2*h), ∑ p : Ch01.Band (2*h),
        if g k p then f k p else 0) = _
  rw [sum_single_pairX k0 p0 f g huniq hsupport]
  dsimp [f]
  have hsign := sc_pair_sign_kleinX h hh branches Ns hN hR hL k0 p0 hk0 hp0
  have hcharR : Ch06Ext.twistedCharacter (2*h)
      (Ch06Ext.periodicTwist (2*h)) p0 x =
      A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns branches.rightSpecies) x := by
    simp [Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, Ch06Ext.periodicTwist, hp0]
  have hcharL : Ch06Ext.twistedCharacter (2*h)
      (Ch06Ext.periodicTwist (2*h)) k0 x =
      A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns branches.leftSpecies) x := by
    simp [Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, Ch06Ext.periodicTwist, hk0]
  have hT : Ch13.lowerCharge Ns branches.leftSpecies branches.rightSpecies =
      Ns branches.rightSpecies := by
    simp [Ch13.lowerCharge, branches.distinct]
  calc
    _ = ((A01.normalization (2*h) : ℂ)^2) *
        ((Ch04.fermionSign (branches.rightSpecies,p0)
            ((A05.groundConfiguration h Ns).erase (branches.leftSpecies,k0)) *
          Ch04.fermionSign (branches.leftSpecies,k0)
            (A05.groundConfiguration h Ns)) *
         (A01.integerCharacter (A01.canonicalRoot (2*h))
            (Ns branches.rightSpecies) x *
          A01.integerCharacter (A01.canonicalRoot (2*h))
            (Ns branches.leftSpecies) x)) := by
      rw [hcharR, hcharL]
      ring
    _ = ((A01.normalization (2*h) : ℂ)^2) *
        ((Ch13.kleinPhase h Ns branches.leftSpecies *
          Ch13.kleinPhase h (Ch13.lowerCharge Ns branches.leftSpecies)
            branches.rightSpecies) *
         (A01.integerCharacter (A01.canonicalRoot (2*h))
            (Ns branches.rightSpecies) x *
          A01.integerCharacter (A01.canonicalRoot (2*h))
            (Ns branches.leftSpecies) x)) := by
      rw [hsign]
    _ = ((A01.normalization (2*h) : ℂ) *
          Ch13.kleinPhase h (Ch13.lowerCharge Ns branches.leftSpecies)
            branches.rightSpecies *
          A01.integerCharacter (A01.canonicalRoot (2*h))
            (Ns branches.rightSpecies) x) *
        ((A01.normalization (2*h) : ℂ) *
          Ch13.kleinPhase h Ns branches.leftSpecies *
          A01.integerCharacter (A01.canonicalRoot (2*h))
            (Ns branches.leftSpecies) x) := by ring
    _ = (((2*h : ℕ) : ℂ)⁻¹) * scChargeCoeff h branches Ns x := by
      simpa [scChargeCoeff, hT] using
        scalar_top_pair_sc h hh Ns (Ch13.lowerCharge Ns branches.leftSpecies)
          branches.leftSpecies branches.rightSpecies x hT



/-- Scalar Klein laws for reflection. They hold for either species order. -/
lemma klein_reflect_right (h : ℕ) (branches : A06.Branches σ) (Ns : σ → ℤ) :
    Ch13.kleinPhase h (reflectLeft branches Ns) branches.rightSpecies =
      Ch13.kleinPhase h Ns branches.rightSpecies := by
  unfold Ch13.kleinPhase
  have hdelta :
      (∑ η ∈ Finset.univ.filter (· < branches.rightSpecies),
        (if η = branches.leftSpecies then 2 * Ns branches.leftSpecies else 0)) =
        (if branches.leftSpecies < branches.rightSpecies then
          2 * Ns branches.leftSpecies else 0) := by
    by_cases hlt : branches.leftSpecies < branches.rightSpecies
    · rw [Finset.sum_eq_single branches.leftSpecies]
      · simp [hlt]
      · intro η hη hηL
        simp [hηL]
      · intro hnot
        exact False.elim (hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩))
    · rw [Finset.sum_eq_zero]
      · simp [hlt]
      · intro η hη
        by_cases heq : η = branches.leftSpecies
        · subst η
          exact False.elim (hlt (Finset.mem_filter.mp hη).2)
        · simp [heq]
  have hsum :
      (∑ η ∈ Finset.univ.filter (· < branches.rightSpecies),
        ((h : ℤ) + Function.update Ns branches.leftSpecies
          (-Ns branches.leftSpecies) η)) =
      (∑ η ∈ Finset.univ.filter (· < branches.rightSpecies), ((h : ℤ) + Ns η)) -
        (∑ η ∈ Finset.univ.filter (· < branches.rightSpecies),
          (if η = branches.leftSpecies then 2 * Ns branches.leftSpecies else 0)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro η hη
    by_cases heq : η = branches.leftSpecies
    · subst η
      simp [Function.update]
      ring
    · simp [Function.update, heq]
  have he :
      Ch13.phaseExponent h (reflectLeft branches Ns) branches.rightSpecies =
        Ch13.phaseExponent h Ns branches.rightSpecies -
          (if branches.leftSpecies < branches.rightSpecies then
            2 * Ns branches.leftSpecies else 0) := by
    unfold Ch13.phaseExponent reflectLeft
    rw [hsum, hdelta]
    simp only [Function.update]
    have hne : branches.rightSpecies ≠ branches.leftSpecies := branches.distinct
    simp [hne]
    ring
  rw [he]
  by_cases hlt : branches.leftSpecies < branches.rightSpecies
  · simp only [hlt, ite_true]
    rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    have hp : (-1 : ℂ) ^ (2 * Ns branches.leftSpecies) = 1 := by
      rw [zpow_mul]
      norm_num
    simp [hp]
  · simp [hlt]

lemma klein_reflect_left (h : ℕ) (branches : A06.Branches σ) (Ns : σ → ℤ) :
    Ch13.kleinPhase h (reflectLeft branches Ns) branches.leftSpecies =
      -Ch13.kleinPhase h (raiseCharge Ns branches.leftSpecies)
        branches.leftSpecies := by
  unfold Ch13.kleinPhase
  have hsum1 :
      (∑ η ∈ Finset.univ.filter (· < branches.leftSpecies),
        ((h : ℤ) + Function.update Ns branches.leftSpecies
          (-Ns branches.leftSpecies) η)) =
      (∑ η ∈ Finset.univ.filter (· < branches.leftSpecies), ((h : ℤ) + Ns η)) := by
    apply Finset.sum_congr rfl
    intro η hη
    have hne : η ≠ branches.leftSpecies := by
      intro he
      subst η
      exact (not_lt_of_ge le_rfl) (Finset.mem_filter.mp hη).2
    simp [Function.update, hne]
  have hsum2 :
      (∑ η ∈ Finset.univ.filter (· < branches.leftSpecies),
        ((h : ℤ) + Function.update Ns branches.leftSpecies
          (Ns branches.leftSpecies + 1) η)) =
      (∑ η ∈ Finset.univ.filter (· < branches.leftSpecies), ((h : ℤ) + Ns η)) := by
    apply Finset.sum_congr rfl
    intro η hη
    have hne : η ≠ branches.leftSpecies := by
      intro he
      subst η
      exact (not_lt_of_ge le_rfl) (Finset.mem_filter.mp hη).2
    simp [Function.update, hne]
  have he :
      Ch13.phaseExponent h (reflectLeft branches Ns) branches.leftSpecies =
        Ch13.phaseExponent h (raiseCharge Ns branches.leftSpecies)
            branches.leftSpecies - 2 * Ns branches.leftSpecies - 1 := by
    unfold Ch13.phaseExponent reflectLeft raiseCharge
    rw [hsum1, hsum2]
    simp [Function.update]
    ring
  rw [he]
  rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  have hp : (-1 : ℂ) ^ (2 * Ns branches.leftSpecies) = 1 := by
    rw [zpow_mul]
    norm_num
  simp [hp]
  rw [div_neg, div_one]

omit [Fintype σ] in
lemma cdw_target_dual (branches : A06.Branches σ) (Ns : σ → ℤ) :
    reflectLeft branches (cdwTarget branches (reflectLeft branches Ns)) =
      raiseCharge (raiseCharge Ns branches.rightSpecies) branches.leftSpecies := by
  have hLR : branches.leftSpecies ≠ branches.rightSpecies := branches.distinct.symm
  have hRL : branches.rightSpecies ≠ branches.leftSpecies := branches.distinct
  funext ν
  by_cases hR : ν = branches.rightSpecies <;>
    by_cases hL : ν = branches.leftSpecies <;>
    simp [cdwTarget, reflectLeft, raiseCharge, Ch13.lowerCharge,
      Function.update, hR, hL, hLR, hRL]; omega

omit [Fintype σ] in
lemma scTarget_reverse_double_raise (branches : A06.Branches σ) (Ns : σ → ℤ) :
    scTarget branches (raiseCharge (raiseCharge Ns branches.rightSpecies)
      branches.leftSpecies) = Ns := by
  simp [scTarget, lowerCharge_raiseCharge]

omit [Fintype σ] in
lemma sc_target_dual (branches : A06.Branches σ) (Ns : σ → ℤ) :
    reflectLeft branches (scTarget branches (reflectLeft branches Ns)) =
      raiseCharge (Ch13.lowerCharge Ns branches.rightSpecies)
        branches.leftSpecies := by
  have hLR : branches.leftSpecies ≠ branches.rightSpecies := branches.distinct.symm
  have hRL : branches.rightSpecies ≠ branches.leftSpecies := branches.distinct
  funext ν
  by_cases hR : ν = branches.rightSpecies <;>
    by_cases hL : ν = branches.leftSpecies <;>
    simp [scTarget, reflectLeft, raiseCharge, Ch13.lowerCharge,
      Function.update, hR, hL, hLR, hRL]; omega

omit [Fintype σ] in
lemma cdwTarget_reverse_shift (branches : A06.Branches σ) (Ns : σ → ℤ) :
    cdwTarget branches
      (raiseCharge (Ch13.lowerCharge Ns branches.rightSpecies)
        branches.leftSpecies) = Ns := by
  have hLR : branches.leftSpecies ≠ branches.rightSpecies := branches.distinct.symm
  have hRL : branches.rightSpecies ≠ branches.leftSpecies := branches.distinct
  funext ν
  by_cases hR : ν = branches.rightSpecies <;>
    by_cases hL : ν = branches.leftSpecies <;>
    simp [cdwTarget, raiseCharge, Ch13.lowerCharge, Function.update,
      hR, hL, hLR, hRL]

/-- Scalar shadow of the adjoint duality, including the indispensable χ(1,x). -/
lemma cdw_charge_duality (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ) (x : ℤ) :
    cdwChargeCoeff h branches (reflectLeft branches Ns) x =
      A01.integerCharacter (A01.canonicalRoot (2 * h)) 1 x *
        star (scChargeCoeff h branches
          (raiseCharge (raiseCharge Ns branches.rightSpecies)
            branches.leftSpecies) x) := by
  unfold cdwChargeCoeff scChargeCoeff
  let N' := raiseCharge (raiseCharge Ns branches.rightSpecies) branches.leftSpecies
  have hroot : IsPrimitiveRoot (A01.canonicalRoot (2*h)) (2*h) :=
    @A01.canonical_root_primitive (2*h) ⟨by omega⟩
  have hchar :
      A01.integerCharacter (A01.canonicalRoot (2*h))
          (reflectLeft branches Ns branches.leftSpecies -
            reflectLeft branches Ns branches.rightSpecies - 1) x =
        A01.integerCharacter (A01.canonicalRoot (2*h)) 1 x *
          star (A01.integerCharacter (A01.canonicalRoot (2*h))
            (N' branches.rightSpecies + N' branches.leftSpecies) x) := by
    rw [@A01.complex_character_conj (2*h) ⟨by omega⟩ _ hroot _ x]
    simp only [A01.integerCharacter]
    simp [reflectLeft, raiseCharge, N', Function.update, branches.distinct,
      branches.distinct.symm]
    rw [← zpow_add₀ (show A01.canonicalRoot (2*h) ≠ 0 from
      (hroot.ne_zero (by omega)))]
    congr 1
    ring_nf
  have hKleft := klein_reflect_left h branches Ns
  have hTD := cdw_target_dual branches Ns
  have hKright := klein_reflect_right h branches
    (cdwTarget branches (reflectLeft branches Ns))
  have hKL : Ch13.kleinPhase h (reflectLeft branches Ns) branches.leftSpecies =
      -Ch13.kleinPhase h (raiseCharge Ns branches.leftSpecies) branches.leftSpecies := hKleft
  have hKR : Ch13.kleinPhase h (cdwTarget branches (reflectLeft branches Ns))
       branches.rightSpecies =
      Ch13.kleinPhase h N' branches.rightSpecies := by
    calc
      Ch13.kleinPhase h (cdwTarget branches (reflectLeft branches Ns)) branches.rightSpecies =
        Ch13.kleinPhase h (reflectLeft branches (cdwTarget branches (reflectLeft branches Ns))) branches.rightSpecies :=
          hKright.symm
      _ = Ch13.kleinPhase h N' branches.rightSpecies := by rw [hTD]
  have hlowL : Ch13.lowerCharge N' branches.leftSpecies =
      raiseCharge Ns branches.rightSpecies := by
    funext ν
    by_cases hνL : ν = branches.leftSpecies
    · subst ν
      simp [N', Ch13.lowerCharge, raiseCharge, Function.update]
    · by_cases hνR : ν = branches.rightSpecies
      · subst ν
        simp [N', Ch13.lowerCharge, raiseCharge, Function.update, hνL]
      · simp [N', Ch13.lowerCharge, raiseCharge, Function.update, hνL, hνR]
  have hlowR : Ch13.lowerCharge N' branches.rightSpecies =
      raiseCharge Ns branches.leftSpecies := by
    funext ν
    by_cases hνR : ν = branches.rightSpecies
    · subst ν
      simp [N', Ch13.lowerCharge, raiseCharge, Function.update, branches.distinct]
    · by_cases hνL : ν = branches.leftSpecies
      · subst ν
        simp [N', Ch13.lowerCharge, raiseCharge, Function.update, hνR]
      · simp [N', Ch13.lowerCharge, raiseCharge, Function.update, hνR, hνL]
  have hcross := Ch13.phase_cross_sign h N' branches.leftSpecies
      branches.rightSpecies branches.distinct.symm
  have hphase :
      Ch13.kleinPhase h (reflectLeft branches Ns) branches.leftSpecies *
        Ch13.kleinPhase h (cdwTarget branches (reflectLeft branches Ns))
          branches.rightSpecies =
       star (Ch13.kleinPhase h N' branches.leftSpecies *
         Ch13.kleinPhase h (Ch13.lowerCharge N' branches.leftSpecies)
           branches.rightSpecies) := by
    rw [hKL, hKR, hlowL]
    have hc := hcross
    rw [hlowL, hlowR] at hc
    have hs (M : σ → ℤ) (ν : σ) : star (Ch13.kleinPhase h M ν) =
        Ch13.kleinPhase h M ν := by simp [Ch13.kleinPhase]
    rw [star_mul, hs, hs]
    simpa [mul_comm] using hc.symm
  rw [hchar, hphase]
  simp only [star_mul]
  dsimp [N']
  ring

lemma sc_charge_duality (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ) (x : ℤ) :
    scChargeCoeff h branches (reflectLeft branches Ns) x =
      A01.integerCharacter (A01.canonicalRoot (2 * h)) 1 x *
        star (cdwChargeCoeff h branches
          (raiseCharge (Ch13.lowerCharge Ns branches.rightSpecies)
            branches.leftSpecies) x) := by
  unfold scChargeCoeff cdwChargeCoeff
  let N' := raiseCharge (Ch13.lowerCharge Ns branches.rightSpecies) branches.leftSpecies
  let M := raiseCharge Ns branches.leftSpecies
  have hroot : IsPrimitiveRoot (A01.canonicalRoot (2*h)) (2*h) :=
    @A01.canonical_root_primitive (2*h) ⟨by omega⟩
  have hchar :
      A01.integerCharacter (A01.canonicalRoot (2*h))
          (reflectLeft branches Ns branches.rightSpecies +
            reflectLeft branches Ns branches.leftSpecies) x =
        A01.integerCharacter (A01.canonicalRoot (2*h)) 1 x *
          star (A01.integerCharacter (A01.canonicalRoot (2*h))
            (raiseCharge (Ch13.lowerCharge Ns branches.rightSpecies) branches.leftSpecies branches.leftSpecies -
             raiseCharge (Ch13.lowerCharge Ns branches.rightSpecies) branches.leftSpecies branches.rightSpecies - 1) x) := by
    rw [@A01.complex_character_conj (2*h) ⟨by omega⟩ _ hroot _ x]
    simp only [A01.integerCharacter]
    simp [reflectLeft, raiseCharge, Ch13.lowerCharge,
      Function.update, branches.distinct, branches.distinct.symm]
    rw [← zpow_add₀ (show A01.canonicalRoot (2*h) ≠ 0 from
      (hroot.ne_zero (by omega))) x
      ((1 - (Ns branches.leftSpecies + 1 -
        (Ns branches.rightSpecies - 1))) * x)]
    congr 1
    ring_nf
  have hKL := klein_reflect_left h branches Ns
  have hleftstate :
      Ch13.lowerCharge (reflectLeft branches Ns) branches.leftSpecies =
        reflectLeft branches M := by
    funext ν
    by_cases hν : ν = branches.leftSpecies
    · subst ν
      simp [Ch13.lowerCharge, reflectLeft, M, raiseCharge, Function.update]
      omega
    · simp [Ch13.lowerCharge, reflectLeft, M, raiseCharge, Function.update, hν]
  have hKR := klein_reflect_right h branches M
  have hright :
      Ch13.kleinPhase h (Ch13.lowerCharge (reflectLeft branches Ns)
        branches.leftSpecies) branches.rightSpecies =
        Ch13.kleinPhase h M branches.rightSpecies := by
    calc
      Ch13.kleinPhase h (Ch13.lowerCharge (reflectLeft branches Ns)
        branches.leftSpecies) branches.rightSpecies =
        Ch13.kleinPhase h (reflectLeft branches M)
          branches.rightSpecies := by rw [hleftstate]
      _ = Ch13.kleinPhase h M branches.rightSpecies := hKR
  have htarget := cdwTarget_reverse_shift branches Ns
  have hcross := Ch13.phase_cross_sign h M
      branches.rightSpecies branches.leftSpecies branches.distinct
  have hlowR :
      Ch13.lowerCharge M branches.rightSpecies = N' := by
    funext ν
    by_cases hνR : ν = branches.rightSpecies
    · subst ν
      simp [N', M, Ch13.lowerCharge, raiseCharge, Function.update, branches.distinct]
    · by_cases hνL : ν = branches.leftSpecies
      · subst ν
        simp [N', M, Ch13.lowerCharge, raiseCharge, Function.update, hνR]
      · simp [N', M, Ch13.lowerCharge, raiseCharge, Function.update, hνR, hνL]
  have hlowL : Ch13.lowerCharge M branches.leftSpecies = Ns := by
    exact lowerCharge_raiseCharge Ns branches.leftSpecies
  have hphase :
      Ch13.kleinPhase h (reflectLeft branches Ns) branches.leftSpecies *
        Ch13.kleinPhase h (Ch13.lowerCharge (reflectLeft branches Ns)
          branches.leftSpecies) branches.rightSpecies =
       star (Ch13.kleinPhase h N' branches.leftSpecies *
         Ch13.kleinPhase h (cdwTarget branches N') branches.rightSpecies) := by
    rw [hKL, hright]
    have hc := hcross
    rw [hlowL, hlowR] at hc
    have hs (P : σ → ℤ) (ν : σ) : star (Ch13.kleinPhase h P ν) =
        Ch13.kleinPhase h P ν := by simp [Ch13.kleinPhase]
    have hsq (P : σ → ℤ) (ν : σ) :
        Ch13.kleinPhase h P ν * Ch13.kleinPhase h P ν = 1 := by
      unfold Ch13.kleinPhase
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      rw [← two_mul, zpow_mul]
      norm_num
    let A := Ch13.kleinPhase h N' branches.leftSpecies
    let B := Ch13.kleinPhase h M branches.rightSpecies
    let C := Ch13.kleinPhase h Ns branches.rightSpecies
    let D := Ch13.kleinPhase h M branches.leftSpecies
    have hAB : A * B = -(C * D) := by simpa [A, B, C, D] using hc
    have hB : B * B = 1 := by simpa [B] using hsq M branches.rightSpecies
    have hC : C * C = 1 := by simpa [C] using hsq Ns branches.rightSpecies
    have hcross' : A * C = -(D * B) := by
      calc
        _ = A * (B * B) * C := by rw [hB]; ring
        _ = (A * B) * (B * C) := by ring
        _ = (-(C * D)) * (B * C) := by rw [hAB]
        _ = -(D * B) * (C * C) := by ring
        _ = -(D * B) := by rw [hC]; ring
    rw [htarget, star_mul, hs, hs]
    simpa [A, B, C, D, mul_comm] using hcross'.symm
  rw [hchar, hphase]
  simp only [star_mul]
  dsimp [N', M]
  ring

lemma cdwChargeCoeff_norm (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ) (x : ℤ) :
    ‖cdwChargeCoeff h branches Ns x‖ = 1 := by
  unfold cdwChargeCoeff
  rw [norm_mul, norm_mul,
    @A01.complex_character_norm (2*h) (⟨by omega⟩ : NeZero (2*h)) _
      (@A01.canonical_root_primitive (2*h) (⟨by omega⟩ : NeZero (2*h))),
    Ch13.phase_norm, Ch13.phase_norm]
  norm_num

lemma scChargeCoeff_norm (h : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ) (x : ℤ) :
    ‖scChargeCoeff h branches Ns x‖ = 1 := by
  unfold scChargeCoeff
  rw [norm_mul, norm_mul,
    @A01.complex_character_norm (2*h) (⟨by omega⟩ : NeZero (2*h)) _
      (@A01.canonical_root_primitive (2*h) (⟨by omega⟩ : NeZero (2*h))),
    Ch13.phase_norm, Ch13.phase_norm]
  norm_num

end FiniteCAR

section FiniteWitnesses

/-- Actual two-species source charge sector (0,0). -/
def witnessZero : Fin 2 → ℤ := fun _ => 0

/-- Actual two-species source charge sector (1,0). -/
def witnessSC : Fin 2 → ℤ := ![1, 0]

lemma witnessZero_admissible : A05.admissible 2 witnessZero := by
  intro ν
  simp [Ch07.admissible, witnessZero]

lemma concrete_cdw_coefficient :
    cdwChargeCoeff 2 Ch16.standardBranches witnessZero 1 = Complex.I := by
  have hroot : A01.canonicalRoot 4 = Complex.I := by
    unfold A01.canonicalRoot
    calc
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (4:ℂ)) =
          Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) := by
            congr 1
            ring
      _ = Complex.I := Complex.exp_pi_div_two_mul_I
  have he0 : (Finset.univ.filter (fun η : Fin 2 => η < 0)) = ∅ := by
    ext η
    simp
  have he1 : (Finset.univ.filter (fun η : Fin 2 => η < 1)) = {0} := by
    ext η
    simp
  have hleft : Ch13.phaseExponent 2 witnessZero Ch16.standardBranches.leftSpecies = 3 := by
    change Ch13.phaseExponent 2 witnessZero 1 = 3
    unfold Ch13.phaseExponent
    rw [he1]
    simp [witnessZero]
  have hright : Ch13.phaseExponent 2 (cdwTarget Ch16.standardBranches witnessZero)
      Ch16.standardBranches.rightSpecies = 2 := by
    change Ch13.phaseExponent 2 (cdwTarget Ch16.standardBranches witnessZero) 0 = 2
    unfold Ch13.phaseExponent
    rw [he0]
    dsimp [Ch16.standardBranches]
    simp [cdwTarget, Ch13.lowerCharge, raiseCharge, witnessZero]
  rw [cdwChargeCoeff]
  simp only [A01.integerCharacter, Ch13.kleinPhase]
  rw [hleft, hright]
  norm_num only [show (2 * 2 : ℕ) = 4 by norm_num]
  rw [hroot]
  norm_num [Ch16.standardBranches, witnessZero]

lemma concrete_sc_coefficient :
    scChargeCoeff 2 Ch16.standardBranches witnessSC 1 = Complex.I := by
  have hroot : A01.canonicalRoot 4 = Complex.I := by
    unfold A01.canonicalRoot
    calc
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (4:ℂ)) =
          Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) := by
            congr 1
            ring
      _ = Complex.I := Complex.exp_pi_div_two_mul_I
  have he0 : (Finset.univ.filter (fun η : Fin 2 => η < 0)) = ∅ := by
    ext η
    simp
  have he1 : (Finset.univ.filter (fun η : Fin 2 => η < 1)) = {0} := by
    ext η
    simp
  have hleft : Ch13.phaseExponent 2 witnessSC Ch16.standardBranches.leftSpecies = 4 := by
    change Ch13.phaseExponent 2 witnessSC 1 = 4
    unfold Ch13.phaseExponent
    rw [he1]
    simp [witnessSC]
  have hright : Ch13.phaseExponent 2 (Ch13.lowerCharge witnessSC Ch16.standardBranches.leftSpecies)
      Ch16.standardBranches.rightSpecies = 2 := by
    change Ch13.phaseExponent 2 (Ch13.lowerCharge witnessSC 1) 0 = 2
    unfold Ch13.phaseExponent
    rw [he0]
    simp [Ch13.lowerCharge, witnessSC]
  rw [scChargeCoeff]
  simp only [A01.integerCharacter, Ch13.kleinPhase]
  rw [hleft, hright]
  norm_num only [show (2 * 2 : ℕ) = 4 by norm_num]
  rw [hroot]
  norm_num [Ch16.standardBranches, witnessSC]

lemma concrete_order_witness_cdw :
    inner ℂ (A05.groundKet 2 (cdwTarget Ch16.standardBranches witnessZero))
      (orderCDW 2 (fun _ => Ch06Ext.periodicTwist 4)
        Ch16.standardBranches 1 (A05.groundKet 2 witnessZero)) =
      Complex.I / 4 := by
  rw [orderCDW_ground_coeff]
  · rw [concrete_cdw_coefficient]
    norm_num [A01.normalization]
    ring
  · decide
  · exact witnessZero_admissible
  · norm_num [Ch16.standardBranches, witnessZero]
  · norm_num [Ch16.standardBranches, witnessZero]

lemma concrete_order_witness_sc :
    inner ℂ (A05.groundKet 2 (scTarget Ch16.standardBranches witnessSC))
      (orderSC 2 (fun _ => Ch06Ext.periodicTwist 4)
        Ch16.standardBranches 1 (A05.groundKet 2 witnessSC)) =
      Complex.I / 4 := by
  rw [orderSC_ground_coeff]
  · rw [concrete_sc_coefficient]
    norm_num [A01.normalization]
    ring
  · decide
  · intro ν
    fin_cases ν <;> norm_num [Ch07.admissible, witnessSC]
  · norm_num [Ch16.standardBranches, witnessSC]


  · norm_num [Ch16.standardBranches, witnessSC]

noncomputable local instance targetZeroModeOrder :
    LinearOrder (A05.Mode (Fin 2) 2) := A05.localModeLinearOrder (σ:=Fin 2) 2
noncomputable local instance targetZeroModeLT :
    LT (A05.Mode (Fin 2) 2) := A05.localModeLT (σ:=Fin 2) 2
noncomputable local instance targetZeroModeLE :
    LE (A05.Mode (Fin 2) 2) := A05.localModeLE (σ:=Fin 2) 2
noncomputable local instance targetZeroModeDecEq :
    DecidableEq (A05.Mode (Fin 2) 2) :=
      fun a b => A05.localModeDecidableEq (σ:=Fin 2) 2 a b
noncomputable local instance targetZeroPairOrder :
    LinearOrder (Fin 2 × Ch01.Band 4) := A05.localModeLinearOrder (σ:=Fin 2) 2
noncomputable local instance targetZeroPairLT :
    LT (Fin 2 × Ch01.Band 4) := A05.localModeLT (σ:=Fin 2) 2
noncomputable local instance targetZeroPairLE :
    LE (Fin 2 × Ch01.Band 4) := A05.localModeLE (σ:=Fin 2) 2
noncomputable local instance targetZeroPairDecEq :
    DecidableEq (Fin 2 × Ch01.Band 4) :=
      A05.localModeDecidableEq (σ:=Fin 2) 2

section DiscardedTargetZeroHelpers

private def targetZeroMn : Ch01.Band 4 :=
  ⟨-1, by norm_num [Ch01.inBandPredicate]⟩
private def targetZeroM0 : Ch01.Band 4 :=
  ⟨0, by norm_num [Ch01.inBandPredicate]⟩

private noncomputable def targetZeroOccupation (l : Ch01.Band 4) :
    A05.Occupation (Fin 2) 2 :=
  insert (0,l) ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn))

private lemma targetZeroSpeciesBridge (S : A05.Occupation (Fin 2) 2)
    (η : Fin 2) (q : Ch01.Band 4) :
    q ∈ Ch07.speciesConfiguration 2 S η ↔ (η,q) ∈ S := by
  simp only [Ch07.speciesConfiguration, Finset.mem_image, Finset.mem_filter]
  aesop

private lemma targetZeroLeftSpeciesOccupation (l : Ch01.Band 4) :
    Ch07.speciesConfiguration 2 (targetZeroOccupation l) 1 = {targetZeroM0} := by
  ext q
  rw [targetZeroSpeciesBridge, Finset.mem_singleton]
  simp only [targetZeroOccupation, Finset.mem_insert, Finset.mem_erase]
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
    norm_num [targetZeroM0]
    omega
  · intro hq
    have hv : q.val = 0 := congrArg Subtype.val hq
    constructor
    · intro he
      have hqmn : q = targetZeroMn := by
        apply Subtype.ext
        exact congrArg Subtype.val (congrArg Prod.snd he)
      rw [hq] at hqmn
      have hv2 := congrArg Subtype.val hqmn
      norm_num [targetZeroM0, targetZeroMn] at hv2
    · simpa [witnessZero] using (show q.val ≤ 0 by omega)

private lemma targetZeroLeftSpeciesExcitation (l : Ch01.Band 4) :
    Ch07.excitationEnergy 2
      (Ch07.speciesConfiguration 2 (targetZeroOccupation l) 1) = 1 := by
  rw [targetZeroLeftSpeciesOccupation]
  unfold Ch07.excitationEnergy Ch07.relativeEnergy Ch07.relativeCharge
  rw [Ch05.sea_energy_even 2 (by decide)]
  norm_num [Ch07.groundEnergy, Ch05.occupationEnergy, targetZeroM0]

private lemma targetZeroOccupationExcitation_pos (l : Ch01.Band 4) :
    1 ≤ Ch07.totalExcitation 2 (targetZeroOccupation l) := by
  rw [Ch07.totalExcitation]
  have hsingle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun ν : Fin 2 => Ch07.excitationEnergy 2
      (Ch07.speciesConfiguration 2 (targetZeroOccupation l) ν))
    (fun ν hν => Ch07.excitation_nonneg 2 (by decide)
      (Ch07.speciesConfiguration 2 (targetZeroOccupation l) ν))
    (Finset.mem_univ (1 : Fin 2))
  have hleft := targetZeroLeftSpeciesExcitation l
  omega

private lemma targetZeroOccupation_not_budget_zero (l : Ch01.Band 4) :
    targetZeroOccupation l ∉
      Ch14.budgetSet 2 (cdwTarget Ch16.standardBranches witnessZero) 0 := by
  intro hb
  have hpos := targetZeroOccupationExcitation_pos l
  have ht := hb.2
  omega

private lemma targetZeroErasedSpeciesOne :
    Ch07.speciesConfiguration 2
      ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn)) 1 =
        {targetZeroM0} := by
  have hcfg : Ch07.speciesConfiguration 2
      ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn)) 1 =
      Ch07.speciesConfiguration 2 (targetZeroOccupation targetZeroM0) 1 := by
    ext q
    rw [targetZeroSpeciesBridge, targetZeroSpeciesBridge]
    simp [targetZeroOccupation, Finset.mem_erase]
  rw [hcfg, targetZeroLeftSpeciesOccupation]

private lemma targetZeroErasedExcitation_ge_one :
    1 ≤ Ch07.totalExcitation 2
      ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn)) := by
  rw [Ch07.totalExcitation]
  have hsingle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun ν : Fin 2 => Ch07.excitationEnergy 2
      (Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn)) ν))
    (fun ν hν => Ch07.excitation_nonneg 2 (by decide)
      (Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn)) ν))
    (Finset.mem_univ (1 : Fin 2))
  have hleft : Ch07.excitationEnergy 2
      (Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn)) 1) = 1 := by
    rw [targetZeroErasedSpeciesOne]
    exact targetZeroLeftSpeciesExcitation targetZeroM0
  omega

private lemma targetZeroErased_not_mid_budget :
    (A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn) ∉
      Ch14.budgetSet 2 (Ch13.lowerCharge witnessZero 1) 0 := by
  intro hb
  have hpos := targetZeroErasedExcitation_ge_one
  have ht := hb.2
  omega

private lemma targetZeroEraseM0_eq_lowerGround :
    (A05.groundConfiguration 2 witnessZero).erase (1,targetZeroM0) =
      A05.groundConfiguration 2 (Ch13.lowerCharge witnessZero 1) := by
  ext z
  obtain ⟨η,q⟩ := z
  rw [Finset.mem_erase, ground_memX 2 witnessZero η q,
    ground_memX 2 (Ch13.lowerCharge witnessZero 1) η q]
  by_cases hη : η = 1
  · subst η
    simp only [Ch13.lowerCharge, Function.update_self, witnessZero]
    constructor
    · rintro ⟨hne,hle⟩
      have hq : q.val ≠ 0 := by
        intro hv
        apply hne
        exact Prod.ext rfl (Subtype.ext (by simpa [targetZeroM0] using hv))
      have hb := q.property
      dsimp [Ch01.inBandPredicate] at hb
      omega
    · intro hle
      constructor
      · intro he
        have hv := congrArg Subtype.val (congrArg Prod.snd he)
        norm_num [targetZeroM0] at hv
        omega
      · omega
  · simp [Ch13.lowerCharge, witnessZero, hη]

private lemma targetZeroLowerAdmissible :
    A05.admissible 2 (Ch13.lowerCharge witnessZero 1) := by
  intro ν
  fin_cases ν <;>
    simp [Ch07.admissible, Ch13.lowerCharge, witnessZero, Function.update]

private lemma targetZeroEraseM0_mem_mid_budget :
    (A05.groundConfiguration 2 witnessZero).erase (1,targetZeroM0) ∈
      Ch14.budgetSet 2 (Ch13.lowerCharge witnessZero 1) 0 := by
  rw [targetZeroEraseM0_eq_lowerGround]
  rw [Ch14.budgetSet]
  have hmem := A05.ground_mem_budget 2 (by decide)
    (Ch13.lowerCharge witnessZero 1) targetZeroLowerAdmissible 0
  have hmem' : A02.ket
      (A05.groundConfiguration 2 (Ch13.lowerCharge witnessZero 1)) ∈
      Ch07.speciesBudget 2 (Ch13.lowerCharge witnessZero 1) 0 := by
    change A05.groundKet 2 (Ch13.lowerCharge witnessZero 1) ∈
      A05.jointBudget 2 (Ch13.lowerCharge witnessZero 1) 0
    exact hmem
  exact (Ch07.species_budget_ket 2
    (A05.groundConfiguration 2 (Ch13.lowerCharge witnessZero 1))
    (Ch13.lowerCharge witnessZero 1) 0).mp hmem'

private lemma targetZeroProjectionKet (l : Ch01.Band 4) :
    Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 0
      (A02.ket (targetZeroOccupation l)) = 0 := by
  rw [Ch14.projection, A03.projection_ket]
  simp only [ite_eq_right (targetZeroOccupation_not_budget_zero l)]

private lemma targetZeroOccupationEq (l : Ch01.Band 4) :
    insert (0,l) ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn)) =
      targetZeroOccupation l := rfl

private lemma targetZeroProjectionCreatedSum (c : ℂ) :
    Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 0
      (c • ∑ p : Ch01.Band 4,
          if (0,p) ∈ A05.groundConfiguration 2 witnessZero then 0 else
            star (Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) p 1) •
              Ch04.fermionSign (0,p)
                ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn)) •
                A02.ket (insert (0,p)
                  ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn)))) = 0 := by
  simp only [map_smul, map_sum]
  apply (smul_eq_zero).2
  right
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : (0,p) ∈ A05.groundConfiguration 2 witnessZero
  · simp [hp]
  · simp only [hp, ite_false, LinearMap.map_smul,
      targetZeroOccupationEq, targetZeroProjectionKet, smul_zero]

end DiscardedTargetZeroHelpers

section DiscardedResidualExpansionHelpers
variable {τ : Type*} [Fintype τ] [LinearOrder τ]
noncomputable local instance discardedModeOrder (h : ℕ) :
    LinearOrder (A05.Mode τ h) := A05.localModeLinearOrder h
noncomputable local instance discardedModeDecEq (h : ℕ) :
    DecidableEq (A05.Mode τ h) := A05.localModeDecidableEq h

private lemma discardedFieldKet (h : ℕ) (b : τ → Ch06Ext.BoundaryTwist (2*h))
    (ν : τ) (x : ℤ) (S : A05.Occupation τ h) :
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

private lemma discardedAdjointLiftedKet (h : ℕ)
    (b : τ → Ch06Ext.BoundaryTwist (2*h)) (ν : τ) (x : ℤ)
    (S : A05.Occupation τ h) :
    LinearMap.adjoint (A05.liftedAnnihilation h b ν x) (A02.ket S) =
      star (A01.normalization (2*h) : ℂ) •
        ∑ k : Ch01.Band (2*h),
          star (Ch06Ext.twistedCharacter (2*h) (b ν) k x) •
            (if (ν,k) ∉ S then
              Ch04.fermionSign (ν,k) S • A02.ket (insert (ν,k) S) else 0) := by
  rw [← LinearMap.star_eq_adjoint]
  simp [A05.liftedAnnihilation, A05.annihilation,
    Ch04.annihilation_eq_adjoint, LinearMap.star_eq_adjoint,
    LinearMap.adjoint_adjoint, Ch04.creation_ket]

private lemma discardedOneSubProjectionKet (h : ℕ) (Ns : τ → ℤ) (K : ℕ)
    (S : A05.Occupation τ h) (c : ℂ) :
    (1 - Ch14.projection h Ns K) (c • A02.ket S) =
      if S ∈ Ch14.budgetSet h Ns K then 0 else c • A02.ket S := by
  rw [LinearMap.sub_apply, Module.End.one_apply, map_smul]
  simp only [Ch14.projection, A03.projection_ket]
  by_cases hs : S ∈ Ch14.budgetSet h Ns K <;> simp [hs]

private lemma discardedProjectedFieldKet (h : ℕ)
    (b : τ → Ch06Ext.BoundaryTwist (2*h)) (br : A06.Branches τ)
    (x : ℤ) (Ns : τ → ℤ) (K : ℕ) (S : A05.Occupation τ h) :
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
  rw [discardedFieldKet]
  simp only [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (br.leftSpecies,k) ∈ S
  · simp only [hk, ite_true]
    rw [discardedOneSubProjectionKet]
  · simp [hk]

private lemma discardedResidualDoubleExpansion (h : ℕ)
    (b : τ → Ch06Ext.BoundaryTwist (2*h)) (br : A06.Branches τ)
    (x : ℤ) (Ns : τ → ℤ) (Km : ℕ) (S : A05.Occupation τ h) :
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
                    Ch04.fermionSign (br.rightSpecies,p)
                      (S.erase (br.leftSpecies,k)) •
                    A02.ket (insert (br.rightSpecies,p)
                      (S.erase (br.leftSpecies,k))) else 0))
        else 0 := by
  simp only [Ch20.cdwResidualOp, Module.End.mul_apply, Ch20.fieldOf]
  rw [discardedProjectedFieldKet]
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
      rw [discardedAdjointLiftedKet]
  · simp only [hk, ite_false, map_zero]
end DiscardedResidualExpansionHelpers

/-- Nonzero discarded L-hole, after the R creation and target projection. -/
lemma concrete_discarded_channel_nonzero :
    Ch14.projectedMap 2 witnessZero (cdwTarget Ch16.standardBranches witnessZero)
        0 1 (cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
          Ch16.standardBranches 1 witnessZero 0)
        (Ch14.groundVector 2 (by decide) witnessZero witnessZero_admissible 0) ≠ 0 := by
  classical
  let m1 : Ch01.Band 4 := ⟨1, by norm_num [Ch01.inBandPredicate]⟩
  have ground_memX := ground_memCDWX (σ := Fin 2)
  have speciesBridge := targetZeroSpeciesBridge
  have leftSpecies_residualOccupation := targetZeroLeftSpeciesOccupation
  have leftSpecies_residual_excitation := targetZeroLeftSpeciesExcitation
  have speciesEraseBridge (S : A05.Occupation (Fin 2) 2) (η ν : Fin 2)
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

  have speciesInsertBridge (S : A05.Occupation (Fin 2) 2) (η ν : Fin 2)
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

  have residual_m1_pair_unique (k p : Ch01.Band 4)
      (heq : insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) =
        targetZeroOccupation m1) : k = targetZeroMn ∧ p = m1 := by
    have hsL := congrArg (fun S => Ch07.speciesConfiguration 2 S 1) heq
    have hsR := congrArg (fun S => Ch07.speciesConfiguration 2 S 0) heq
    have hL0 : targetZeroM0 ∈ Ch07.speciesConfiguration 2
        (insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k))) 1 := by
      rw [hsL, leftSpecies_residualOccupation]
      simp
    have hsrcmn : targetZeroMn ∈ Ch07.speciesConfiguration 2
        (A05.groundConfiguration 2 witnessZero) 1 := by
      rw [speciesBridge, ground_memX]
      simp [witnessZero,targetZeroMn]
    have hk : k ≠ targetZeroM0 := by
      intro h
      subst k
      have hL0' : targetZeroM0 ∈ Ch07.speciesConfiguration 2
          ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroM0)) 1 := by
        rw [speciesInsertBridge] at hL0
        simpa using hL0
      have hnot : targetZeroM0 ∉ Ch07.speciesConfiguration 2
          ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroM0)) 1 := by
        rw [speciesEraseBridge]
        simp
      exact hnot hL0'
    have hkn : k = targetZeroMn := by
      have hmnAbsent : targetZeroMn ∉ Ch07.speciesConfiguration 2
          (insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k))) 1 := by
        rw [hsL, leftSpecies_residualOccupation]
        simp only [Finset.mem_singleton]
        intro heq
        have hv := congrArg Subtype.val heq
        norm_num [targetZeroMn,targetZeroM0] at hv
      have heraseAbsent : targetZeroMn ∉ Ch07.speciesConfiguration 2
          ((A05.groundConfiguration 2 witnessZero).erase (1,k)) 1 := by
        rw [speciesInsertBridge] at hmnAbsent
        intro hm
        exact hmnAbsent (Or.inl hm)
      by_contra hnot
      have hmnErase : targetZeroMn ∈ Ch07.speciesConfiguration 2
          ((A05.groundConfiguration 2 witnessZero).erase (1,k)) 1 := by
        apply (speciesEraseBridge _ _ _ _ _).mpr
        refine ⟨hsrcmn, Or.inr ?_⟩
        intro heq
        exact hnot heq.symm
      exact heraseAbsent hmnErase
    refine ⟨hkn, ?_⟩
    subst k
    have hR1 : m1 ∈ Ch07.speciesConfiguration 2
        (insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn))) 0 := by
      rw [hsR]
      rw [speciesBridge]
      simp [targetZeroOccupation, m1]
    have hsource1 : m1 ∉ Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn)) 0 := by
      rw [speciesEraseBridge, speciesBridge, ground_memX]
      simp [witnessZero,m1,targetZeroMn]
    rw [speciesInsertBridge] at hR1
    rcases hR1 with hbad | ⟨_,hp⟩
    · exact (hsource1 hbad).elim
    · exact hp.symm



  have rightSpecies_residual_m1 :
      Ch07.speciesConfiguration 2 (targetZeroOccupation m1) 0 =
        Ch07.groundConfiguration 2 1 := by
    ext q
    rw [speciesBridge]
    simp only [targetZeroOccupation, Finset.mem_insert, Finset.mem_erase]
    simp only [Prod.mk.injEq]
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


  have residual_m1_target_budget :
      targetZeroOccupation m1 ∈ Ch14.budgetSet 2
        (cdwTarget Ch16.standardBranches witnessZero) 1 := by
    rw [Ch14.budgetSet]
    constructor
    · intro ν
      fin_cases ν
      · change Ch07.relativeCharge 2
          (Ch07.speciesConfiguration 2 (targetZeroOccupation m1) 0) = 1
        rw [rightSpecies_residual_m1]
        exact Ch07.ground_configuration_charge 2 (by decide) 1 (by norm_num [Ch07.admissible])
      · change Ch07.relativeCharge 2
          (Ch07.speciesConfiguration 2 (targetZeroOccupation m1) 1) = -1
        rw [leftSpecies_residualOccupation]
        norm_num [Ch07.relativeCharge]
    · rw [Ch07.totalExcitation]
      simp only [Fin.sum_univ_two]
      rw [leftSpecies_residualOccupation, rightSpecies_residual_m1]
      have hleft : Ch07.excitationEnergy 2 {targetZeroM0} = 1 := by
        unfold Ch07.excitationEnergy Ch07.relativeEnergy Ch07.relativeCharge
        rw [Ch05.sea_energy_even 2 (by decide)]
        norm_num [Ch07.groundEnergy, Ch05.occupationEnergy, targetZeroM0]
      have hright : Ch07.excitationEnergy 2
          (Ch07.groundConfiguration 2 1) = 0 :=
        Ch07.ground_configuration_excitation 2 (by decide) 1 (by norm_num [Ch07.admissible])
      rw [hleft, hright]
      norm_num

  have mapIf
      (f : A05.FockSpace (Fin 2) 2 →ₗ[ℂ] A05.FockSpace (Fin 2) 2) (P : Prop) [Decidable P] (x y : A05.FockSpace (Fin 2) 2) :
      f (if P then x else y) = if P then f x else f y := by
    split_ifs <;> rfl

  have inner_zero_ifX (x v : A05.FockSpace (Fin 2) 2) (p : Prop) [Decidable p] :
      inner ℂ x (if p then 0 else v) = if p then 0 else inner ℂ x v := by
    split_ifs <;> simp

  let residual_m1_g (k p : Ch01.Band 4) : Prop :=
    (1,k) ∈ A05.groundConfiguration 2 witnessZero ∧
    (A05.groundConfiguration 2 witnessZero).erase (1,k) ∉
      Ch14.budgetSet 2 (Ch13.lowerCharge witnessZero 1) 0 ∧
    (0,p) ∉ (A05.groundConfiguration 2 witnessZero).erase (1,k) ∧
    insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) ∈
      Ch14.budgetSet 2 (cdwTarget Ch16.standardBranches witnessZero) 1 ∧
    insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) = targetZeroOccupation m1

  let residual_m1_f (k p : Ch01.Band 4) : ℂ :=
    Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) k 1 *
      Ch04.fermionSign (1,k) (A05.groundConfiguration 2 witnessZero) *
      star (A01.normalization 4 : ℂ) *
      star (Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) p 1) *
      Ch04.fermionSign (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k))

  have residual_m1_inner_expand :
      inner ℂ (A02.ket (targetZeroOccupation m1))
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
    rw [discardedResidualDoubleExpansion]
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
        · simp only [residual_m1_g, hp, not_true_eq_false, false_and, and_false, ite_false, mul_zero]
        · simp only [hp, not_false_eq_true, ite_true]
          by_cases ht : insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) ∈
              Ch14.budgetSet 2 (cdwTarget Ch16.standardBranches witnessZero) 1
          · by_cases heq : insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) =
                targetZeroOccupation m1
            · have hIns : insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) ∈
                  Ch14.budgetSet 2 (cdwTarget Ch16.standardBranches witnessZero) 1 := by
                rw [heq]
                exact residual_m1_target_budget
              simp only [residual_m1_g, hk, hmid, hp, heq, not_false_eq_true,
                true_and, and_true, ite_true, eq_self]
              simp [residual_m1_f, mul_assoc, mul_left_comm, mul_comm]
              rfl
            · have hneq : targetZeroOccupation m1 ≠
                  insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) :=
                fun h => heq h.symm
              simp only [residual_m1_g, hk, hmid, hp, heq, hneq, not_false_eq_true,
                and_false, ite_false]
              simp only [ite_self, mul_zero]
          · by_cases heq : insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) =
                targetZeroOccupation m1
            · have hIns : insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) ∈
                  Ch14.budgetSet 2 (cdwTarget Ch16.standardBranches witnessZero) 1 := by
                rw [heq]
                exact residual_m1_target_budget
              exact (ht hIns).elim
            · have hneq : targetZeroOccupation m1 ≠
                  insert (0,p) ((A05.groundConfiguration 2 witnessZero).erase (1,k)) :=
                fun h => heq h.symm
              simp only [residual_m1_g, hk, hmid, hp, heq, hneq, not_false_eq_true,
                and_false, ite_false]
              simp only [ite_self, mul_zero]
    · simp [hk, residual_m1_g]

  have residual_m1_coefficient_nonzero :
      inner ℂ (A02.ket (targetZeroOccupation m1))
        (Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 1
          (cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
            Ch16.standardBranches 1 witnessZero 0
            (@A02.ket (A05.Mode (Fin 2) 2) (inferInstance)
              (A05.localModeDecidableEq (σ:=Fin 2) 2)
              (A05.groundConfiguration 2 witnessZero)))) ≠ 0 := by
    rw [residual_m1_inner_expand]
    classical
    let g := residual_m1_g
    let f := residual_m1_f
    have huniq : ∀ k p, g k p → k = targetZeroMn ∧ p = m1 := by
      intro k p hg
      exact residual_m1_pair_unique k p hg.2.2.2.2
    have hsupport : g targetZeroMn m1 := by
      refine ⟨?_, targetZeroErased_not_mid_budget, ?_, residual_m1_target_budget, ?_⟩
      · rw [ground_memX 2 witnessZero 1 targetZeroMn]
        simp [witnessZero,targetZeroMn]
      · intro hp
        have hsource : (0,m1) ∈ A05.groundConfiguration 2 witnessZero :=
          (Finset.mem_erase.mp hp).2
        rw [ground_memX 2 witnessZero 0 m1] at hsource
        simp [witnessZero,m1] at hsource
      · simp [targetZeroOccupation]
    change (A01.normalization 4 : ℂ) *
        (∑ k : Ch01.Band 4, ∑ p : Ch01.Band 4,
          if g k p then f k p else 0) ≠ 0
    rw [sum_single_pairX targetZeroMn m1 f g huniq hsupport]
    simp only [f]
    have hnorm : (A01.normalization 4 : ℂ) ≠ 0 := by
      norm_num [A01.normalization]
    have hsign₁ : Ch04.fermionSign (1,targetZeroMn)
        (A05.groundConfiguration 2 witnessZero) ≠ 0 := by
      exact Ch04.fermion_sign_ne_zero _ _
    have hsign₂ : Ch04.fermionSign (0,m1)
        ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn)) ≠ 0 := by
      exact Ch04.fermion_sign_ne_zero _ _
    have hnormStar : star (A01.normalization 4 : ℂ) ≠ 0 := by
      simpa using hnorm
    have hchar₁ : Ch06Ext.twistedCharacter 4
        (Ch06Ext.periodicTwist 4) targetZeroMn 1 ≠ 0 := by
      unfold Ch06Ext.twistedCharacter
      apply mul_ne_zero
      · unfold Ch06Ext.liftPhase Ch06Ext.periodicTwist
        simp
      · unfold A01.integerCharacter
        have hroot : A01.canonicalRoot 4 ≠ 0 := by
          unfold A01.canonicalRoot
          exact Complex.exp_ne_zero _
        exact zpow_ne_zero _ hroot
    have hchar₂ : Ch06Ext.twistedCharacter 4
        (Ch06Ext.periodicTwist 4) m1 1 ≠ 0 := by
      unfold Ch06Ext.twistedCharacter
      apply mul_ne_zero
      · unfold Ch06Ext.liftPhase Ch06Ext.periodicTwist
        simp
      · unfold A01.integerCharacter
        have hroot : A01.canonicalRoot 4 ≠ 0 := by
          unfold A01.canonicalRoot
          exact Complex.exp_ne_zero _
        exact zpow_ne_zero _ hroot
    have hchar₂Star : star (Ch06Ext.twistedCharacter 4
        (Ch06Ext.periodicTwist 4) m1 1) ≠ 0 := by
      simpa using hchar₂
    unfold residual_m1_f
    apply mul_ne_zero hnorm
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hchar₁ hsign₁)
      hnormStar) hchar₂Star) hsign₂
  intro hz
  have hraw := congrArg Subtype.val hz
  change Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 1
      ((cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
        Ch16.standardBranches 1 witnessZero 0)
       (A05.groundKet 2 witnessZero)) = 0 at hraw
  have hi := congrArg (fun y => inner ℂ (A02.ket (targetZeroOccupation m1)) y) hraw
  simp at hi
  exact residual_m1_coefficient_nonzero hi


/-- A *different* target cutoff removes the same discarded channel. -/
lemma concrete_discarded_channel_target_zero :
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
  rw [discardedResidualDoubleExpansion]
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
    · have heq : x = targetZeroMn := by
        apply Subtype.ext
        simpa [targetZeroMn] using hneg
      subst x
      have hsrc : (Ch16.standardBranches.leftSpecies,targetZeroMn) ∈
          A05.groundConfiguration 2 witnessZero := by
        simpa [Ch16.standardBranches] using hmem
      simp [Ch16.standardBranches]
      have hmid :
          (A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn) ∉
            Ch14.budgetSet 2 (Ch13.lowerCharge witnessZero 1) 0 := by
        exact targetZeroErased_not_mid_budget
      simp only [ite_eq_left hmem, ite_eq_right hmid]
      have hkill := targetZeroProjectionCreatedSum (A01.normalization 4 : ℂ)
      simp only [LinearMap.map_smul]
      change (Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) targetZeroMn 1 *
          Ch04.fermionSign (1,targetZeroMn) (A05.groundConfiguration 2 witnessZero)) •
        (Ch14.projection 2 (cdwTarget Ch16.standardBranches witnessZero) 0)
          (A01.normalization 4 •
            ∑ p : Ch01.Band 4,
              if (0,p) ∈ A05.groundConfiguration 2 witnessZero then 0 else
                star (Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) p 1) •
                  Ch04.fermionSign (0,p)
                    ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn)) •
                  A02.ket (insert (0,p)
                    ((A05.groundConfiguration 2 witnessZero).erase (1,targetZeroMn)))) = 0
      exact (congrArg (fun z =>
        (Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) targetZeroMn 1 *
          Ch04.fermionSign (1,targetZeroMn) (A05.groundConfiguration 2 witnessZero)) • z)
        hkill).trans (by simp)
    · have heq : x = targetZeroM0 := by
        apply Subtype.ext
        simpa [targetZeroM0] using hzero
      subst x
      have hsrc : (Ch16.standardBranches.leftSpecies,targetZeroM0) ∈
          A05.groundConfiguration 2 witnessZero := by
        simpa [Ch16.standardBranches] using hmem
      have hmid :
          (A05.groundConfiguration 2 witnessZero).erase
            (Ch16.standardBranches.leftSpecies,targetZeroM0) ∈
          Ch14.budgetSet 2 (Ch13.lowerCharge witnessZero Ch16.standardBranches.leftSpecies) 0 := by
        convert targetZeroEraseM0_mem_mid_budget using 1 <;> rfl
      simp only [ite_eq_left hmid]
      simp [Ch16.standardBranches, hmem]
  · simp [Ch16.standardBranches, hmem]

lemma concrete_orderSC_nonzero :
    orderSC 2 (fun _ => Ch06Ext.periodicTwist 4) Ch16.standardBranches 1 ≠ 0 := by
  intro hz
  have h := congrArg (fun A : A05.Operators (Fin 2) 2 =>
    inner ℂ (A05.groundKet 2 (scTarget Ch16.standardBranches witnessSC))
      (A (A05.groundKet 2 witnessSC))) hz
  rw [concrete_order_witness_sc] at h
  norm_num at h

end FiniteWitnesses

section ModeFamilyDuality

/-- This parameter operation changes v₂ to -v₂, not the CAR representation. -/
def dualPair (hp : Ch18.HyperbolicPair) : Ch18.HyperbolicPair where
  c := hp.c
  s := -hp.s
  hyperbolic_id := by simpa only [neg_sq] using hp.hyperbolic_id

/-- Full hyperbolic witness with sign-reversed interaction; no data `sorry`. -/
def dualParams {v1 v2 : ℝ}
    (lp : A07Interactions.HyperbolicParams v1 v2) :
    A07Interactions.HyperbolicParams v1 (-v2) where
  u := lp.u
  c := lp.c
  s := -lp.s
  u_pos := lp.u_pos
  c_pos := lp.c_pos
  u_sq := by simpa only [neg_sq] using lp.u_sq
  hyperbolic_id := by simpa only [neg_sq] using lp.hyperbolic_id
  match_v1 := by simpa only [neg_sq] using lp.match_v1
  match_v2 := by
    simpa only [mul_neg] using congrArg Neg.neg lp.match_v2

/-- An indexed pair of ambient endomorphism families, not an oscillator quotient. -/
abbrev ModeFamily (E : Type*) [AddCommGroup E] [Module ℂ E] :=
  A06.Orientation → ℤ → Module.End ℂ E

noncomputable def speciesFamily {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h : ℕ) (branches : A06.Branches σ) : ModeFamily (A05.FockSpace σ h) :=
  fun η k => A05.rho h (A06.speciesOf branches η) k

/-- D on mode families: right changes sign; left is unchanged. -/
def dualFamily {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) : ModeFamily E :=
  fun η k => match η with
    | .right => -ρ .right k
    | .left => ρ .left k

noncomputable def dressedCreatorOf {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (c s : ℝ) (η : A06.Orientation) (m : ℕ) :
    Module.End ℂ E :=
  (c : ℂ) • ρ η (m : ℤ) +
    (s : ℂ) • ρ (A07Interactions.oppositeOrientation η) (-(m : ℤ))

noncomputable def dressedAnnihilatorOf {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (c s : ℝ) (η : A06.Orientation) (m : ℕ) :
    Module.End ℂ E :=
  (c : ℂ) • ρ η (-(m : ℤ)) +
    (s : ℂ) • ρ (A07Interactions.oppositeOrientation η) (m : ℤ)

/-- Term-for-term A07 pairing expression, with its original word order. -/
noncomputable def pairingModeOf {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (m : ℕ) (v1 v2 : ℝ) : Module.End ℂ E :=
  (v1 : ℂ) •
      (ρ .right (m : ℤ) * ρ .right (-(m : ℤ)) +
       ρ .left (m : ℤ) * ρ .left (-(m : ℤ))) +
    (v2 : ℂ) •
      (ρ .right (m : ℤ) * ρ .left (m : ℤ) +
       ρ .right (-(m : ℤ)) * ρ .left (-(m : ℤ)))

/-- Finite dressed phase of an arbitrary mode family; no self-adjoint claim. -/
noncomputable def chiralPhaseOf {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (c s : ℝ)
    (η : A06.Orientation) (x : ℤ) : Module.End ℂ E :=
  ∑ m ∈ Finset.Icc 1 M,
    ((m : ℂ)⁻¹) •
      (A01.integerCharacter (A01.canonicalRoot (2 * h))
          (-(A06.orientationSign η) * (m : ℤ)) x •
          dressedCreatorOf ρ c s η m +
       A01.integerCharacter (A01.canonicalRoot (2 * h))
          (A06.orientationSign η * (m : ℤ)) x •
          dressedAnnihilatorOf ρ c s η m)

noncomputable def xCDWOf {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (hp : Ch18.HyperbolicPair)
    (x : ℤ) : Module.End ℂ E :=
  ((hp.c - hp.s : ℝ) : ℂ) •
    (chiralPhaseOf ρ h M hp.c hp.s .right x +
      chiralPhaseOf ρ h M hp.c hp.s .left x)

noncomputable def xSCOf {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (hp : Ch18.HyperbolicPair)
    (x : ℤ) : Module.End ℂ E :=
  ((hp.c + hp.s : ℝ) : ℂ) •
    (chiralPhaseOf ρ h M hp.c hp.s .right x -
      chiralPhaseOf ρ h M hp.c hp.s .left x)

/-- D₁, a finite real-valued trigonometric kernel, not a correlator. -/
noncomputable def logKernel (h M : ℕ) (x y : ℤ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    (1 - Real.cos
      ((2 * Real.pi * (m : ℝ) * ((x - y : ℤ) : ℝ)) /
        ((2 * h : ℕ) : ℝ))) / (m : ℝ)

lemma dualPair_involutive (hp : Ch18.HyperbolicPair) :
    dualPair (dualPair hp) = hp := by
  cases hp with
  | mk c s hid => simp [dualPair]

/-- Indexed parameter records have different syntactic fibers; state involution
on the physical coordinates rather than an ill-typed heterogeneous equality. -/
lemma dualParams_involutive {v1 v2 : ℝ}
    (lp : A07Interactions.HyperbolicParams v1 v2) :
    (dualParams (dualParams lp)).u = lp.u ∧
    (dualParams (dualParams lp)).c = lp.c ∧
    (dualParams (dualParams lp)).s = lp.s := by
  simp [dualParams]

lemma luttingerG_dual (hp : Ch18.HyperbolicPair) :
    Ch18.luttingerG (dualPair hp) = Ch18.luttingerGInv hp := by
  simp [Ch18.luttingerG, Ch18.luttingerGInv, dualPair]

lemma luttingerGInv_dual (hp : Ch18.HyperbolicPair) :
    Ch18.luttingerGInv (dualPair hp) = Ch18.luttingerG hp := by
  dsimp [Ch18.luttingerG, Ch18.luttingerGInv, dualPair]
  ring

lemma dualParams_pair {v1 v2 : ℝ}
    (lp : A07Interactions.HyperbolicParams v1 v2) :
    Ch18.HyperbolicPair.ofParams (dualParams lp) =
      dualPair (Ch18.HyperbolicPair.ofParams lp) := by
  cases lp with
  | mk u c s up cp us hid mv1 mv2 =>
    simp [dualParams, Ch18.HyperbolicPair.ofParams, dualPair]

lemma v2Velocity_neg (g2 : ℝ) :
    Ch17.v2Velocity (-g2) = -Ch17.v2Velocity g2 := by
  simp [Ch17.v2Velocity]
  ring

/-- Exact bridge to the *current* ambient finite CAR density modes. -/
lemma dressedCreatorOf_species {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h m : ℕ) (c s : ℝ) (branches : A06.Branches σ)
    (η : A06.Orientation) :
    dressedCreatorOf (speciesFamily h branches) c s η m =
      A07Interactions.bogoliubovCreator h m c s branches η := by
  rfl

lemma dressedAnnihilatorOf_species {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h m : ℕ) (c s : ℝ) (branches : A06.Branches σ)
    (η : A06.Orientation) :
    dressedAnnihilatorOf (speciesFamily h branches) c s η m =
      A07Interactions.bogoliubovAnnihilator h m c s branches η := by
  rfl

lemma pairingModeOf_species {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h m : ℕ) (v1 v2 : ℝ) (branches : A06.Branches σ) :
    pairingModeOf (speciesFamily h branches) m v1 v2 =
      A07Interactions.pairingMode h m v1 v2 branches := by
  rfl

lemma dualFamily_involutive {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) :
    dualFamily (dualFamily ρ) = ρ := by
  funext η k
  cases η <;> simp [dualFamily]

/-- Cross commutators acquire a minus sign, even for arbitrary families. -/
lemma dual_commutator {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (η η' : A06.Orientation) (m n : ℤ) :
    A02.commutator (dualFamily ρ η m) (dualFamily ρ η' n) =
      (if η = η' then (1 : ℂ) else -1) •
        A02.commutator (ρ η m) (ρ η' n) := by
  cases η <;> cases η' <;> simp [dualFamily, A02.commutator]
  all_goals noncomm_ring

lemma dual_dressed_creator_right {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (c s : ℝ) (m : ℕ) :
    dressedCreatorOf (dualFamily ρ) c s .right m =
      -dressedCreatorOf ρ c (-s) .right m := by
  simp [dressedCreatorOf, dualFamily, A07Interactions.oppositeOrientation]
  abel

lemma dual_dressed_creator_left {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (c s : ℝ) (m : ℕ) :
    dressedCreatorOf (dualFamily ρ) c s .left m =
      dressedCreatorOf ρ c (-s) .left m := by
  simp [dressedCreatorOf, dualFamily, A07Interactions.oppositeOrientation]

lemma dual_dressed_annihilator_right {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (c s : ℝ) (m : ℕ) :
    dressedAnnihilatorOf (dualFamily ρ) c s .right m =
      -dressedAnnihilatorOf ρ c (-s) .right m := by
  simp [dressedAnnihilatorOf, dualFamily, A07Interactions.oppositeOrientation]
  abel

lemma dual_dressed_annihilator_left {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (c s : ℝ) (m : ℕ) :
    dressedAnnihilatorOf (dualFamily ρ) c s .left m =
      dressedAnnihilatorOf ρ c (-s) .left m := by
  simp [dressedAnnihilatorOf, dualFamily, A07Interactions.oppositeOrientation]

lemma dual_chiralPhase_right {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (c s : ℝ) (x : ℤ) :
    chiralPhaseOf (dualFamily ρ) h M c s .right x =
      -chiralPhaseOf ρ h M c (-s) .right x := by
  unfold chiralPhaseOf
  simp only [dual_dressed_creator_right, dual_dressed_annihilator_right]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [smul_neg]
  module

lemma dual_chiralPhase_left {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (c s : ℝ) (x : ℤ) :
    chiralPhaseOf (dualFamily ρ) h M c s .left x =
      chiralPhaseOf ρ h M c (-s) .left x := by
  unfold chiralPhaseOf
  simp only [dual_dressed_creator_left, dual_dressed_annihilator_left]

/-- The negative signs are fixed by φ = R+L and θ = R-L. -/
lemma dual_xCDW {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (hp : Ch18.HyperbolicPair) (x : ℤ) :
    xCDWOf (dualFamily ρ) h M hp x =
      -xSCOf ρ h M (dualPair hp) x := by
  simp only [xCDWOf, xSCOf, dual_chiralPhase_right, dual_chiralPhase_left, dualPair]
  module

lemma dual_xSC {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (h M : ℕ) (hp : Ch18.HyperbolicPair) (x : ℤ) :
    xSCOf (dualFamily ρ) h M hp x =
      -xCDWOf ρ h M (dualPair hp) x := by
  simp only [xCDWOf, xSCOf, dual_chiralPhase_right, dual_chiralPhase_left, dualPair]
  module

/-- Pairing-family substitution; *not* a finite-Fock spectral equivalence. -/
lemma dual_pairingMode {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ρ : ModeFamily E) (m : ℕ) (v1 v2 : ℝ) :
    pairingModeOf (dualFamily ρ) m v1 v2 =
      pairingModeOf ρ m v1 (-v2) := by
  simp [pairingModeOf, dualFamily]

/-- The chemical-potential-adjusted symmetric charge scalar transforms exactly. -/
lemma dual_symmetric_zero_mode {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h : ℕ) (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) :
    Ch17.symmetricZeroModeScalar h vF g4 g2 branches (reflectLeft branches Ns) =
      Ch17.symmetricZeroModeScalar h vF g4 (-g2) branches Ns := by
  have hne : branches.rightSpecies ≠ branches.leftSpecies := branches.distinct
  unfold Ch17.symmetricZeroModeScalar reflectLeft
  simp [Function.update, hne]
  ring

lemma dual_canonical_mu_zero_mode {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h : ℕ) (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) :
    Ch17.zeroModeEnergyScalar h vF g4 g2 (Ch17.canonicalMu h vF)
        branches (reflectLeft branches Ns) =
      Ch17.zeroModeEnergyScalar h vF g4 (-g2) (Ch17.canonicalMu h vF)
        branches Ns := by
  rw [Ch17.zero_mode_scalar_canonical_mu, Ch17.zero_mode_scalar_canonical_mu]
  exact dual_symmetric_zero_mode h vF g4 g2 branches Ns

lemma logKernel_self (h M : ℕ) (x : ℤ) :
    logKernel h M x x = 0 := by
  simp [logKernel]

lemma logKernel_symm (h M : ℕ) (x y : ℤ) :
    logKernel h M x y = logKernel h M y x := by
  unfold logKernel
  apply Finset.sum_congr rfl
  intro m hm
  apply congrArg (fun z : ℝ => (1-z)/(m:ℝ))
  have hd : ((y-x:ℤ):ℝ) = -((x-y:ℤ):ℝ) := by
    exact_mod_cast (show y - x = -(x-y) by omega)
  have hang :
      (2 * Real.pi * (m:ℝ) * ((x-y:ℤ):ℝ)) / ((2*h:ℕ):ℝ) =
      -(2 * Real.pi * (m:ℝ) * ((y-x:ℤ):ℝ) / ((2*h:ℕ):ℝ)) := by
    rw [hd]
    ring
  rw [hang, Real.cos_neg]

lemma logKernel_nonneg (h M : ℕ) (x y : ℤ) :
    0 ≤ logKernel h M x y := by
  unfold logKernel
  apply Finset.sum_nonneg
  intro m hm
  apply div_nonneg
  · exact sub_nonneg.mpr (Real.cos_le_one _)
  · exact Nat.cast_nonneg _

end ModeFamilyDuality

section DualityWitnesses

lemma concrete_luttingerG :
    Ch18.luttingerG Ch18.concretePair = (1 / 4 : ℝ) := by
  dsimp [Ch18.luttingerG, Ch18.concretePair,
    Ch18.HyperbolicPair.ofParams, Ch18.concreteParams]
  norm_num

lemma concrete_luttingerG_dual :
    Ch18.luttingerG (dualPair Ch18.concretePair) = (4 : ℝ) := by
  dsimp [Ch18.luttingerG, dualPair, Ch18.concretePair,
    Ch18.HyperbolicPair.ofParams, Ch18.concreteParams]
  norm_num

lemma concrete_dualPair_ne :
    dualPair Ch18.concretePair ≠ Ch18.concretePair := by
  intro he
  have hs := congrArg Ch18.HyperbolicPair.s he
  dsimp [dualPair] at hs
  have hne : Ch18.concretePair.s ≠ 0 := by
    dsimp [Ch18.concretePair, Ch18.HyperbolicPair.ofParams,
      Ch18.concreteParams]
    norm_num
  exact hne (by linarith)

/-- A nontrivial v₂ = 15 pairing term changes on the actual finite Fock ket. -/
lemma concrete_pairing_duality_nontrivial :
    pairingModeOf (speciesFamily 8 Ch16.standardBranches) 1 17 15
        (A05.groundKet 8 Ch18.concreteNs) ≠
      pairingModeOf (speciesFamily 8 Ch16.standardBranches) 1 17 (-15)
        (A05.groundKet 8 Ch18.concreteNs) := by
  have hN : A05.admissible 8 Ch18.concreteNs := by
    intro ν
    simp [Ch07.admissible, Ch18.concreteNs]
  have hmarg : A06.branchMargins 8 1 1 Ch18.concreteNs Ch16.standardBranches := by
    norm_num [A06.branchMargins, A06.marginAt, Ch18.concreteNs, Ch16.standardBranches]
  let D := A05.rho 8 Ch16.standardBranches.rightSpecies 1 *
      A05.rho 8 Ch16.standardBranches.rightSpecies (-1) +
    A05.rho 8 Ch16.standardBranches.leftSpecies 1 *
      A05.rho 8 Ch16.standardBranches.leftSpecies (-1)
  let Q := A05.rho 8 Ch16.standardBranches.rightSpecies 1 *
      A05.rho 8 Ch16.standardBranches.leftSpecies 1 +
    A05.rho 8 Ch16.standardBranches.rightSpecies (-1) *
      A05.rho 8 Ch16.standardBranches.leftSpecies (-1)
  have hQ : Q (A05.groundKet 8 Ch18.concreteNs) ≠ 0 := by
    dsimp [Q]
    exact A07Interactions.pairing_mode_ground_nonzero 8 1 1 (by norm_num) (by norm_num)
      (by norm_num) Ch18.concreteNs hN Ch16.standardBranches hmarg
  intro heq
  have heq' : (17:ℂ) • D (A05.groundKet 8 Ch18.concreteNs) +
        (15:ℂ) • Q (A05.groundKet 8 Ch18.concreteNs) =
      (17:ℂ) • D (A05.groundKet 8 Ch18.concreteNs) +
        (-15:ℂ) • Q (A05.groundKet 8 Ch18.concreteNs) := by
    simpa [D, Q, pairingModeOf, speciesFamily, A06.speciesOf] using heq
  have hz : (30:ℂ) • Q (A05.groundKet 8 Ch18.concreteNs) = 0 := by
    calc
      (30:ℂ) • Q (A05.groundKet 8 Ch18.concreteNs) =
          ((17:ℂ) • D (A05.groundKet 8 Ch18.concreteNs) +
            (15:ℂ) • Q (A05.groundKet 8 Ch18.concreteNs)) -
          ((17:ℂ) • D (A05.groundKet 8 Ch18.concreteNs) +
            (-15:ℂ) • Q (A05.groundKet 8 Ch18.concreteNs)) := by module
      _ = 0 := by rw [heq']; abel
  exact hQ ((smul_eq_zero.mp hz).resolve_left (by norm_num))

lemma concrete_logKernel : logKernel 2 1 1 0 = 1 := by
  unfold logKernel
  norm_num [show (2 * Real.pi / 4 : ℝ) = Real.pi / 2 by ring,
    Real.cos_pi_div_two]

/-- The *unadjusted* linear-μ term breaks the purported dual zero-mode law. -/
lemma concrete_linear_mu_counterexample :
    Ch17.zeroModeEnergyScalar 1 1 0 0 1 Ch16.standardBranches
        (![0, 1] : Fin 2 → ℤ) ≠
      Ch17.zeroModeEnergyScalar 1 1 0 0 1 Ch16.standardBranches
        (![0, -1] : Fin 2 → ℤ) := by
  intro hEq
  have hRed := hEq
  norm_num [Ch17.zeroModeEnergyScalar, Ch16.standardBranches] at hRed
  have hpi : Real.pi = 2 := by linarith
  have hc : Real.cos 1 = 0 := by
    simpa [hpi] using Real.cos_pi_div_two
  exact (ne_of_gt Real.cos_one_pos) hc

end DualityWitnesses

end Bosonize.Ch20
