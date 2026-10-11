module

public import Bosonize.Core.A05MultiSpecies

/-! CH13: explicit finite Gram-kernel Klein operators on the actual CAR carrier.
Complete finite data with proved typed budget isometries and intertwining squares. -/
@[expose] public section
namespace Bosonize.Ch13
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable local instance localModeLinearOrder (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.speciesOrder h
noncomputable local instance localModeLT (h : ℕ) : LT (A05.Mode σ h) := (A05.speciesOrder h).toLT
noncomputable local instance localModeLE (h : ℕ) : LE (A05.Mode σ h) := (A05.speciesOrder h).toLE
noncomputable local instance localModeDecidableEq (h : ℕ) : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq

abbrev FockSpace (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A05.FockSpace σ h
abbrev Operators (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A05.Operators σ h

def lowerCharge (Ns : σ → ℤ) (ν : σ) : σ → ℤ := Function.update Ns ν (Ns ν-1)

def phaseExponent (h : ℕ) (Ns : σ → ℤ) (ν : σ) : ℤ :=
  (∑ η ∈ Finset.univ.filter (· < ν), ((h : ℤ)+Ns η)) + ((h : ℤ)+Ns ν-1)

noncomputable def kleinPhase (h : ℕ) (Ns : σ → ℤ) (ν : σ) : ℂ :=
  (-1 : ℂ) ^ phaseExponent h Ns ν

def pairMargin (h K : ℕ) (Ns : σ → ℤ) (ν : σ) : Prop :=
  A05.r2 h K Ns ∧ A05.r2 h K (lowerCharge Ns ν)

def fourSectorMargin (h K : ℕ) (Ns : σ → ℤ) (ν η : σ) : Prop :=
  A05.r2 h K Ns ∧ A05.r2 h K (lowerCharge Ns ν) ∧
    A05.r2 h K (lowerCharge Ns η) ∧ A05.r2 h K (lowerCharge (lowerCharge Ns ν) η)

/-- Positive normalization is proved in A05; this data definition does not assume it. -/
noncomputable def kleinKernel (h : ℕ) (Ns : σ → ℤ) (ν : σ) (K : ℕ) : Operators σ h :=
  ∑ p : A05.JointPartitions σ K,
    (kleinPhase h Ns ν / (A05.jointNormalization p : ℂ)) •
      ((innerₛₗ ℂ (A05.partitionState h Ns p)).smulRight
        (A05.partitionState h (lowerCharge Ns ν) p))

/-- The inverse kernel uses the conjugate SOURCE phase and reversed rank-one factors. -/
noncomputable def inverseKernel (h : ℕ) (Ns : σ → ℤ) (ν : σ) (K : ℕ) : Operators σ h :=
  ∑ p : A05.JointPartitions σ K,
    (star (kleinPhase h Ns ν) / (A05.jointNormalization p : ℂ)) •
      ((innerₛₗ ℂ (A05.partitionState h (lowerCharge Ns ν) p)).smulRight
        (A05.partitionState h Ns p))

/-- A complete map from the actual source subtype to the ambient target carrier.
Codomain membership and isometry are proved contracts, not data certificates. -/
noncomputable def kleinFromBudget (h : ℕ) (Ns : σ → ℤ) (ν : σ) (K : ℕ) :
    A05.jointBudget h Ns K →ₗ[ℂ] FockSpace σ h :=
  (kleinKernel h Ns ν K).comp (A05.jointBudget h Ns K).subtype

omit [Fintype σ] in
lemma lower_charge_commute (Ns : σ → ℤ) (ν η : σ) (hne : ν≠η) :
    lowerCharge (lowerCharge Ns ν) η = lowerCharge (lowerCharge Ns η) ν := by
  funext γ
  by_cases hγν : γ=ν
  · subst γ
    simp [lowerCharge, hne, Ne.symm hne]
  · by_cases hγη : γ=η
    · subst γ
      simp [lowerCharge, hne, Ne.symm hne]
    · simp [lowerCharge, hγν, hγη]

lemma phase_norm (h : ℕ) (Ns : σ → ℤ) (ν : σ) : ‖kleinPhase h Ns ν‖ = 1 := by
  simp [kleinPhase, norm_zpow]

lemma phase_cross_sign (h : ℕ) (Ns : σ → ℤ) (ν η : σ) (hne : ν≠η) :
    kleinPhase h (lowerCharge Ns ν) η * kleinPhase h Ns ν =
      -(kleinPhase h (lowerCharge Ns η) ν * kleinPhase h Ns η) := by
  have hshift (a b : σ) (hab : a≠b) :
      phaseExponent h (lowerCharge Ns a) b = phaseExponent h Ns b - (if a<b then 1 else 0) := by
    have hpoint (γ : σ) : (h : ℤ)+lowerCharge Ns a γ = (h : ℤ)+Ns γ - (if γ=a then 1 else 0) := by
      by_cases hγ : γ=a
      · subst γ
        simp [lowerCharge]
        ring
      · simp [lowerCharge, hγ]
    simp only [phaseExponent]
    simp only [hpoint, Finset.sum_sub_distrib]
    simp [Ne.symm hab]
    ring
  have hphase (a b : σ) (hab : a≠b) :
      kleinPhase h (lowerCharge Ns a) b = if a<b then -kleinPhase h Ns b else kleinPhase h Ns b := by
    unfold kleinPhase
    rw [hshift a b hab]
    by_cases hlt : a<b
    · simp only [hlt, ite_true]
      rw [zpow_sub₀ (by norm_num : (-1 : ℂ)≠0)]
      simp [div_neg, div_one]
    · simp [hlt]
  rw [hphase ν η hne, hphase η ν hne.symm]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · simp only [hlt, not_lt_of_gt hlt, ite_true, ite_false]
    ring
  · simp only [hgt, not_lt_of_gt hgt, ite_true, ite_false]
    ring

omit [Fintype σ] [LinearOrder σ] in
lemma r2_admissible (h K : ℕ) (Ns : σ → ℤ) (hR2 : A05.r2 h K Ns) :
    A05.admissible h Ns := by
  intro ν
  have hm := hR2 ν
  have hn := le_abs_self (Ns ν)
  have hl := neg_le_abs (Ns ν)
  constructor <;> omega

/-- Actual lexicographic CAR ground coefficient includes both sign contributions. -/
lemma ground_top_annihilation (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (ν : σ) (hν : -(h : ℤ)+1 ≤ Ns ν)
    (k : Ch01.Band (2*h)) (hk : k.val=Ns ν) :
    A05.annihilation h ν k (A05.groundKet h Ns) =
      kleinPhase h Ns ν • A05.groundKet h (lowerCharge Ns ν) := by
  classical
  have hmem (η : σ) (l : Ch01.Band (2*h)) :
      (η,l) ∈ A05.groundConfiguration h Ns ↔ l.val ≤ Ns η := by
    simp only [A05.groundConfiguration, A05.jointConfiguration, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_image, Ch07.groundConfiguration,
      Finset.mem_filter]
    aesop
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
    simp only [Ch07.groundConfiguration, Finset.mem_filter, Finset.mem_univ, true_and,
      ]
    change (l.val ≤ Ns ν ∧ l.val < k.val) ↔ l.val ≤ Ns ν-1
    rw [hk]
    omega
  have hc : ((Ch04.precedingCount (ν,k) (A05.groundConfiguration h Ns) : ℕ) : ℤ) =
      phaseExponent h Ns ν := by
    rw [A05.preceding_count_split]
    simp only [hcomp, Nat.cast_add, Nat.cast_sum]
    simp_rw [Ch07.ground_configuration_card h hh _ (hN _)]
    unfold Ch04.precedingCount
    rw [ht, Ch07.ground_configuration_card h hh _ hlow]
    simp only [phaseExponent]
    ring
  have hsign : Ch04.fermionSign (ν,k) (A05.groundConfiguration h Ns) =
      kleinPhase h Ns ν := by
    unfold Ch04.fermionSign kleinPhase
    rw [← zpow_natCast, hc]
  have herase : (A05.groundConfiguration h Ns).erase (ν,k) =
      A05.groundConfiguration h (lowerCharge Ns ν) := by
    ext p
    obtain ⟨η,l⟩ := p
    have hm2 : (η,l) ∈ A05.groundConfiguration h (lowerCharge Ns ν) ↔
        l.val ≤ lowerCharge Ns ν η := by
      simp only [A05.groundConfiguration, A05.jointConfiguration, Finset.mem_biUnion,
        Finset.mem_univ, true_and, Finset.mem_image, Ch07.groundConfiguration,
        Finset.mem_filter]
      aesop
    rw [Finset.mem_erase, hmem, hm2]
    by_cases he : η = ν
    · subst η
      simp only [lowerCharge, Function.update_self]
      simp only [ne_eq, Prod.mk.injEq, true_and]
      have hlk : l = k ↔ l.val = Ns ν := by
        constructor
        · rintro rfl; exact hk
        · intro heq; apply Subtype.ext; exact heq.trans hk.symm
      rw [hlk]
      omega
    · simp [lowerCharge, he]
  unfold A05.annihilation A05.groundKet
  rw [Ch04.annihilation_ket, ite_eq_left ((hmem ν k).mpr (by omega)), hsign, herase]

lemma ground_field_coefficient (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (ν : σ) (hν : -(h : ℤ)+1 ≤ Ns ν)
    (b : σ → Ch06Ext.BoundaryTwist (2*h)) (x : ℤ) :
    inner ℂ (A05.groundKet h (lowerCharge Ns ν))
      (A05.liftedAnnihilation h b ν x (A05.groundKet h Ns)) =
      (A01.normalization (2*h) : ℂ) * kleinPhase h Ns ν *
        Ch06Ext.liftPhase (2*h) (b ν) x * A01.canonicalRoot (2*h)^(x*Ns ν) := by
  classical
  let kt : Ch01.Band (2*h) := ⟨Ns ν, by
    unfold Ch01.inBandPredicate
    obtain ⟨hl, hu⟩ := hN ν
    push_cast
    constructor <;> omega⟩
  have hkt : kt.val = Ns ν := rfl
  have hmem (Ms : σ → ℤ) (η : σ) (l : Ch01.Band (2*h)) :
      (η,l) ∈ A05.groundConfiguration h Ms ↔ l.val ≤ Ms η := by
    simp only [A05.groundConfiguration, A05.jointConfiguration, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_image, Ch07.groundConfiguration,
      Finset.mem_filter]
    aesop
  have hc (k : Ch01.Band (2*h)) :
      inner ℂ (A05.groundKet h (lowerCharge Ns ν))
        (A05.annihilation h ν k (A05.groundKet h Ns)) =
        if k = kt then kleinPhase h Ns ν else 0 := by
    by_cases he : k = kt
    · subst k
      rw [ground_top_annihilation h hh Ns hN ν hν kt hkt]
      simp [A05.groundKet, inner_smul_right, A02.ket_norm]
    · have hne : A05.groundConfiguration h (lowerCharge Ns ν) ≠
          (A05.groundConfiguration h Ns).erase (ν,k) := by
        intro heq
        have htmem : (ν,kt) ∈ (A05.groundConfiguration h Ns).erase (ν,k) := by
          apply Finset.mem_erase.mpr
          constructor
          · intro hh
            have hk : kt = k := (Prod.mk.inj hh).2
            exact he hk.symm
          · exact (hmem Ns ν kt).mpr (by rw [hkt])
        rw [← heq] at htmem
        have hb := (hmem (lowerCharge Ns ν) ν kt).mp htmem
        simp only [lowerCharge, Function.update_self, hkt] at hb
        omega
      unfold A05.annihilation A05.groundKet
      rw [Ch04.annihilation_ket]
      split_ifs <;> simp [inner_smul_right, A02.ket_inner, hne]
  unfold A05.liftedAnnihilation
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, inner_smul_right, inner_sum]
  simp_rw [hc]
  rw [Finset.sum_eq_single kt]
  · simp only [ite_true]
    unfold Ch06Ext.twistedCharacter A01.integerCharacter
    rw [hkt]
    ring
  · intro k _ hne
    simp [hne]
  · simp

lemma kernel_partition (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hR2 : A05.r2 h K Ns) (p : A05.JointPartitions σ K) :
    kleinKernel h Ns ν K (A05.partitionState h Ns p) =
      kleinPhase h Ns ν • A05.partitionState h (lowerCharge Ns ν) p := by
  have hn : (A05.jointNormalization p : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (A05.joint_normalization_positive K p))
  simp only [kleinKernel, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply]
  simp_rw [A05.partition_gram h hh Ns (r2_admissible h K Ns hR2) K hR2]
  rw [Finset.sum_eq_single p]
  · simp only [ite_true]
    rw [smul_smul, div_mul_cancel₀ _ hn]
  · intro q _ hqp
    simp [hqp]
  · simp

lemma inverse_partition (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hR2 : A05.r2 h K (lowerCharge Ns ν)) (p : A05.JointPartitions σ K) :
    inverseKernel h Ns ν K (A05.partitionState h (lowerCharge Ns ν) p) =
      star (kleinPhase h Ns ν) • A05.partitionState h Ns p := by
  have hn : (A05.jointNormalization p : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (A05.joint_normalization_positive K p))
  simp only [inverseKernel, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply]
  simp_rw [A05.partition_gram h hh (lowerCharge Ns ν)
    (r2_admissible h K _ hR2) K hR2]
  rw [Finset.sum_eq_single p]
  · simp only [ite_true]
    rw [smul_smul, div_mul_cancel₀ _ hn]
  · intro q _ hqp
    simp [hqp]
  · simp

lemma kernel_maps_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hN : A05.admissible h (lowerCharge Ns ν)) (v : FockSpace σ h) :
    kleinKernel h Ns ν K v ∈ A05.jointBudget h (lowerCharge Ns ν) K := by
  simp only [kleinKernel, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply]
  apply Submodule.sum_mem
  intro p _
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  exact A05.partition_mem_budget h hh _ hN K p

lemma inverse_maps_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hN : A05.admissible h Ns) (v : FockSpace σ h) :
    inverseKernel h Ns ν K v ∈ A05.jointBudget h Ns K := by
  simp only [inverseKernel, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply]
  apply Submodule.sum_mem
  intro p _
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  exact A05.partition_mem_budget h hh _ hN K p

lemma kernel_inner_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) (v w : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) (hw : w ∈ A05.jointBudget h Ns K) :
    inner ℂ (kleinKernel h Ns ν K v) (kleinKernel h Ns ν K w) = inner ℂ v w := by
  have hp : kleinPhase h Ns ν * star (kleinPhase h Ns ν) = 1 := by
    simpa [phase_norm] using Complex.mul_conj' (kleinPhase h Ns ν)
  have hNs := r2_admissible h K Ns hm.1
  have hNt := r2_admissible h K (lowerCharge Ns ν) hm.2
  have hg (p q : A05.JointPartitions σ K) :
      inner ℂ (kleinKernel h Ns ν K (A05.partitionState h Ns p))
        (kleinKernel h Ns ν K (A05.partitionState h Ns q)) =
      inner ℂ (A05.partitionState h Ns p) (A05.partitionState h Ns q) := by
    rw [kernel_partition h hh Ns ν K hm.1 p, kernel_partition h hh Ns ν K hm.1 q,
      inner_smul_left, inner_smul_right,
      A05.partition_gram h hh (lowerCharge Ns ν) hNt K hm.2,
      A05.partition_gram h hh Ns hNs K hm.1]
    simp only [starRingEnd_apply]
    rw [← mul_assoc, mul_comm (star (kleinPhase h Ns ν)), hp, one_mul]
  rw [← A05.partition_spanning h hh Ns hNs K hm.1] at hv hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨p,rfl⟩
    induction hw using Submodule.span_induction with
    | mem y hy => rcases hy with ⟨q,rfl⟩; exact hg p q
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, inner_add_right, hx, hy]
    | smul a x _ hx => simp only [map_smul, inner_smul_right, hx]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, inner_add_left, hx, hy]
  | smul a x _ hx => simp only [map_smul, inner_smul_left, hx]

lemma inverse_kernel_source (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) (v : FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    inverseKernel h Ns ν K (kleinKernel h Ns ν K v) = v := by
  have hp : kleinPhase h Ns ν * star (kleinPhase h Ns ν) = 1 := by
    simpa [phase_norm] using Complex.mul_conj' (kleinPhase h Ns ν)
  obtain ⟨b, hb⟩ := A05.partition_basis h hh (Ns) (r2_admissible h K (Ns) hm.1) K hm.1
  let F : A05.jointBudget h (Ns) K →ₗ[ℂ] FockSpace σ h :=
    ((inverseKernel h Ns ν K).comp (kleinKernel h Ns ν K)).comp (A05.jointBudget h (Ns) K).subtype
  have he : F = (A05.jointBudget h (Ns) K).subtype := by
    apply b.ext
    intro p
    change inverseKernel h Ns ν K (kleinKernel h Ns ν K (b p : FockSpace σ h)) = (b p : FockSpace σ h)
    rw [hb p, kernel_partition h hh Ns ν K hm.1 p, map_smul, inverse_partition h hh Ns ν K hm.2 p, smul_smul]
    simpa [mul_comm] using congrArg (fun a : ℂ => a • A05.partitionState h (Ns) p) hp
  exact LinearMap.congr_fun he ⟨v,hv⟩

lemma kernel_inverse_target (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h (lowerCharge Ns ν) K) :
    kleinKernel h Ns ν K (inverseKernel h Ns ν K v) = v := by
  have hp : kleinPhase h Ns ν * star (kleinPhase h Ns ν) = 1 := by
    simpa [phase_norm] using Complex.mul_conj' (kleinPhase h Ns ν)
  obtain ⟨b, hb⟩ := A05.partition_basis h hh (lowerCharge Ns ν) (r2_admissible h K (lowerCharge Ns ν) hm.2) K hm.2
  let F : A05.jointBudget h (lowerCharge Ns ν) K →ₗ[ℂ] FockSpace σ h :=
    ((kleinKernel h Ns ν K).comp (inverseKernel h Ns ν K)).comp (A05.jointBudget h (lowerCharge Ns ν) K).subtype
  have he : F = (A05.jointBudget h (lowerCharge Ns ν) K).subtype := by
    apply b.ext
    intro p
    change kleinKernel h Ns ν K (inverseKernel h Ns ν K (b p : FockSpace σ h)) = (b p : FockSpace σ h)
    rw [hb p, inverse_partition h hh Ns ν K hm.2 p, map_smul, kernel_partition h hh Ns ν K hm.1 p, smul_smul]
    simpa [mul_comm] using congrArg (fun a : ℂ => a • A05.partitionState h (lowerCharge Ns ν) p) hp
  exact LinearMap.congr_fun he ⟨v,hv⟩

lemma kernel_adjoint (h : ℕ) (Ns : σ → ℤ) (ν : σ) (K : ℕ) :
    LinearMap.adjoint (kleinKernel h Ns ν K) = inverseKernel h Ns ν K := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [inverseKernel, kleinKernel, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply, inner_sum, sum_inner,
    inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro p _
  simp [inner_conj_symm, mul_comm]

/-- Surjective typed budget isometry, canonically realized by the explicit kernel. -/
theorem klein_isometry_equiv (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) :
    ∃ F : A05.jointBudget h Ns K ≃ₗᵢ[ℂ] A05.jointBudget h (lowerCharge Ns ν) K,
      ∀ v, (F v : FockSpace σ h) = kleinKernel h Ns ν K v := by
  let f : A05.jointBudget h Ns K →ₗ[ℂ] A05.jointBudget h (lowerCharge Ns ν) K :=
    ((kleinKernel h Ns ν K).comp (A05.jointBudget h Ns K).subtype).codRestrict
      (A05.jointBudget h (lowerCharge Ns ν) K)
      (fun v => kernel_maps_budget h hh Ns ν K (r2_admissible h K (lowerCharge Ns ν) hm.2) v)
  let g : A05.jointBudget h (lowerCharge Ns ν) K →ₗ[ℂ] A05.jointBudget h Ns K :=
    ((inverseKernel h Ns ν K).comp (A05.jointBudget h (lowerCharge Ns ν) K).subtype).codRestrict
      (A05.jointBudget h Ns K)
      (fun v => inverse_maps_budget h hh Ns ν K (r2_admissible h K Ns hm.1) v)
  let e : A05.jointBudget h Ns K ≃ₗ[ℂ] A05.jointBudget h (lowerCharge Ns ν) K :=
    { f with
      invFun := g
      left_inv := by
        intro v
        apply Subtype.ext
        exact inverse_kernel_source h hh Ns ν K hm v v.property
      right_inv := by
        intro v
        apply Subtype.ext
        exact kernel_inverse_target h hh Ns ν K hm v v.property }
  refine ⟨{ e with norm_map' := ?_ }, ?_⟩
  · intro v
    change ‖kleinKernel h Ns ν K v‖ = ‖(v : FockSpace σ h)‖
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      kernel_inner_budget h hh Ns ν K hm v v v.property v.property]
  · intro v
    rfl

lemma kernel_cutoff_consistent (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K J : ℕ)
    (hKJ : K≤J) (hm : pairMargin h J Ns ν) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) :
    kleinKernel h Ns ν J v = kleinKernel h Ns ν K v := by
  have hsmall : A05.r2 h K Ns := by
    intro η
    have hj := hm.1 η
    have hkj : (K : ℤ) ≤ J := by exact_mod_cast hKJ
    omega
  rw [← A05.partition_spanning h hh Ns (r2_admissible h K Ns hsmall) K hsmall] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    let q : A05.JointPartitions σ J := ⟨fun η =>
      ⟨⟨(p.val η).1.val, by have hp := (p.val η).1.isLt; omega⟩, (p.val η).2⟩,
      by exact le_trans p.property hKJ⟩
    have hq (Ms : σ → ℤ) : A05.partitionState h Ms q = A05.partitionState h Ms p := rfl
    rw [← hq Ns, kernel_partition h hh Ns ν J hm.1 q, hq]
    rw [hq Ns, kernel_partition h hh Ns ν K hsmall p]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, hx]

lemma kernel_raising_intertwine (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (K m : ℕ) (hmpos : 0<m)
    (hm : pairMargin h (K+m) Ns ν) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) :
    kleinKernel h Ns ν (K+m) (A05.rho h η (m : ℤ) v) =
      A05.rho h η (m : ℤ) (kleinKernel h Ns ν K v) := by
  have hsrc := r2_admissible h (K+m) Ns hm.1
  have htgt := r2_admissible h (K+m) (lowerCharge Ns ν) hm.2
  have hsmall : A05.r2 h K Ns := by
    intro γ
    have hg := hm.1 γ
    omega
  rw [← A05.partition_spanning h hh Ns hsrc K hsmall] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    let E := (p.val η).1.val
    let np : Nat.Partition (E+m) :=
      { parts := m ::ₘ (p.val η).2.parts
        parts_pos := by
          intro i hi
          rcases Multiset.mem_cons.mp hi with hi | hi
          · subst i; exact hmpos
          · exact (p.val η).2.parts_pos hi
        parts_sum := by simp [E, (p.val η).2.parts_sum, Nat.add_comm] }
    let qp : σ → Ch11.BudgetPartitions (K+m) := fun γ =>
      if γ=η then ⟨⟨E+m, by have he := (p.val η).1.isLt; omega⟩, np⟩
      else ⟨⟨(p.val γ).1.val, by have he := (p.val γ).1.isLt; omega⟩, (p.val γ).2⟩
    have he (γ : σ) : (qp γ).1.val = (p.val γ).1.val + if γ=η then m else 0 := by
      by_cases hg : γ=η
      · subst γ; simp [qp, E]
      · simp [qp, hg]
    let q : A05.JointPartitions σ (K+m) := ⟨qp, by
      simp_rw [he]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact Nat.add_le_add_right p.property m⟩
    have hlist (γ : σ) : Ch11.partitionList (q.val γ).2 =
        if γ=η then Ch11.partitionList np else Ch11.partitionList (p.val γ).2 := by
      by_cases hg : γ=η
      · have heq : q.val γ = (⟨⟨E+m, by have he := (p.val η).1.isLt; omega⟩, np⟩ :
            Ch11.BudgetPartitions (K+m)) := by
          simp only [q, qp, ite_eq_left hg]
        rw [ite_eq_left hg]
        exact congrArg (fun b : Ch11.BudgetPartitions (K+m) => b.2.parts.sort (· ≥ ·)) heq
      · have heq : q.val γ = (⟨⟨(p.val γ).1.val, by have he := (p.val γ).1.isLt; omega⟩, (p.val γ).2⟩ :
            Ch11.BudgetPartitions (K+m)) := by
          simp only [q, qp, ite_eq_right hg]
        rw [ite_eq_right hg]
        exact congrArg (fun b : Ch11.BudgetPartitions (K+m) => b.2.parts.sort (· ≥ ·)) heq
    have hstate (Ms : σ → ℤ) (hMs : A05.admissible h Ms) :
        A05.rho h η (m : ℤ) (A05.partitionState h Ms p) = A05.partitionState h Ms q := by
      unfold A05.partitionState
      rw [A05.word_tensor h Ms hMs, A05.rho_tensor, A05.word_tensor h Ms hMs]
      congr 1
      funext γ
      rw [hlist]
      by_cases hg : γ=η
      · subst γ
        simp only [Function.update_self]
        change Ch09.rho h (m : ℤ) (Ch11.wordState h (Ms η) (hMs η)
          (Ch11.partitionList (p.val η).2)) =
          Ch11.wordState h (Ms η) (hMs η) (Ch11.partitionList np)
        have hnp := Ch11.partition_state_order_independent h (Ms η) (hMs η) np
          (m :: Ch11.partitionList (p.val η).2)
          (by
            change m ::ₘ (Ch11.partitionList (p.val η).2 : Multiset ℕ) = np.parts
            rw [Ch11.partition_list_multiset])
        rw [Ch11.word_state_cons] at hnp
        exact hnp
      · simp [hg]
    rw [hstate Ns hsrc, kernel_partition h hh Ns ν (K+m) hm.1 q,
      kernel_partition h hh Ns ν K hsmall p, map_smul, hstate (lowerCharge Ns ν) htgt]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, hx]

lemma kernel_lowering_intertwine (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (K m : ℕ) (hmpos : 0<m)
    (hm : pairMargin h (K+m) Ns ν) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns (K+m)) :
    kleinKernel h Ns ν K (A05.rho h η (-(m : ℤ)) v) =
      A05.rho h η (-(m : ℤ)) (kleinKernel h Ns ν (K+m) v) := by
  have hm0 : pairMargin h K Ns ν := by
    constructor
    · intro γ
      have hc := hm.1 γ
      omega
    · intro γ
      have hc := hm.2 γ
      omega
  have hNt := r2_admissible h (K+m) (lowerCharge Ns ν) hm.2
  have hlow : A05.rho h η (-(m : ℤ)) v ∈ A05.jointBudget h Ns K := by
    have hx := A05.rho_budget_map h η (-(m : ℤ)) Ns (K+m) v hv
    simpa [A05.jointBudget, Nat.cast_add] using hx
  have hL := kernel_maps_budget h hh Ns ν K hNt (A05.rho h η (-(m : ℤ)) v)
  have hhigh := kernel_maps_budget h hh Ns ν (K+m) hNt v
  have hR : A05.rho h η (-(m : ℤ)) (kleinKernel h Ns ν (K+m) v) ∈
      A05.jointBudget h (lowerCharge Ns ν) K := by
    have hx := A05.rho_budget_map h η (-(m : ℤ)) (lowerCharge Ns ν) (K+m)
      (kleinKernel h Ns ν (K+m) v) hhigh
    simpa [A05.jointBudget, Nat.cast_add] using hx
  obtain ⟨F0,hF0⟩ := klein_isometry_equiv h hh Ns ν K hm0
  have he : (⟨kleinKernel h Ns ν K (A05.rho h η (-(m : ℤ)) v),hL⟩ :
      A05.jointBudget h (lowerCharge Ns ν) K) =
      ⟨A05.rho h η (-(m : ℤ)) (kleinKernel h Ns ν (K+m) v),hR⟩ := by
    apply ext_inner_left ℂ
    intro w
    obtain ⟨u,rfl⟩ := F0.surjective w
    change inner ℂ (F0 u : FockSpace σ h)
        (kleinKernel h Ns ν K (A05.rho h η (-(m : ℤ)) v)) =
      inner ℂ (F0 u : FockSpace σ h)
        (A05.rho h η (-(m : ℤ)) (kleinKernel h Ns ν (K+m) v))
    rw [hF0 u]
    have huplus : A05.rho h η (m : ℤ) u ∈ A05.jointBudget h Ns (K+m) := by
      have hx := A05.rho_budget_map h η (m : ℤ) Ns K u u.property
      simpa [A05.jointBudget, Nat.cast_add] using hx
    calc
      _ = inner ℂ (u : FockSpace σ h) (A05.rho h η (-(m : ℤ)) v) :=
        kernel_inner_budget h hh Ns ν K hm0 u _ u.property hlow
      _ = inner ℂ (A05.rho h η (m : ℤ) u) v := by
        rw [← A05.rho_adjoint h η (m : ℤ), LinearMap.adjoint_inner_right]
      _ = inner ℂ (kleinKernel h Ns ν (K+m) (A05.rho h η (m : ℤ) u))
          (kleinKernel h Ns ν (K+m) v) :=
        (kernel_inner_budget h hh Ns ν (K+m) hm _ v huplus hv).symm
      _ = inner ℂ (A05.rho h η (m : ℤ) (kleinKernel h Ns ν K u))
          (kleinKernel h Ns ν (K+m) v) := by
        rw [kernel_raising_intertwine h hh Ns ν η K m hmpos hm u u.property]
      _ = _ := by
        rw [← A05.rho_adjoint h η (m : ℤ), LinearMap.adjoint_inner_right]
  exact congrArg Subtype.val he

/-- Both horizontal arrows and both density arrows are actual typed maps,
identified pointwise with the complete finite operators above. -/
theorem klein_raising_square (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (K m : ℕ) (hmpos : 0<m)
    (hm : pairMargin h (K+m) Ns ν) :
    ∃ F0 : A05.jointBudget h Ns K ≃ₗᵢ[ℂ] A05.jointBudget h (lowerCharge Ns ν) K,
    ∃ F1 : A05.jointBudget h Ns (K+m) ≃ₗᵢ[ℂ] A05.jointBudget h (lowerCharge Ns ν) (K+m),
    ∃ R0 : A05.jointBudget h Ns K →ₗ[ℂ] A05.jointBudget h Ns (K+m),
    ∃ R1 : A05.jointBudget h (lowerCharge Ns ν) K →ₗ[ℂ] A05.jointBudget h (lowerCharge Ns ν) (K+m),
      (∀ v, (F0 v : FockSpace σ h)=kleinKernel h Ns ν K v) ∧
      (∀ v, (F1 v : FockSpace σ h)=kleinKernel h Ns ν (K+m) v) ∧
      (∀ v, (R0 v : FockSpace σ h)=A05.rho h η (m : ℤ) v) ∧
      (∀ v, (R1 v : FockSpace σ h)=A05.rho h η (m : ℤ) v) ∧
      F1.toLinearMap.comp R0 = R1.comp F0.toLinearMap := by
  have hm0 : pairMargin h K Ns ν := by
    constructor
    · intro γ; have ht := hm.1 γ; push_cast at ht; omega
    · intro γ; have ht := hm.2 γ; push_cast at ht; omega
  obtain ⟨F0, hF0⟩ := klein_isometry_equiv h hh Ns ν K hm0
  obtain ⟨F1, hF1⟩ := klein_isometry_equiv h hh Ns ν (K+m) hm
  let R0 : A05.jointBudget h Ns K →ₗ[ℂ] A05.jointBudget h Ns (K+m) :=
    ((A05.rho h η (m : ℤ)).comp (A05.jointBudget h Ns K).subtype).codRestrict _
      (fun v => by simpa [A05.jointBudget, Nat.cast_add] using A05.rho_budget_map h η (m : ℤ) Ns K v v.property)
  let R1 : A05.jointBudget h (lowerCharge Ns ν) K →ₗ[ℂ]
      A05.jointBudget h (lowerCharge Ns ν) (K+m) :=
    ((A05.rho h η (m : ℤ)).comp (A05.jointBudget h (lowerCharge Ns ν) K).subtype).codRestrict _
      (fun v => by simpa [A05.jointBudget, Nat.cast_add] using A05.rho_budget_map h η (m : ℤ) (lowerCharge Ns ν) K v v.property)
  refine ⟨F0, F1, R0, R1, hF0, hF1, (fun _ => rfl), (fun _ => rfl), ?_⟩
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change (F1 (R0 v) : FockSpace σ h) = (R1 (F0 v) : FockSpace σ h)
  rw [hF1]
  change kleinKernel h Ns ν (K+m) (A05.rho h η (m : ℤ) v) =
    A05.rho h η (m : ℤ) (F0 v)
  rw [hF0]
  exact kernel_raising_intertwine h hh Ns ν η K m hmpos hm v v.property

theorem klein_lowering_square (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (K m : ℕ) (hmpos : 0<m)
    (hm : pairMargin h (K+m) Ns ν) :
    ∃ F0 : A05.jointBudget h Ns K ≃ₗᵢ[ℂ] A05.jointBudget h (lowerCharge Ns ν) K,
    ∃ F1 : A05.jointBudget h Ns (K+m) ≃ₗᵢ[ℂ] A05.jointBudget h (lowerCharge Ns ν) (K+m),
    ∃ R0 : A05.jointBudget h Ns (K+m) →ₗ[ℂ] A05.jointBudget h Ns K,
    ∃ R1 : A05.jointBudget h (lowerCharge Ns ν) (K+m) →ₗ[ℂ] A05.jointBudget h (lowerCharge Ns ν) K,
      (∀ v, (F0 v : FockSpace σ h)=kleinKernel h Ns ν K v) ∧
      (∀ v, (F1 v : FockSpace σ h)=kleinKernel h Ns ν (K+m) v) ∧
      (∀ v, (R0 v : FockSpace σ h)=A05.rho h η (-(m : ℤ)) v) ∧
      (∀ v, (R1 v : FockSpace σ h)=A05.rho h η (-(m : ℤ)) v) ∧
      F0.toLinearMap.comp R0 = R1.comp F1.toLinearMap := by
  have hm0 : pairMargin h K Ns ν := by
    constructor
    · intro γ; have ht := hm.1 γ; push_cast at ht; omega
    · intro γ; have ht := hm.2 γ; push_cast at ht; omega
  obtain ⟨F0, hF0⟩ := klein_isometry_equiv h hh Ns ν K hm0
  obtain ⟨F1, hF1⟩ := klein_isometry_equiv h hh Ns ν (K+m) hm
  let R0 : A05.jointBudget h Ns (K+m) →ₗ[ℂ] A05.jointBudget h Ns K :=
    ((A05.rho h η (-(m : ℤ))).comp (A05.jointBudget h Ns (K+m)).subtype).codRestrict _
      (fun v => by simpa [A05.jointBudget, Nat.cast_add] using A05.rho_budget_map h η (-(m : ℤ)) Ns (K+m) v v.property)
  let R1 : A05.jointBudget h (lowerCharge Ns ν) (K+m) →ₗ[ℂ]
      A05.jointBudget h (lowerCharge Ns ν) K :=
    ((A05.rho h η (-(m : ℤ))).comp (A05.jointBudget h (lowerCharge Ns ν) (K+m)).subtype).codRestrict _
      (fun v => by simpa [A05.jointBudget, Nat.cast_add] using A05.rho_budget_map h η (-(m : ℤ)) (lowerCharge Ns ν) (K+m) v v.property)
  refine ⟨F0, F1, R0, R1, hF0, hF1, (fun _ => rfl), (fun _ => rfl), ?_⟩
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change (F0 (R0 v) : FockSpace σ h) = (R1 (F1 v) : FockSpace σ h)
  rw [hF0]
  change kleinKernel h Ns ν K (A05.rho h η (-(m : ℤ)) v) =
    A05.rho h η (-(m : ℤ)) (F1 v)
  rw [hF1]
  exact kernel_lowering_intertwine h hh Ns ν η K m hmpos hm v v.property

lemma kernel_cross_anticommute (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (hne : ν≠η)
    (K : ℕ) (hm : fourSectorMargin h K Ns ν η) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) :
    kleinKernel h (lowerCharge Ns ν) η K (kleinKernel h Ns ν K v) +
      kleinKernel h (lowerCharge Ns η) ν K (kleinKernel h Ns η K v) = 0 := by
  have hNs := r2_admissible h K Ns hm.1
  rw [← A05.partition_spanning h hh Ns hNs K hm.1] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨p,rfl⟩
    rw [kernel_partition h hh Ns ν K hm.1 p,
      kernel_partition h hh Ns η K hm.1 p, map_smul, map_smul,
      kernel_partition h hh (lowerCharge Ns ν) η K hm.2.1 p,
      kernel_partition h hh (lowerCharge Ns η) ν K hm.2.2.1 p,
      lower_charge_commute Ns ν η hne, smul_smul, smul_smul]
    rw [mul_comm (kleinPhase h Ns ν), mul_comm (kleinPhase h Ns η),
      phase_cross_sign h Ns ν η hne, neg_smul, neg_add_cancel]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add]
    rw [add_add_add_comm, hx, hy, add_zero]
  | smul a x _ hx =>
    simp only [map_smul, ← smul_add, hx, smul_zero]

lemma kernel_number_shift (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) (v : FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    kleinKernel h Ns ν K (A05.chargeObservable h η v) =
      A05.chargeObservable h η (kleinKernel h Ns ν K v) +
        (if ν=η then (1 : ℂ) else 0) • kleinKernel h Ns ν K v := by
  have ht := kernel_maps_budget h hh Ns ν K (r2_admissible h K (lowerCharge Ns ν) hm.2) v
  rw [A05.charge_budget h η Ns K v hv, map_smul,
    A05.charge_budget h η (lowerCharge Ns ν) K (kleinKernel h Ns ν K v) ht,
    ← add_smul]
  congr 1
  by_cases he : ν=η
  · subst η
    simp [lowerCharge]
  · simp [lowerCharge, Ne.symm he, he]

lemma kernel_ground (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) :
    kleinKernel h Ns ν K (A05.groundKet h Ns) =
      kleinPhase h Ns ν • A05.groundKet h (lowerCharge Ns ν) := by
  let p0 : A05.JointPartitions σ K :=
    ⟨fun _ => ⟨⟨0, by omega⟩, (default : Nat.Partition 0)⟩, by simp⟩
  have hg (Ms : σ → ℤ) (hMs : A05.admissible h Ms) :
      A05.partitionState h Ms p0 = A05.groundKet h Ms := by
    unfold A05.partitionState
    rw [A05.word_tensor h Ms hMs]
    simpa [p0, Ch11.partitionList, Ch11.wordState, Ch11.creatorWord,
      Ch07.groundKet, A05.groundKet, A05.groundConfiguration] using
      A05.tensor_kets h (fun η => Ch07.groundConfiguration h (Ms η))
  rw [← hg Ns (r2_admissible h K Ns hm.1), kernel_partition h hh Ns ν K hm.1,
    hg (lowerCharge Ns ν) (r2_admissible h K _ hm.2)]

lemma kernel_ground_nonzero (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) :
    kleinKernel h Ns ν K (A05.groundKet h Ns) ≠ 0 := by
  rw [kernel_ground h hh Ns ν K hm]
  apply smul_ne_zero
  · intro hz
    have hn := phase_norm h Ns ν
    rw [hz, norm_zero] at hn
    norm_num at hn
  · exact A05.ground_ne_zero h _

/-- Double Klein paths have actual nonzero ground action. This also covers
same-species squares under the stated doubly lowered-sector margin. -/
lemma double_kernel_ground_nonzero (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ)
    (K : ℕ) (hm : fourSectorMargin h K Ns ν η) :
    kleinKernel h (lowerCharge Ns ν) η K
      (kleinKernel h Ns ν K (A05.groundKet h Ns)) ≠ 0 := by
  rw [kernel_ground h hh Ns ν K ⟨hm.1, hm.2.1⟩, map_smul,
    kernel_ground h hh (lowerCharge Ns ν) η K ⟨hm.2.1, hm.2.2.2⟩]
  apply smul_ne_zero
  · intro hz
    have hn := phase_norm h Ns ν
    rw [hz, norm_zero] at hn
    norm_num at hn
  · apply smul_ne_zero
    · intro hz
      have hn := phase_norm h (lowerCharge Ns ν) η
      rw [hz, norm_zero] at hn
      norm_num at hn
    · exact A05.ground_ne_zero h _

end Bosonize.Ch13
