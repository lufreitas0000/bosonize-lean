module

public import BosonizeStubs.A05MultiSpecies

/-! CH13: explicit finite Gram-kernel Klein operators on the actual CAR carrier.
All data are complete; typed budget isometries and squares are Phase A obligations. -/
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

lemma lower_charge_commute (Ns : σ → ℤ) (ν η : σ) (hne : ν≠η) :
    lowerCharge (lowerCharge Ns ν) η = lowerCharge (lowerCharge Ns η) ν := by sorry

lemma phase_norm (h : ℕ) (Ns : σ → ℤ) (ν : σ) : ‖kleinPhase h Ns ν‖ = 1 := by sorry

lemma phase_cross_sign (h : ℕ) (Ns : σ → ℤ) (ν η : σ) (hne : ν≠η) :
    kleinPhase h (lowerCharge Ns ν) η * kleinPhase h Ns ν =
      -(kleinPhase h (lowerCharge Ns η) ν * kleinPhase h Ns η) := by sorry

lemma r2_admissible (h K : ℕ) (Ns : σ → ℤ) (hR2 : A05.r2 h K Ns) :
    A05.admissible h Ns := by sorry

/-- Actual lexicographic CAR ground coefficient includes both sign contributions. -/
lemma ground_top_annihilation (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (ν : σ) (hν : -(h : ℤ)+1 ≤ Ns ν)
    (k : Ch01.Band (2*h)) (hk : k.val=Ns ν) :
    A05.annihilation h ν k (A05.groundKet h Ns) =
      kleinPhase h Ns ν • A05.groundKet h (lowerCharge Ns ν) := by sorry

lemma ground_field_coefficient (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (ν : σ) (hν : -(h : ℤ)+1 ≤ Ns ν)
    (b : σ → Ch06Ext.BoundaryTwist (2*h)) (x : ℤ) :
    inner ℂ (A05.groundKet h (lowerCharge Ns ν))
      (A05.liftedAnnihilation h b ν x (A05.groundKet h Ns)) =
      (A01.normalization (2*h) : ℂ) * kleinPhase h Ns ν *
        Ch06Ext.liftPhase (2*h) (b ν) x * A01.canonicalRoot (2*h)^(x*Ns ν) := by sorry

lemma kernel_partition (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hR2 : A05.r2 h K Ns) (p : A05.JointPartitions σ K) :
    kleinKernel h Ns ν K (A05.partitionState h Ns p) =
      kleinPhase h Ns ν • A05.partitionState h (lowerCharge Ns ν) p := by sorry

lemma inverse_partition (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hR2 : A05.r2 h K (lowerCharge Ns ν)) (p : A05.JointPartitions σ K) :
    inverseKernel h Ns ν K (A05.partitionState h (lowerCharge Ns ν) p) =
      star (kleinPhase h Ns ν) • A05.partitionState h Ns p := by sorry

lemma kernel_maps_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hN : A05.admissible h (lowerCharge Ns ν)) (v : FockSpace σ h) :
    kleinKernel h Ns ν K v ∈ A05.jointBudget h (lowerCharge Ns ν) K := by sorry

lemma inverse_maps_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hN : A05.admissible h Ns) (v : FockSpace σ h) :
    inverseKernel h Ns ν K v ∈ A05.jointBudget h Ns K := by sorry

lemma kernel_inner_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) (v w : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) (hw : w ∈ A05.jointBudget h Ns K) :
    inner ℂ (kleinKernel h Ns ν K v) (kleinKernel h Ns ν K w) = inner ℂ v w := by sorry

lemma inverse_kernel_source (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) (v : FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    inverseKernel h Ns ν K (kleinKernel h Ns ν K v) = v := by sorry

lemma kernel_inverse_target (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h (lowerCharge Ns ν) K) :
    kleinKernel h Ns ν K (inverseKernel h Ns ν K v) = v := by sorry

lemma kernel_adjoint (h : ℕ) (Ns : σ → ℤ) (ν : σ) (K : ℕ) :
    LinearMap.adjoint (kleinKernel h Ns ν K) = inverseKernel h Ns ν K := by sorry

/-- Surjective typed budget isometry, canonically realized by the explicit kernel. -/
theorem klein_isometry_equiv (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) :
    ∃ F : A05.jointBudget h Ns K ≃ₗᵢ[ℂ] A05.jointBudget h (lowerCharge Ns ν) K,
      ∀ v, (F v : FockSpace σ h) = kleinKernel h Ns ν K v := by sorry

lemma kernel_cutoff_consistent (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K J : ℕ)
    (hKJ : K≤J) (hm : pairMargin h J Ns ν) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) :
    kleinKernel h Ns ν J v = kleinKernel h Ns ν K v := by sorry

lemma kernel_raising_intertwine (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (K m : ℕ) (hmpos : 0<m)
    (hm : pairMargin h (K+m) Ns ν) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) :
    kleinKernel h Ns ν (K+m) (A05.rho h η (m : ℤ) v) =
      A05.rho h η (m : ℤ) (kleinKernel h Ns ν K v) := by sorry

lemma kernel_lowering_intertwine (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (K m : ℕ) (hmpos : 0<m)
    (hm : pairMargin h (K+m) Ns ν) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns (K+m)) :
    kleinKernel h Ns ν K (A05.rho h η (-(m : ℤ)) v) =
      A05.rho h η (-(m : ℤ)) (kleinKernel h Ns ν (K+m) v) := by sorry

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
      F1.toLinearMap.comp R0 = R1.comp F0.toLinearMap := by sorry

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
      F0.toLinearMap.comp R0 = R1.comp F1.toLinearMap := by sorry

lemma kernel_cross_anticommute (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (hne : ν≠η)
    (K : ℕ) (hm : fourSectorMargin h K Ns ν η) (v : FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) :
    kleinKernel h (lowerCharge Ns ν) η K (kleinKernel h Ns ν K v) +
      kleinKernel h (lowerCharge Ns η) ν K (kleinKernel h Ns η K v) = 0 := by sorry

lemma kernel_number_shift (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) (v : FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    kleinKernel h Ns ν K (A05.chargeObservable h η v) =
      A05.chargeObservable h η (kleinKernel h Ns ν K v) +
        (if ν=η then (1 : ℂ) else 0) • kleinKernel h Ns ν K v := by sorry

lemma kernel_ground (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) :
    kleinKernel h Ns ν K (A05.groundKet h Ns) =
      kleinPhase h Ns ν • A05.groundKet h (lowerCharge Ns ν) := by sorry

lemma kernel_ground_nonzero (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (K : ℕ)
    (hm : pairMargin h K Ns ν) :
    kleinKernel h Ns ν K (A05.groundKet h Ns) ≠ 0 := by sorry

/-- Double Klein paths have actual nonzero ground action. This also covers
same-species squares under the stated doubly lowered-sector margin. -/
lemma double_kernel_ground_nonzero (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν η : σ)
    (K : ℕ) (hm : fourSectorMargin h K Ns ν η) :
    kleinKernel h (lowerCharge Ns ν) η K
      (kleinKernel h Ns ν K (A05.groundKet h Ns)) ≠ 0 := by sorry

end Bosonize.Ch13
