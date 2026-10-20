import Bosonize.Core.Ch20CDW
import Bosonize.Core.V1S5SmallInteractingModel

/-! V1-S6 Phase A: typed physical product residuals and field obstructions. -/
@[expose] section
namespace Bosonize.V1S6

open scoped BigOperators

variable {U H : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A finite-dimensional isometric embedding together with its actual Hilbert
adjoint. The inner-product equation fixes the adjoint convention; the left
inverse equation records isometry and does not assert surjectivity. -/
structure IsometricEmbedding where
  map : U →L[ℂ] H
  adjoint : H →L[ℂ] U
  adjoint_inner : ∀ u h, inner ℂ (map u) h = inner ℂ u (adjoint h)
  adjoint_map : adjoint.comp map = ContinuousLinearMap.id ℂ U

/-- An actual ambient orthogonal projection, with both defining equations
explicit. -/
structure OrthogonalProjection (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] where
  map : H →L[ℂ] H
  idempotent : map.comp map = map
  selfAdjoint : ∀ x y, inner ℂ (map x) y = inner ℂ x (map y)

/-- Orthogonal projection onto the selected embedded range. -/
def rangeProjection (E : IsometricEmbedding (U := U) (H := H)) : H →L[ℂ] H :=
  E.map.comp E.adjoint

omit [FiniteDimensional ℂ U] in
/-- The selected embedded range is a subspace of the ambient budget range.
This is the geometric content needed for `P - U U†` to be the omitted
orthogonal range inside `P`. -/
lemma rangeProjection_subprojection (E : IsometricEmbedding (U := U) (H := H))
    (P : OrthogonalProjection H)
    (hE : P.map.comp E.map = E.map) :
    P.map.comp (rangeProjection E) = rangeProjection E := by
  ext x
  simp [rangeProjection, ← ContinuousLinearMap.comp_assoc, hE]

/-- The ambient intermediate-budget channel discarded by projection. -/
def intermediateResidual {S T : Type*}
    [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
    (A : H →L[ℂ] T) (B : S →L[ℂ] H) (P : OrthogonalProjection H) : S →L[ℂ] T :=
  A.comp ((ContinuousLinearMap.id ℂ H - P.map).comp B)

/-- The part of the ambient intermediate budget omitted by an embedded
oscillator or partition carrier. It vanishes only when range equality is proved. -/
def omittedRangeResidual (E : IsometricEmbedding (U := U) (H := H)) {S T : Type*}
    [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
    (A : H →L[ℂ] T) (B : S →L[ℂ] H) (P : OrthogonalProjection H) : S →L[ℂ] T :=
  A.comp ((P.map - rangeProjection E).comp B)

/-- Exact finite-dictionary error for an independently defined candidate on
the selected finite source/target carriers. This includes its mode cutoff and
normalization choices; it is not identified with either in isolation. -/
def finiteDictionaryError {S T : Type*}
    [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
    (actual candidate : S →L[ℂ] T) : S →L[ℂ] T := actual - candidate

def finiteDictionaryErrorOnVector {S T : Type*}
    [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
    (actual candidate : S →ₗ[ℂ] T) (v : S) : T := actual v - candidate v

section TypedProducts
variable {S T X Y Z : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [FiniteDimensional ℂ Z]

omit [FiniteDimensional ℂ U] [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] in
/-- Transport a physical product through endpoint and intermediate isometric
embeddings. Both the ambient projection loss and the omitted embedded-range
term remain explicit. -/
lemma typed_product_decomposition
    (Us : IsometricEmbedding (U := S) (H := X))
    (Um : IsometricEmbedding (U := U) (H := H))
    (Ut : IsometricEmbedding (U := T) (H := Y))
    (A : H →L[ℂ] Y) (B : X →L[ℂ] H) (Pm : OrthogonalProjection H)
    (_hUm : Pm.map.comp Um.map = Um.map) :
    Ut.adjoint.comp (A.comp (B.comp Us.map)) =
      ((Ut.adjoint.comp (A.comp Um.map)).comp
        (Um.adjoint.comp (B.comp Us.map))) +
      (Ut.adjoint.comp ((intermediateResidual A B Pm).comp Us.map)) +
      (Ut.adjoint.comp ((omittedRangeResidual Um A B Pm).comp Us.map)) := by
  have _hRange := rangeProjection_subprojection Um Pm _hUm
  ext x
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    intermediateResidual, omittedRangeResidual, rangeProjection,
    sub_apply, ContinuousLinearMap.id_apply]
  simp only [map_sub]
  module

/-- Operator-norm comparison: the two projection/range residuals and the two
independent finite-dictionary errors are kept explicit. State and dispersion
terms do not apply because this is an operator comparison with fixed carriers. -/
theorem quantitative_product_comparison
    (Us : IsometricEmbedding (U := S) (H := X))
    (Um : IsometricEmbedding (U := U) (H := H))
    (Ut : IsometricEmbedding (U := T) (H := Y))
    (A : H →L[ℂ] Y) (B : X →L[ℂ] H) (Pm : OrthogonalProjection H)
    (hUm : Pm.map.comp Um.map = Um.map)
    (VA : U →L[ℂ] T) (VB : S →L[ℂ] U) :
    ‖Ut.adjoint.comp (A.comp (B.comp Us.map)) - VA.comp VB‖ ≤
      ‖Ut.adjoint.comp ((intermediateResidual A B Pm).comp Us.map)‖ +
      ‖Ut.adjoint.comp ((omittedRangeResidual Um A B Pm).comp Us.map)‖ +
      ‖finiteDictionaryError (Ut.adjoint.comp (A.comp Um.map)) VA‖ *
        ‖Um.adjoint.comp (B.comp Us.map)‖ +
      ‖VA‖ * ‖finiteDictionaryError (Um.adjoint.comp (B.comp Us.map)) VB‖ := by
  let Ahat := Ut.adjoint.comp (A.comp Um.map)
  let Bhat := Um.adjoint.comp (B.comp Us.map)
  let Rproj := Ut.adjoint.comp ((intermediateResidual A B Pm).comp Us.map)
  let Rrange := Ut.adjoint.comp ((omittedRangeResidual Um A B Pm).comp Us.map)
  have hprod : Ahat.comp Bhat - VA.comp VB =
      (Ahat - VA).comp Bhat + VA.comp (Bhat - VB) := by
    ext x
    simp [Ahat, Bhat, ContinuousLinearMap.comp_apply]
  have hdecomp := typed_product_decomposition Us Um Ut A B Pm hUm
  calc
    ‖Ut.adjoint.comp (A.comp (B.comp Us.map)) - VA.comp VB‖ =
        ‖Rproj + Rrange + (Ahat.comp Bhat - VA.comp VB)‖ := by
          rw [hdecomp]
          congr 1
          ext x
          simp [Ahat, Bhat, Rproj, Rrange, ContinuousLinearMap.comp_apply,
            intermediateResidual, omittedRangeResidual, rangeProjection]
          module
    _ ≤ ‖Rproj‖ + ‖Rrange‖ + ‖Ahat.comp Bhat - VA.comp VB‖ := by
          calc
            ‖Rproj + Rrange + (Ahat.comp Bhat - VA.comp VB)‖ ≤
                ‖Rproj + Rrange‖ + ‖Ahat.comp Bhat - VA.comp VB‖ := norm_add_le _ _
            _ ≤ ‖Rproj‖ + ‖Rrange‖ + ‖Ahat.comp Bhat - VA.comp VB‖ := by
                gcongr
                exact norm_add_le Rproj Rrange
    _ ≤ ‖Rproj‖ + ‖Rrange‖ +
          ‖Ahat - VA‖ * ‖Bhat‖ + ‖VA‖ * ‖Bhat - VB‖ := by
          have herr : ‖Ahat.comp Bhat - VA.comp VB‖ ≤
              ‖Ahat - VA‖ * ‖Bhat‖ + ‖VA‖ * ‖Bhat - VB‖ := by
            rw [hprod]
            calc
              ‖(Ahat - VA).comp Bhat + VA.comp (Bhat - VB)‖ ≤
                  ‖(Ahat - VA).comp Bhat‖ + ‖VA.comp (Bhat - VB)‖ := norm_add_le _ _
              _ ≤ ‖Ahat - VA‖ * ‖Bhat‖ + ‖VA‖ * ‖Bhat - VB‖ := by
                  exact add_le_add
                    (ContinuousLinearMap.opNorm_comp_le _ _)
                    (ContinuousLinearMap.opNorm_comp_le _ _)
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_left herr (‖Rproj‖ + ‖Rrange‖)
    _ = _ := by
          simp [Ahat, Bhat, Rproj, Rrange, finiteDictionaryError]
end TypedProducts

section ConcreteObstructions
def singleSpeciesZeroCharge : PUnit → ℤ := fun _ => 0

theorem singleSpeciesZero_admissible : A05.admissible 3 singleSpeciesZeroCharge := by
  intro ν
  simp [singleSpeciesZeroCharge, Ch07.admissible]

/-- Nonempty-cutoff (`M=1`) full-ground-image obstruction: h=3, N=0,
Kin=0, Kout=2, trivial twist and x=0. This is the actual A-vs-B comparison;
the theorem does not identify the separate S2 formal vertex C with either. -/
theorem h3_m1_ground_image_mismatch :
    ‖finiteDictionaryErrorOnVector
      (S := A05.jointBudget 3 singleSpeciesZeroCharge 0)
      (T := A05.jointBudget 3 (Ch13.lowerCharge singleSpeciesZeroCharge PUnit.unit) 2)
      (Ch14.physicalMap 3 (fun _ => Ch06Ext.periodicTwist 6)
        singleSpeciesZeroCharge PUnit.unit 0 0 2)
      (Ch14.vertexCandidate 3 1 (fun _ => Ch06Ext.periodicTwist 6)
        singleSpeciesZeroCharge PUnit.unit 0 0 2)
      (Ch14.groundVector 3 (by decide) singleSpeciesZeroCharge
        singleSpeciesZero_admissible 0)‖ ≥ 1 / (2 * Real.sqrt 6) := by
  sorry

/-- The accepted CH20 discarded-channel witness strengthened to a norm lower
bound on the actual projected finite carrier. -/
theorem cdw_discarded_channel_norm_lower_bound :
    ‖Ch14.projectedMap 2 Ch20.witnessZero
      (Ch20.cdwTarget Ch16.standardBranches Ch20.witnessZero) 0 1
      (Ch20.cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
        Ch16.standardBranches 1 Ch20.witnessZero 0)
      (Ch14.groundVector 2 (by decide) Ch20.witnessZero
        Ch20.witnessZero_admissible 0)‖ ≥ (1 / 4 : ℝ) := by
  classical
  let (h : ℕ) : LinearOrder (A05.Mode (Fin 2) h) := A05.localModeLinearOrder h
  let (h : ℕ) : LT (A05.Mode (Fin 2) h) := A05.localModeLT h
  let (h : ℕ) : LE (A05.Mode (Fin 2) h) := A05.localModeLE h
  let (h : ℕ) : DecidableEq (A05.Mode (Fin 2) h) := A05.localModeDecidableEq h
  let : LinearOrder (Fin 2 × Ch01.Band 4) := A05.localModeLinearOrder 2
  let : DecidableEq (Fin 2 × Ch01.Band 4) := A05.localModeDecidableEq 2
  have ground_memX (h : ℕ) (Ns : (Fin 2) → ℤ) (ν : (Fin 2))
      (k : Ch01.Band (2*h)) :
      (ν,k) ∈ A05.groundConfiguration h Ns ↔ k.val ≤ Ns ν := by
    simp only [A05.groundConfiguration, A05.jointConfiguration,
      Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
      Ch07.groundConfiguration, Finset.mem_filter]
    aesop

  let targetZeroMn : Ch01.Band 4 :=
    ⟨-1, by norm_num [Ch01.inBandPredicate]⟩

  let targetZeroM0 : Ch01.Band 4 :=
    ⟨0, by norm_num [Ch01.inBandPredicate]⟩

  let targetZeroOccupation (l : Ch01.Band 4) :
      A05.Occupation (Fin 2) 2 :=
    insert (0,l) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,targetZeroMn))

  have targetZeroSpeciesBridge (S : A05.Occupation (Fin 2) 2)
      (η : Fin 2) (q : Ch01.Band 4) :
      q ∈ Ch07.speciesConfiguration 2 S η ↔ (η,q) ∈ S := by
    simp only [Ch07.speciesConfiguration, Finset.mem_image, Finset.mem_filter]
    aesop

  have targetZeroLeftSpeciesOccupation (l : Ch01.Band 4) :
      Ch07.speciesConfiguration 2 (targetZeroOccupation l) 1 = {targetZeroM0} := by
    ext q
    rw [targetZeroSpeciesBridge, Finset.mem_singleton]
    simp only [targetZeroOccupation, Finset.mem_insert, Finset.mem_erase]
    have hs : (1 : Fin 2) ≠ 0 := by decide
    simp only [Prod.mk.injEq, hs, false_and, false_or]
    rw [ground_memX 2 Ch20.witnessZero 1 q]
    simp only [Ch20.witnessZero]
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
      · simpa [Ch20.witnessZero] using (show q.val ≤ 0 by omega)

  have targetZeroLeftSpeciesExcitation (l : Ch01.Band 4) :
      Ch07.excitationEnergy 2
        (Ch07.speciesConfiguration 2 (targetZeroOccupation l) 1) = 1 := by
    rw [targetZeroLeftSpeciesOccupation]
    unfold Ch07.excitationEnergy Ch07.relativeEnergy Ch07.relativeCharge
    rw [Ch05.sea_energy_even 2 (by decide)]
    norm_num [Ch07.groundEnergy, Ch05.occupationEnergy, targetZeroM0]

  have targetZeroErasedSpeciesOne :
      Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,targetZeroMn)) 1 =
          {targetZeroM0} := by
    have hcfg : Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,targetZeroMn)) 1 =
        Ch07.speciesConfiguration 2 (targetZeroOccupation targetZeroM0) 1 := by
      ext q
      rw [targetZeroSpeciesBridge, targetZeroSpeciesBridge]
      simp [targetZeroOccupation, Finset.mem_erase]
    rw [hcfg, targetZeroLeftSpeciesOccupation]

  have targetZeroErasedExcitation_ge_one :
      1 ≤ Ch07.totalExcitation 2
        ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,targetZeroMn)) := by
    rw [Ch07.totalExcitation]
    have hsingle := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun ν : Fin 2 => Ch07.excitationEnergy 2
        (Ch07.speciesConfiguration 2
          ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,targetZeroMn)) ν))
      (fun ν hν => Ch07.excitation_nonneg 2 (by decide)
        (Ch07.speciesConfiguration 2
          ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,targetZeroMn)) ν))
      (Finset.mem_univ (1 : Fin 2))
    have hleft : Ch07.excitationEnergy 2
        (Ch07.speciesConfiguration 2
          ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,targetZeroMn)) 1) = 1 := by
      rw [targetZeroErasedSpeciesOne]
      exact targetZeroLeftSpeciesExcitation targetZeroM0
    omega

  have targetZeroErased_not_mid_budget :
      (A05.groundConfiguration 2 Ch20.witnessZero).erase (1,targetZeroMn) ∉
        Ch14.budgetSet 2 (Ch13.lowerCharge Ch20.witnessZero 1) 0 := by
    intro hb
    have hpos := targetZeroErasedExcitation_ge_one
    have ht := hb.2
    omega

  have discardedFieldKet (h : ℕ) (b : (Fin 2) → Ch06Ext.BoundaryTwist (2*h))
      (ν : (Fin 2)) (x : ℤ) (S : A05.Occupation (Fin 2) h) :
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

  have discardedAdjointLiftedKet (h : ℕ)
      (b : (Fin 2) → Ch06Ext.BoundaryTwist (2*h)) (ν : (Fin 2)) (x : ℤ)
      (S : A05.Occupation (Fin 2) h) :
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

  have discardedOneSubProjectionKet (h : ℕ) (Ns : (Fin 2) → ℤ) (K : ℕ)
      (S : A05.Occupation (Fin 2) h) (c : ℂ) :
      (1 - Ch14.projection h Ns K) (c • A02.ket S) =
        if S ∈ Ch14.budgetSet h Ns K then 0 else c • A02.ket S := by
    rw [LinearMap.sub_apply, Module.End.one_apply, map_smul]
    simp only [Ch14.projection, A03.projection_ket]
    by_cases hs : S ∈ Ch14.budgetSet h Ns K <;> simp [hs]

  have discardedProjectedFieldKet (h : ℕ)
      (b : (Fin 2) → Ch06Ext.BoundaryTwist (2*h)) (br : A06.Branches (Fin 2))
      (x : ℤ) (Ns : (Fin 2) → ℤ) (K : ℕ) (S : A05.Occupation (Fin 2) h) :
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

  have discardedResidualDoubleExpansion (h : ℕ)
      (b : (Fin 2) → Ch06Ext.BoundaryTwist (2*h)) (br : A06.Branches (Fin 2))
      (x : ℤ) (Ns : (Fin 2) → ℤ) (Km : ℕ) (S : A05.Occupation (Fin 2) h) :
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

  have inner_fsumX {E : Type} [SeminormedAddCommGroup E]
      [InnerProductSpace ℂ E] {ι : Type} [Fintype ι]
      (f : ι → E) (x : E) :
      inner ℂ x (∑ i, f i) = ∑ i, inner ℂ x (f i) := by
    rw [← innerₛₗ_apply_apply]
    rw [map_sum]
    simp only [innerₛₗ_apply_apply]

  have inner_if_zeroX {E : Type} [SeminormedAddCommGroup E]
      [InnerProductSpace ℂ E] (x v : E) (p : Prop) [Decidable p] :
      inner ℂ x (if p then v else 0) = if p then inner ℂ x v else 0 := by
    split_ifs <;> simp

  have sum_single_pairX {ι κ : Type} [Fintype ι] [Fintype κ]
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
  classical
  let m1 : Ch01.Band 4 := ⟨1, by norm_num [Ch01.inBandPredicate]⟩
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
      (heq : insert (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k)) =
        targetZeroOccupation m1) : k = targetZeroMn ∧ p = m1 := by
    have hsL := congrArg (fun S => Ch07.speciesConfiguration 2 S 1) heq
    have hsR := congrArg (fun S => Ch07.speciesConfiguration 2 S 0) heq
    have hL0 : targetZeroM0 ∈ Ch07.speciesConfiguration 2
        (insert (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k))) 1 := by
      rw [hsL, leftSpecies_residualOccupation]
      simp
    have hsrcmn : targetZeroMn ∈ Ch07.speciesConfiguration 2
        (A05.groundConfiguration 2 Ch20.witnessZero) 1 := by
      rw [speciesBridge, ground_memX]
      simp [Ch20.witnessZero,targetZeroMn]
    have hk : k ≠ targetZeroM0 := by
      intro h
      subst k
      have hL0' : targetZeroM0 ∈ Ch07.speciesConfiguration 2
          ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,targetZeroM0)) 1 := by
        rw [speciesInsertBridge] at hL0
        simpa using hL0
      have hnot : targetZeroM0 ∉ Ch07.speciesConfiguration 2
          ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,targetZeroM0)) 1 := by
        rw [speciesEraseBridge]
        simp
      exact hnot hL0'
    have hkn : k = targetZeroMn := by
      have hmnAbsent : targetZeroMn ∉ Ch07.speciesConfiguration 2
          (insert (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k))) 1 := by
        rw [hsL, leftSpecies_residualOccupation]
        simp only [Finset.mem_singleton]
        intro heq
        have hv := congrArg Subtype.val heq
        norm_num [targetZeroMn,targetZeroM0] at hv
      have heraseAbsent : targetZeroMn ∉ Ch07.speciesConfiguration 2
          ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k)) 1 := by
        rw [speciesInsertBridge] at hmnAbsent
        intro hm
        exact hmnAbsent (Or.inl hm)
      by_contra hnot
      have hmnErase : targetZeroMn ∈ Ch07.speciesConfiguration 2
          ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k)) 1 := by
        apply (speciesEraseBridge _ _ _ _ _).mpr
        refine ⟨hsrcmn, Or.inr ?_⟩
        intro heq
        exact hnot heq.symm
      exact heraseAbsent hmnErase
    refine ⟨hkn, ?_⟩
    subst k
    have hR1 : m1 ∈ Ch07.speciesConfiguration 2
        (insert (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,targetZeroMn))) 0 := by
      rw [hsR]
      rw [speciesBridge]
      simp [targetZeroOccupation, m1]
    have hsource1 : m1 ∉ Ch07.speciesConfiguration 2
        ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,targetZeroMn)) 0 := by
      rw [speciesEraseBridge, speciesBridge, ground_memX]
      simp [Ch20.witnessZero,m1,targetZeroMn]
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
    rw [ground_memX 2 Ch20.witnessZero 0 q]
    simp only [Ch07.groundConfiguration, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Ch20.witnessZero]
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
        (Ch20.cdwTarget Ch16.standardBranches Ch20.witnessZero) 1 := by
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
    (1,k) ∈ A05.groundConfiguration 2 Ch20.witnessZero ∧
    (A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k) ∉
      Ch14.budgetSet 2 (Ch13.lowerCharge Ch20.witnessZero 1) 0 ∧
    (0,p) ∉ (A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k) ∧
    insert (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k)) ∈
      Ch14.budgetSet 2 (Ch20.cdwTarget Ch16.standardBranches Ch20.witnessZero) 1 ∧
    insert (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k)) = targetZeroOccupation m1

  let residual_m1_f (k p : Ch01.Band 4) : ℂ :=
    Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) k 1 *
      Ch04.fermionSign (1,k) (A05.groundConfiguration 2 Ch20.witnessZero) *
      star (A01.normalization 4 : ℂ) *
      star (Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) p 1) *
      Ch04.fermionSign (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k))

  have residual_m1_inner_expand :
      inner ℂ (A02.ket (targetZeroOccupation m1))
        (Ch14.projection 2 (Ch20.cdwTarget Ch16.standardBranches Ch20.witnessZero) 1
          (Ch20.cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
            Ch16.standardBranches 1 Ch20.witnessZero 0
            (@A02.ket (A05.Mode (Fin 2) 2) (inferInstance)
              (A05.localModeDecidableEq (σ:=Fin 2) 2)
              (A05.groundConfiguration 2 Ch20.witnessZero)))) =
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
    by_cases hk : (1,k) ∈ A05.groundConfiguration 2 Ch20.witnessZero
    · simp only [hk, ite_true]
      by_cases hmid : (A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k) ∈
          Ch14.budgetSet 2 (Ch13.lowerCharge Ch20.witnessZero 1) 0
      · simp [hmid, residual_m1_g]
      · simp only [hmid, ite_false]
        rw [← mul_assoc, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : (0,p) ∈ (A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k)
        · simp only [residual_m1_g, hp, not_true_eq_false, false_and, and_false, ite_false, mul_zero]
        · simp only [hp, not_false_eq_true, ite_true]
          by_cases ht : insert (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k)) ∈
              Ch14.budgetSet 2 (Ch20.cdwTarget Ch16.standardBranches Ch20.witnessZero) 1
          · by_cases heq : insert (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k)) =
                targetZeroOccupation m1
            · have hIns : insert (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k)) ∈
                  Ch14.budgetSet 2 (Ch20.cdwTarget Ch16.standardBranches Ch20.witnessZero) 1 := by
                rw [heq]
                exact residual_m1_target_budget
              simp only [residual_m1_g, hk, hmid, hp, heq, not_false_eq_true,
                true_and, and_true, ite_true, eq_self]
              simp [residual_m1_f, mul_assoc, mul_left_comm, mul_comm]
              rfl
            · have hneq : targetZeroOccupation m1 ≠
                  insert (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k)) :=
                fun h => heq h.symm
              simp only [residual_m1_g, hk, hmid, hp, heq, hneq, not_false_eq_true,
                and_false, ite_false]
              simp only [ite_self, mul_zero]
          · by_cases heq : insert (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k)) =
                targetZeroOccupation m1
            · have hIns : insert (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k)) ∈
                  Ch14.budgetSet 2 (Ch20.cdwTarget Ch16.standardBranches Ch20.witnessZero) 1 := by
                rw [heq]
                exact residual_m1_target_budget
              exact (ht hIns).elim
            · have hneq : targetZeroOccupation m1 ≠
                  insert (0,p) ((A05.groundConfiguration 2 Ch20.witnessZero).erase (1,k)) :=
                fun h => heq h.symm
              simp only [residual_m1_g, hk, hmid, hp, heq, hneq, not_false_eq_true,
                and_false, ite_false]
              simp only [ite_self, mul_zero]
    · simp [hk, residual_m1_g]

  have coefficient_norm :
      ‖inner ℂ (A02.ket (targetZeroOccupation m1))
        (Ch14.projection 2 (Ch20.cdwTarget Ch16.standardBranches Ch20.witnessZero) 1
          (Ch20.cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
            Ch16.standardBranches 1 Ch20.witnessZero 0
            (@A02.ket (A05.Mode (Fin 2) 2) (inferInstance)
              (A05.localModeDecidableEq (σ:=Fin 2) 2)
              (A05.groundConfiguration 2 Ch20.witnessZero))))‖ = (1 / 4 : ℝ) := by
    rw [residual_m1_inner_expand]
    classical
    let g := residual_m1_g
    let f := residual_m1_f
    have huniq : ∀ k p, g k p → k = targetZeroMn ∧ p = m1 := by
      intro k p hg
      exact residual_m1_pair_unique k p hg.2.2.2.2
    have hsupport : g targetZeroMn m1 := by
      refine ⟨?_, targetZeroErased_not_mid_budget, ?_, residual_m1_target_budget, ?_⟩
      · rw [ground_memX 2 Ch20.witnessZero 1 targetZeroMn]
        simp [Ch20.witnessZero,targetZeroMn]
      · intro hp
        have hsource : (0,m1) ∈ A05.groundConfiguration 2 Ch20.witnessZero :=
          (Finset.mem_erase.mp hp).2
        rw [ground_memX 2 Ch20.witnessZero 0 m1] at hsource
        simp [Ch20.witnessZero,m1] at hsource
      · simp [targetZeroOccupation]
    change ‖(A01.normalization 4 : ℂ) *
        (∑ k : Ch01.Band 4, ∑ p : Ch01.Band 4,
          if g k p then f k p else 0)‖ = (1 / 4 : ℝ)
    rw [sum_single_pairX targetZeroMn m1 f g huniq hsupport]
    simp only [f]
    have hchar (k : Ch01.Band 4) :
        ‖Ch06Ext.twistedCharacter 4 (Ch06Ext.periodicTwist 4) k 1‖ = 1 := by
      simpa [Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, Ch06Ext.periodicTwist] using
        A01.complex_character_norm 4 _ (A01.canonical_root_primitive 4) k.val 1
    have hsign (i : A05.Mode (Fin 2) 2) (S : A05.Occupation (Fin 2) 2) :
        ‖Ch04.fermionSign i S‖ = 1 := by
      simp [Ch04.fermionSign]
    simp only [residual_m1_f, norm_mul, norm_star, hchar, hsign]
    have hsqrt : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [A01.normalization, hsqrt]
  have hbound := norm_inner_le_norm (𝕜 := ℂ) (A02.ket (targetZeroOccupation m1))
    (Ch14.projection 2 (Ch20.cdwTarget Ch16.standardBranches Ch20.witnessZero) 1
      (Ch20.cdwResidualOp 2 (fun _ => Ch06Ext.periodicTwist 4)
        Ch16.standardBranches 1 Ch20.witnessZero 0 (A05.groundKet 2 Ch20.witnessZero)))
  rw [A05.groundKet] at hbound
  rw [coefficient_norm, A02.ket_norm, one_mul] at hbound
  exact hbound
end ConcreteObstructions

end Bosonize.V1S6
end
