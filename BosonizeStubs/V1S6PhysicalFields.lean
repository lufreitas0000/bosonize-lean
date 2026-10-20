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
  sorry
end ConcreteObstructions

end Bosonize.V1S6
end
