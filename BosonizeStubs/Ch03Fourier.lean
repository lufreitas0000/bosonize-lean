module

public import Bosonize.Core.Ch02UmbralCalculus
public import BosonizeStubs.A01FourierCharacters
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Chapter 3: finite Fourier transform

Phase A, unlocked. S is negative-sign analysis; T is positive-sign synthesis.
The generic algebraic inverse is L⁻¹ T. Complex counting-space normalization is separate.
No isometry equivalence is bundled until its proof fields are available in Phase B.
-/

@[expose] public section

namespace Bosonize.Ch03

open scoped BigOperators

variable {K : Type*} [Field K]

/-- Unscaled negative-sign analysis on distinct position and band function carriers. -/
noncomputable def analysis (L : ℕ) [NeZero L] (ζ : K) :
    (Ch01.Lattice L → K) →ₗ[K] (Ch01.Band L → K) where
  toFun f k := ∑ x : Ch01.Lattice L, f x * A01.integerCharacter ζ (-k.val) (x.val : ℤ)
  map_add' f g := by
    funext k
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

/-- Unscaled positive-sign synthesis, before division by L. -/
noncomputable def synthesis (L : ℕ) [NeZero L] (ζ : K) :
    (Ch01.Band L → K) →ₗ[K] (Ch01.Lattice L → K) where
  toFun g x := ∑ k : Ch01.Band L, g k * A01.bandCharacter L ζ k x
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

/-- Candidate algebraic inverse; inverse claims explicitly require nonzero scalar L. -/
noncomputable def inverseAnalysis (L : ℕ) [NeZero L] (ζ : K) :
    (Ch01.Band L → K) →ₗ[K] (Ch01.Lattice L → K) := (L : K)⁻¹ • synthesis L ζ

lemma analysis_apply (L : ℕ) [NeZero L] (ζ : K) (f : Ch01.Lattice L → K)
    (k : Ch01.Band L) : analysis L ζ f k =
      ∑ x : Ch01.Lattice L, f x * A01.integerCharacter ζ (-k.val) (x.val : ℤ) := by sorry

lemma synthesis_apply (L : ℕ) [NeZero L] (ζ : K) (g : Ch01.Band L → K)
    (x : Ch01.Lattice L) : synthesis L ζ g x =
      ∑ k : Ch01.Band L, g k * A01.bandCharacter L ζ k x := by sorry

lemma synthesis_analysis (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    (synthesis L ζ).comp (analysis L ζ) = (L : K) • LinearMap.id := by sorry

lemma analysis_synthesis (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    (analysis L ζ).comp (synthesis L ζ) = (L : K) • LinearMap.id := by sorry

lemma inverse_analysis_left (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (hLK : (L : K) ≠ 0) :
    (inverseAnalysis L ζ).comp (analysis L ζ) = LinearMap.id := by sorry

lemma inverse_analysis_right (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (hLK : (L : K) ≠ 0) :
    (analysis L ζ).comp (inverseAnalysis L ζ) = LinearMap.id := by sorry

lemma analysis_bijective (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (hLK : (L : K) ≠ 0) :
    Function.Bijective (analysis L ζ) := by sorry

/-- A nonzero image witness: the position delta at zero analyzes to the constant one. -/
lemma analysis_delta_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    analysis L ζ (Pi.single (0 : Ch01.Lattice L) 1) = fun _ ↦ 1 := by sorry

lemma shift_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.shift (A01.bandCharacter L ζ k) = (ζ ^ k.val) • A01.bandCharacter L ζ k := by sorry

lemma inverse_shift_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.inverseShift (A01.bandCharacter L ζ k) =
      (ζ ^ (-k.val)) • A01.bandCharacter L ζ k := by sorry

lemma forward_diff_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.forwardDiff (A01.bandCharacter L ζ k) =
      (ζ ^ k.val - 1) • A01.bandCharacter L ζ k := by sorry

lemma backward_diff_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.backwardDiff (A01.bandCharacter L ζ k) =
      (1 - ζ ^ (-k.val)) • A01.bandCharacter L ζ k := by sorry

lemma laplacian_eigenvalue_factor (ζ : K) (hζ : ζ ≠ 0) (k : ℤ) :
    (ζ ^ k - 1) * (1 - ζ ^ (-k)) = ζ ^ k + ζ ^ (-k) - 2 := by sorry

lemma laplacian_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.laplacian (A01.bandCharacter L ζ k) =
      (ζ ^ k.val + ζ ^ (-k.val) - 2) • A01.bandCharacter L ζ k := by sorry

lemma analysis_forward_diff (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (f : Ch01.Lattice L → K) (k : Ch01.Band L) :
    analysis L ζ (Ch02.forwardDiff f) k = (ζ ^ k.val - 1) * analysis L ζ f k := by sorry

lemma analysis_backward_diff (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (f : Ch01.Lattice L → K) (k : Ch01.Band L) :
    analysis L ζ (Ch02.backwardDiff f) k = (1 - ζ ^ (-k.val)) * analysis L ζ f k := by sorry

lemma analysis_laplacian (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (f : Ch01.Lattice L → K) (k : Ch01.Band L) :
    analysis L ζ (Ch02.laplacian f) k =
      (ζ ^ k.val + ζ ^ (-k.val) - 2) * analysis L ζ f k := by sorry

/-- Counting-inner-product spatial carrier. -/
abbrev PositionSpace (L : ℕ) := EuclideanSpace ℂ (Ch01.Lattice L)

/-- Counting-inner-product signed momentum carrier. -/
abbrev MomentumSpace (L : ℕ) := EuclideanSpace ℂ (Ch01.Band L)

/-- Euclidean-to-function transport; this does not assert a function-norm isometry. -/
noncomputable def positionFunctions (L : ℕ) : PositionSpace L ≃ₗ[ℂ] (Ch01.Lattice L → ℂ) :=
  WithLp.linearEquiv 2 ℂ (Ch01.Lattice L → ℂ)

noncomputable def momentumFunctions (L : ℕ) : MomentumSpace L ≃ₗ[ℂ] (Ch01.Band L → ℂ) :=
  WithLp.linearEquiv 2 ℂ (Ch01.Band L → ℂ)

/-- Canonical unscaled analysis transported to the counting-space carriers. -/
noncomputable def analysisEuclidean (L : ℕ) [NeZero L] : PositionSpace L →ₗ[ℂ] MomentumSpace L :=
  (momentumFunctions L).symm.toLinearMap.comp
    ((analysis L (A01.canonicalRoot L)).comp (positionFunctions L).toLinearMap)

noncomputable def synthesisEuclidean (L : ℕ) [NeZero L] : MomentumSpace L →ₗ[ℂ] PositionSpace L :=
  (positionFunctions L).symm.toLinearMap.comp
    ((synthesis L (A01.canonicalRoot L)).comp (momentumFunctions L).toLinearMap)

/-- Normalized U remains a linear map in Phase A. -/
noncomputable def unitaryFourier (L : ℕ) [NeZero L] : PositionSpace L →ₗ[ℂ] MomentumSpace L :=
  (A01.normalization L : ℂ) • analysisEuclidean L

/-- Positive-sign candidate normalized inverse. -/
noncomputable def inverseUnitaryFourier (L : ℕ) [NeZero L] : MomentumSpace L →ₗ[ℂ] PositionSpace L :=
  (A01.normalization L : ℂ) • synthesisEuclidean L

/-- Transport a frozen Chapter 2 operator without redefining it. -/
noncomputable def transportPositionOperator (L : ℕ)
    (A : Module.End ℂ (Ch01.Lattice L → ℂ)) : Module.End ℂ (PositionSpace L) :=
  (positionFunctions L).symm.toLinearMap.comp (A.comp (positionFunctions L).toLinearMap)

lemma analysis_eq_dft (L : ℕ) [NeZero L] (f : Ch01.Lattice L → ℂ) (k : Ch01.Band L) :
    analysis L (A01.canonicalRoot L) f k =
      ZMod.dft f (Ch01.bandProjection L k) := by sorry

lemma inverse_analysis_eq_inv_dft (L : ℕ) [NeZero L] (g : Ch01.Band L → ℂ)
    (x : Ch01.Lattice L) :
    inverseAnalysis L (A01.canonicalRoot L) g x =
      (ZMod.dft.symm (fun r ↦ g ((A01.bandEquiv L).symm r))) x := by sorry

lemma synthesisEuclidean_analysisEuclidean (L : ℕ) [NeZero L] :
    (synthesisEuclidean L).comp (analysisEuclidean L) = (L : ℂ) • LinearMap.id := by sorry

lemma analysisEuclidean_synthesisEuclidean (L : ℕ) [NeZero L] :
    (analysisEuclidean L).comp (synthesisEuclidean L) = (L : ℂ) • LinearMap.id := by sorry

lemma analysisEuclidean_adjoint (L : ℕ) [NeZero L] :
    (analysisEuclidean L).adjoint = synthesisEuclidean L := by sorry

lemma unitary_inverse_left (L : ℕ) [NeZero L] :
    (inverseUnitaryFourier L).comp (unitaryFourier L) = LinearMap.id := by sorry

lemma unitary_inverse_right (L : ℕ) [NeZero L] :
    (unitaryFourier L).comp (inverseUnitaryFourier L) = LinearMap.id := by sorry

lemma unitary_adjoint (L : ℕ) [NeZero L] :
    (unitaryFourier L).adjoint = inverseUnitaryFourier L := by sorry

lemma unitary_inner (L : ℕ) [NeZero L] (f g : PositionSpace L) :
    inner ℂ (unitaryFourier L f) (unitaryFourier L g) = inner ℂ f g := by sorry

lemma unitary_isometry (L : ℕ) [NeZero L] : Isometry (unitaryFourier L) := by sorry

lemma unitary_surjective (L : ℕ) [NeZero L] :
    Function.Surjective (unitaryFourier L) := by sorry

lemma unitary_laplacian (L : ℕ) [NeZero L] (f : PositionSpace L) (k : Ch01.Band L) :
    momentumFunctions L
      (unitaryFourier L (transportPositionOperator L Ch02.laplacian f)) k =
      (A01.canonicalRoot L ^ k.val + A01.canonicalRoot L ^ (-k.val) - 2) *
        momentumFunctions L (unitaryFourier L f) k := by sorry

lemma canonical_laplacian_dispersion (L : ℕ) [NeZero L] (k : ℤ) :
    A01.canonicalRoot L ^ k + A01.canonicalRoot L ^ (-k) - 2 =
      ((-4 * Real.sin (Real.pi * (k : ℝ) / (L : ℝ)) ^ 2 : ℝ) : ℂ) := by sorry

lemma singleton_analysis (f : Ch01.Lattice 1 → ℂ) (k : Ch01.Band 1) :
    analysis 1 (A01.canonicalRoot 1) f k = f 0 := by sorry

end Bosonize.Ch03
