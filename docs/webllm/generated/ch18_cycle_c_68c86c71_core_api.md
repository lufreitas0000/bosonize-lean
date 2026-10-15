# CH18 exact Core API context

Definitions/context and theorem headers from committed Core; proof bodies omitted. Source hashes identify complete files. Import Bosonize to use the declarations. This digest does not compile Lean.


## Bosonize/Core/A01FourierCharacters.lean

SHA-256: b6ede9e474ef2ad05b8d904061ba7250dd7e404e524e6ec09261de4a1645fd8a

### Data and context

```text
module

public

import Bosonize.Core.Ch01LatticeBand

public

import Mathlib.Analysis.Fourier.ZMod

public

import Mathlib.Analysis.SpecialFunctions.Pow.Real

public

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public

section

namespace Bosonize.A01

open scoped BigOperators

variable {K : Type*} [Field K]

def integerCharacter (ζ : K) (k x : ℤ) : K := ζ ^ (k * x)

def residueCharacter (L : ℕ) (ζ : K) (k x : Ch01.Lattice L) : K :=
  integerCharacter ζ (k.val : ℤ) (x.val : ℤ)

def bandCharacter (L : ℕ) (ζ : K) (k : Ch01.Band L) (x : Ch01.Lattice L) : K :=
  integerCharacter ζ k.val (x.val : ℤ)

noncomputable def bandEquiv (L : ℕ) [NeZero L] : Ch01.Band L ≃ Ch01.Lattice L :=
  Equiv.ofBijective (Ch01.bandProjection L)
    (Ch01.band_projection_bijective L (Nat.pos_of_ne_zero (NeZero.ne L)))

noncomputable def canonicalRoot (L : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (L : ℂ))

noncomputable def normalization (L : ℕ) : ℝ := (Real.sqrt (L : ℝ))⁻¹

end Bosonize.A01
```

### Proved headers

```text
lemma root_pow_size (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) : ζ ^ L = 1

lemma root_ne_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) : ζ ≠ 0

lemma character_representative_independent (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k x s t : ℤ) : integerCharacter ζ (k + s * (L : ℤ)) (x + t * (L : ℤ)) = integerCharacter ζ k x

lemma residue_character_int_cast (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : residueCharacter L ζ (k : Ch01.Lattice L) (x : Ch01.Lattice L) = integerCharacter ζ k x

lemma residue_character_add_right (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k x y : Ch01.Lattice L) : residueCharacter L ζ k (x + y) = residueCharacter L ζ k x * residueCharacter L ζ k y

lemma residue_character_add_left (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k p x : Ch01.Lattice L) : residueCharacter L ζ (k + p) x = residueCharacter L ζ k x * residueCharacter L ζ p x

lemma residue_character_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (x : Ch01.Lattice L) : residueCharacter L ζ 0 x = 1

lemma residue_character_neg (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k x : Ch01.Lattice L) : residueCharacter L ζ (-k) x = (residueCharacter L ζ k x)⁻¹

lemma residue_character_sub (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k p x : Ch01.Lattice L) : residueCharacter L ζ (k - p) x = residueCharacter L ζ k x * (residueCharacter L ζ p x)⁻¹

lemma character_ne_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : integerCharacter ζ k x ≠ 0

lemma character_nontrivial (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Lattice L) (hk : k ≠ 0) : ∃ x : Ch01.Lattice L, residueCharacter L ζ k x ≠ 1

lemma band_character_projection (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) (x : Ch01.Lattice L) : bandCharacter L ζ k x = residueCharacter L ζ (Ch01.bandProjection L k) x

lemma band_character_add (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) (x : Ch01.Lattice L) : bandCharacter L ζ (Ch01.bandAdd L (Nat.pos_of_ne_zero (NeZero.ne L)) k p) x = bandCharacter L ζ k x * bandCharacter L ζ p x

lemma band_character_neg (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) (x : Ch01.Lattice L) : bandCharacter L ζ (Ch01.bandNeg L (Nat.pos_of_ne_zero (NeZero.ne L)) k) x = integerCharacter ζ (-k.val) (x.val : ℤ)

lemma band_character_sub (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) (x : Ch01.Lattice L) : bandCharacter L ζ (Ch01.bandAdd L (Nat.pos_of_ne_zero (NeZero.ne L)) k (Ch01.bandNeg L (Nat.pos_of_ne_zero (NeZero.ne L)) p)) x = integerCharacter ζ (k.val - p.val) (x.val : ℤ)

lemma sum_band_eq_sum_lattice (L : ℕ) [NeZero L] (f : Ch01.Lattice L → K) : (∑ k : Ch01.Band L, f (Ch01.bandProjection L k)) = ∑ x : Ch01.Lattice L, f x

lemma character_sum (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Lattice L) : (∑ x : Ch01.Lattice L, residueCharacter L ζ k x) = if k = 0 then (L : K) else 0

lemma character_orthogonality (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k p : Ch01.Band L) : (∑ x : Ch01.Lattice L, integerCharacter ζ (k.val - p.val) (x.val : ℤ)) = if k = p then (L : K) else 0

lemma dual_character_orthogonality (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (x y : Ch01.Lattice L) : (∑ k : Ch01.Band L, integerCharacter ζ k.val ((x.val : ℤ) - (y.val : ℤ))) = if x = y then (L : K) else 0

lemma canonical_root_primitive (L : ℕ) [NeZero L] : IsPrimitiveRoot (canonicalRoot L) L

lemma canonical_character_std (L : ℕ) [NeZero L] (k x : Ch01.Lattice L) : residueCharacter L (canonicalRoot L) k x = ZMod.stdAddChar (k * x)

lemma complex_character_conj (L : ℕ) [NeZero L] (ζ : ℂ) (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : star (integerCharacter ζ k x) = integerCharacter ζ (-k) x

lemma complex_character_norm (L : ℕ) [NeZero L] (ζ : ℂ) (hζ : IsPrimitiveRoot ζ L) (k x : ℤ) : ‖integerCharacter ζ k x‖ = 1

lemma normalization_pos (L : ℕ) [NeZero L] : 0 < normalization L

lemma normalization_square (L : ℕ) [NeZero L] : (L : ℝ) * normalization L ^ 2 = 1

lemma normalization_conj (L : ℕ) : star (normalization L : ℂ) = (normalization L : ℂ)

lemma normalization_square_complex (L : ℕ) [NeZero L] : (L : ℂ) * (normalization L : ℂ) ^ 2 = 1

lemma normalization_car_coefficient (L : ℕ) [NeZero L] : ‖(normalization L : ℂ)‖ ^ 2 * (L : ℝ) = 1

lemma singleton_character (ζ : K) (hζ : IsPrimitiveRoot ζ 1) (k : Ch01.Band 1) (x : Ch01.Lattice 1) : bandCharacter 1 ζ k x = 1

lemma nyquist_character_neg (L : ℕ) [NeZero L] (hEven : Even L) (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) (hk : k.val = ((L / 2 : ℕ) : ℤ)) (x : Ch01.Lattice L) : integerCharacter ζ (-k.val) (x.val : ℤ) = bandCharacter L ζ k x
```


## Bosonize/Core/Ch03Fourier.lean

SHA-256: 6d0ba9cd4751c7cb321bc8cc786f355b768ee84a28ea6251628e495972160fed

### Data and context

```text
module

public

import Bosonize.Core.Ch02UmbralCalculus

public

import Bosonize.Core.A01FourierCharacters

public

import Mathlib.Analysis.InnerProductSpace.PiL2

public

import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public

section

namespace Bosonize.Ch03

open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def analysis (L : ℕ) [NeZero L] (ζ : K) :
    (Ch01.Lattice L → K) →ₗ[K] (Ch01.Band L → K) where
  toFun f k := ∑ x : Ch01.Lattice L, f x * A01.integerCharacter ζ (-k.val) (x.val : ℤ)
  map_add' f g := by
    funext k
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

noncomputable def synthesis (L : ℕ) [NeZero L] (ζ : K) :
    (Ch01.Band L → K) →ₗ[K] (Ch01.Lattice L → K) where
  toFun g x := ∑ k : Ch01.Band L, g k * A01.bandCharacter L ζ k x
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

noncomputable def inverseAnalysis (L : ℕ) [NeZero L] (ζ : K) :
    (Ch01.Band L → K) →ₗ[K] (Ch01.Lattice L → K) := (L : K)⁻¹ • synthesis L ζ

abbrev PositionSpace (L : ℕ) := EuclideanSpace ℂ (Ch01.Lattice L)

abbrev MomentumSpace (L : ℕ) := EuclideanSpace ℂ (Ch01.Band L)

noncomputable def positionFunctions (L : ℕ) : PositionSpace L ≃ₗ[ℂ] (Ch01.Lattice L → ℂ) :=
  WithLp.linearEquiv 2 ℂ (Ch01.Lattice L → ℂ)

noncomputable def momentumFunctions (L : ℕ) : MomentumSpace L ≃ₗ[ℂ] (Ch01.Band L → ℂ) :=
  WithLp.linearEquiv 2 ℂ (Ch01.Band L → ℂ)

noncomputable def analysisEuclidean (L : ℕ) [NeZero L] : PositionSpace L →ₗ[ℂ] MomentumSpace L :=
  (momentumFunctions L).symm.toLinearMap.comp
    ((analysis L (A01.canonicalRoot L)).comp (positionFunctions L).toLinearMap)

noncomputable def synthesisEuclidean (L : ℕ) [NeZero L] : MomentumSpace L →ₗ[ℂ] PositionSpace L :=
  (positionFunctions L).symm.toLinearMap.comp
    ((synthesis L (A01.canonicalRoot L)).comp (momentumFunctions L).toLinearMap)

noncomputable def unitaryFourier (L : ℕ) [NeZero L] : PositionSpace L →ₗ[ℂ] MomentumSpace L :=
  (A01.normalization L : ℂ) • analysisEuclidean L

noncomputable def inverseUnitaryFourier (L : ℕ) [NeZero L] : MomentumSpace L →ₗ[ℂ] PositionSpace L :=
  (A01.normalization L : ℂ) • synthesisEuclidean L

noncomputable def transportPositionOperator (L : ℕ)
    (A : Module.End ℂ (Ch01.Lattice L → ℂ)) : Module.End ℂ (PositionSpace L) :=
  (positionFunctions L).symm.toLinearMap.comp (A.comp (positionFunctions L).toLinearMap)

end Bosonize.Ch03
```

### Proved headers

```text
lemma analysis_apply (L : ℕ) [NeZero L] (ζ : K) (f : Ch01.Lattice L → K) (k : Ch01.Band L) : analysis L ζ f k = ∑ x : Ch01.Lattice L, f x * A01.integerCharacter ζ (-k.val) (x.val : ℤ)

lemma synthesis_apply (L : ℕ) [NeZero L] (ζ : K) (g : Ch01.Band L → K) (x : Ch01.Lattice L) : synthesis L ζ g x = ∑ k : Ch01.Band L, g k * A01.bandCharacter L ζ k x

lemma synthesis_analysis (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) : (synthesis L ζ).comp (analysis L ζ) = (L : K) • LinearMap.id

lemma analysis_synthesis (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) : (analysis L ζ).comp (synthesis L ζ) = (L : K) • LinearMap.id

lemma inverse_analysis_left (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (hLK : (L : K) ≠ 0) : (inverseAnalysis L ζ).comp (analysis L ζ) = LinearMap.id

lemma inverse_analysis_right (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (hLK : (L : K) ≠ 0) : (analysis L ζ).comp (inverseAnalysis L ζ) = LinearMap.id

lemma analysis_bijective (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (hLK : (L : K) ≠ 0) : Function.Bijective (analysis L ζ)

lemma analysis_delta_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) : analysis L ζ (Pi.single (0 : Ch01.Lattice L) 1) = fun _ ↦ 1

lemma shift_character (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) : Ch02.shift (A01.bandCharacter L ζ k) = (ζ ^ k.val) • A01.bandCharacter L ζ k

lemma inverse_shift_character (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) : Ch02.inverseShift (A01.bandCharacter L ζ k) = (ζ ^ (-k.val)) • A01.bandCharacter L ζ k

lemma forward_diff_character (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) : Ch02.forwardDiff (A01.bandCharacter L ζ k) = (ζ ^ k.val - 1) • A01.bandCharacter L ζ k

lemma backward_diff_character (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) : Ch02.backwardDiff (A01.bandCharacter L ζ k) = (1 - ζ ^ (-k.val)) • A01.bandCharacter L ζ k

lemma laplacian_eigenvalue_factor (ζ : K) (hζ : ζ ≠ 0) (k : ℤ) : (ζ ^ k - 1) * (1 - ζ ^ (-k)) = ζ ^ k + ζ ^ (-k) - 2

lemma laplacian_character (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) : Ch02.laplacian (A01.bandCharacter L ζ k) = (ζ ^ k.val + ζ ^ (-k.val) - 2) • A01.bandCharacter L ζ k

lemma analysis_forward_diff (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (f : Ch01.Lattice L → K) (k : Ch01.Band L) : analysis L ζ (Ch02.forwardDiff f) k = (ζ ^ k.val - 1) * analysis L ζ f k

lemma analysis_backward_diff (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (f : Ch01.Lattice L → K) (k : Ch01.Band L) : analysis L ζ (Ch02.backwardDiff f) k = (1 - ζ ^ (-k.val)) * analysis L ζ f k

lemma analysis_laplacian (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) (f : Ch01.Lattice L → K) (k : Ch01.Band L) : analysis L ζ (Ch02.laplacian f) k = (ζ ^ k.val + ζ ^ (-k.val) - 2) * analysis L ζ f k

lemma analysis_eq_dft (L : ℕ) [NeZero L] (f : Ch01.Lattice L → ℂ) (k : Ch01.Band L) : analysis L (A01.canonicalRoot L) f k = ZMod.dft f (Ch01.bandProjection L k)

lemma inverse_analysis_eq_inv_dft (L : ℕ) [NeZero L] (g : Ch01.Band L → ℂ) (x : Ch01.Lattice L) : inverseAnalysis L (A01.canonicalRoot L) g x = (ZMod.dft.symm (fun r ↦ g ((A01.bandEquiv L).symm r))) x

lemma synthesisEuclidean_analysisEuclidean (L : ℕ) [NeZero L] : (synthesisEuclidean L).comp (analysisEuclidean L) = (L : ℂ) • LinearMap.id

lemma analysisEuclidean_synthesisEuclidean (L : ℕ) [NeZero L] : (analysisEuclidean L).comp (synthesisEuclidean L) = (L : ℂ) • LinearMap.id

lemma analysisEuclidean_adjoint (L : ℕ) [NeZero L] : (analysisEuclidean L).adjoint = synthesisEuclidean L

lemma unitary_inverse_left (L : ℕ) [NeZero L] : (inverseUnitaryFourier L).comp (unitaryFourier L) = LinearMap.id

lemma unitary_inverse_right (L : ℕ) [NeZero L] : (unitaryFourier L).comp (inverseUnitaryFourier L) = LinearMap.id

lemma unitary_adjoint (L : ℕ) [NeZero L] : (unitaryFourier L).adjoint = inverseUnitaryFourier L

lemma unitary_inner (L : ℕ) [NeZero L] (f g : PositionSpace L) : inner ℂ (unitaryFourier L f) (unitaryFourier L g) = inner ℂ f g

lemma unitary_isometry (L : ℕ) [NeZero L] : Isometry (unitaryFourier L)

lemma unitary_surjective (L : ℕ) [NeZero L] : Function.Surjective (unitaryFourier L)

lemma unitary_laplacian (L : ℕ) [NeZero L] (f : PositionSpace L) (k : Ch01.Band L) : momentumFunctions L (unitaryFourier L (transportPositionOperator L Ch02.laplacian f)) k = (A01.canonicalRoot L ^ k.val + A01.canonicalRoot L ^ (-k.val) - 2) * momentumFunctions L (unitaryFourier L f) k

lemma canonical_laplacian_dispersion (L : ℕ) [NeZero L] (k : ℤ) : A01.canonicalRoot L ^ k + A01.canonicalRoot L ^ (-k) - 2 = ((-4 * Real.sin (Real.pi * (k : ℝ) / (L : ℝ)) ^ 2 : ℝ) : ℂ)

lemma singleton_analysis (f : Ch01.Lattice 1 → ℂ) (k : Ch01.Band 1) : analysis 1 (A01.canonicalRoot 1) f k = f 0
```


## Bosonize/Core/Ch10Heisenberg.lean

SHA-256: b60b521055ca01363a033e227f473e9bb51a21abc58d92fc668d1ab5c49af735

### Data and context

```text
module

public

import Bosonize.Core.A04CurrentMargins

@[expose] public

section

namespace Bosonize.Ch10

open scoped BigOperators Classical

noncomputable def densityWord (h : ℕ) (ds : List ℤ) : Ch09.Operators h :=
  A03.applicationWord (ds.map (Ch09.rho h))

def writtenExcursion (ds : List ℤ) : ℤ := A03.upwardExcursion ds.reverse

def schwingerCoefficient (m n : ℤ) : ℂ := if m+n=0 then -(m : ℂ) else 0

end Bosonize.Ch10
```

### Proved headers

```text
lemma rho_opposite_edge (h m : ℕ) (hm : m ≤ h) : A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ)) = A04.diagonalEdge h m

lemma rho_schwinger_m1 (h m K : ℕ) (hh : 0 < h) (N : ℤ) (hmargin : (m : ℤ)+(K : ℤ)+|N| ≤ (h : ℤ)) : ∀ v ∈ Ch07.fixedBudget h N (K : ℤ), A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ)) v = (m : ℂ) • v

lemma rho_schwinger_signed (h : ℕ) (hh : 0 < h) (m : ℕ) (N K : ℤ) (hmargin : (m : ℤ)+K+|N| ≤ (h : ℤ)) : ∀ v ∈ Ch07.fixedBudget h N K, A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ)) v = (m : ℂ) • v

lemma rho_offdiagonal_m2 (h : ℕ) (hh : 0 < h) (m n N K : ℤ) (hmn : m+n ≠ 0) (hmargin : |m|+|n|+K+|N| ≤ (h : ℤ)) : ∀ v ∈ Ch07.fixedBudget h N K, A02.commutator (Ch09.rho h m) (Ch09.rho h n) v = 0

lemma rho_signed_ccr (h : ℕ) (hh : 0 < h) (m n N K : ℤ) (hmargin : |m|+|n|+K+|N| ≤ (h : ℤ)) : ∀ v ∈ Ch07.fixedBudget h N K, A02.commutator (Ch09.rho h m) (Ch09.rho h n) v = schwingerCoefficient m n • v

lemma normal_commutator_eq (h : ℕ) (m n : ℤ) : A02.commutator (Ch09.normalRho h m) (Ch09.normalRho h n) = A02.commutator (Ch09.rho h m) (Ch09.rho h n)

lemma normal_signed_ccr (h : ℕ) (hh : 0 < h) (m n N K : ℤ) (hmargin : |m|+|n|+K+|N| ≤ (h : ℤ)) : ∀ v ∈ Ch07.fixedBudget h N K, A02.commutator (Ch09.normalRho h m) (Ch09.normalRho h n) v = schwingerCoefficient m n • v

lemma normal_uniform_ccr (h M : ℕ) (hh : 0 < h) (m n N K : ℤ) (hm : |m| ≤ (M : ℤ)) (hn : |n| ≤ (M : ℤ)) (hmargin : 2*(M : ℤ)+K+|N| ≤ (h : ℤ)) : ∀ v ∈ Ch07.fixedBudget h N K, A02.commutator (Ch09.normalRho h m) (Ch09.normalRho h n) v = schwingerCoefficient m n • v

lemma reconstructed_density_ccr (h : ℕ) [NeZero (2*h)] (hh : 0 < h) (b : Ch06Ext.BoundaryTwist (2*h)) (m n N K : ℤ) (hmargin : |m|+|n|+K+|N| ≤ (h : ℤ)) : ∀ v ∈ Ch07.fixedBudget h N K, A02.commutator (Ch09.reconstructedDensity (2*h) b m) (Ch09.reconstructedDensity (2*h) b n) v = schwingerCoefficient m n • v

lemma density_word_nil (h : ℕ) : densityWord h [] = 1

lemma density_word_cons (h : ℕ) (d : ℤ) (ds : List ℤ) : densityWord h (d::ds) = densityWord h ds * Ch09.rho h d

lemma density_word_filtered (h : ℕ) (ds : List ℤ) : A03.Filtered (Ch07.relativeCharge h) (Ch07.excitationEnergy h) (densityWord h ds) 0 ds.sum

lemma density_word_budget (h : ℕ) (ds : List ℤ) (N K : ℤ) : ∀ v ∈ Ch07.fixedBudget h N K, densityWord h ds v ∈ Ch07.fixedBudget h N (K+ds.sum)

lemma density_word_prefix_exact_budget (h : ℕ) (ds : List ℤ) (r : ℕ) (N K : ℤ) : ∀ v ∈ Ch07.fixedBudget h N K, densityWord h (ds.take r) v ∈ Ch07.fixedBudget h N (K+(ds.take r).sum)

lemma density_word_prefix_budget (h : ℕ) (ds : List ℤ) (r : ℕ) (N K : ℤ) : ∀ v ∈ Ch07.fixedBudget h N K, densityWord h (ds.take r) v ∈ Ch07.fixedBudget h N (K+A03.upwardExcursion ds)

lemma normal_ccr_after_prefix (h M : ℕ) (hh : 0 < h) (ds : List ℤ) (r : ℕ) (m n N K : ℤ) (hm : |m| ≤ (M : ℤ)) (hn : |n| ≤ (M : ℤ)) (hmargin : 2*(M : ℤ)+K+A03.upwardExcursion ds+|N| ≤ (h : ℤ)) : ∀ v ∈ Ch07.fixedBudget h N K, A02.commutator (Ch09.normalRho h m) (Ch09.normalRho h n) (densityWord h (ds.take r) v) = schwingerCoefficient m n • densityWord h (ds.take r) v

lemma written_word_eq (h : ℕ) (ds : List ℤ) : (ds.map (Ch09.rho h)).prod = densityWord h ds.reverse

lemma written_suffix_budget (h : ℕ) (ds : List ℤ) (r : ℕ) (N K : ℤ) : ∀ v ∈ Ch07.fixedBudget h N K, densityWord h (ds.reverse.take r) v ∈ Ch07.fixedBudget h N (K+writtenExcursion ds)

lemma ground_budget_witness (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N) (K : ℕ) : ∃ v ∈ Ch07.fixedBudget h N (K : ℤ), v ≠ 0

lemma rho_empty_commutator (h m : ℕ) : A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ)) (A02.ket (∅ : Ch07.Occupation h)) = 0

lemma rho_global_scalar_impossible (h m : ℕ) (hm : 0 < m) : A02.commutator (Ch09.rho h (-(m : ℤ))) (Ch09.rho h (m : ℤ)) ≠ (m : ℂ) • (1 : Ch09.Operators h)
```


## Bosonize/Core/A05MultiSpecies.lean

SHA-256: bb9055adcf9358d5f2274666205d31dc3073716fe53e5f6bf02a983f92335bc2

### Data and context

```text
module

public

import Bosonize.Core.Ch11HaldaneCompleteness

public

import Mathlib.Order.Prod.Lex.Basic

@[expose] public

section

namespace Bosonize.A05

open scoped BigOperators Classical

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

abbrev Mode (σ : Type*) (h : ℕ) := σ × Ch01.Band (2*h)

@[instance_reducible] noncomputable def speciesOrder (h : ℕ) : LinearOrder (Mode σ h) :=
  inferInstanceAs (LinearOrder (σ ×ₗ Ch01.Band (2*h)))

noncomputable local instance localModeLinearOrder (h : ℕ) : LinearOrder (Mode σ h) := speciesOrder h

noncomputable local instance localModeLT (h : ℕ) : LT (Mode σ h) := (speciesOrder h).toLT

noncomputable local instance localModeLE (h : ℕ) : LE (Mode σ h) := (speciesOrder h).toLE

noncomputable local instance localModeDecidableEq (h : ℕ) : DecidableEq (Mode σ h) := (speciesOrder h).toDecidableEq

abbrev Occupation (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A02.Occupation (Mode σ h)

abbrev FockSpace (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := A02.FockSpace (Mode σ h)

abbrev Operators (σ : Type*) [Fintype σ] [LinearOrder σ] (h : ℕ) := Module.End ℂ (FockSpace σ h)

noncomputable abbrev jointBudget (h : ℕ) (Ns : σ → ℤ) (K : ℕ) := Ch07.speciesBudget h Ns (K : ℤ)

def admissible (h : ℕ) (Ns : σ → ℤ) : Prop := ∀ ν, Ch07.admissible h (Ns ν)

def r2 (h K : ℕ) (Ns : σ → ℤ) : Prop := ∀ ν, 2*(K : ℤ)+|Ns ν| ≤ (h : ℤ)

noncomputable def jointConfiguration (h : ℕ) (Ss : σ → Ch07.Occupation h) : Occupation σ h :=
  Finset.univ.biUnion (fun ν => (Ss ν).image (fun k => (ν,k)))

noncomputable def groundConfiguration (h : ℕ) (Ns : σ → ℤ) : Occupation σ h :=
  jointConfiguration h (fun ν => Ch07.groundConfiguration h (Ns ν))

noncomputable def groundKet (h : ℕ) (Ns : σ → ℤ) : FockSpace σ h :=
  A02.ket (groundConfiguration h Ns)

noncomputable def tensorVector (h : ℕ) (vs : σ → Ch07.FockSpace h) : FockSpace σ h :=
  (A02.coordinates (Mode σ h)).symm (fun S => ∏ ν, vs ν (Ch07.speciesConfiguration h S ν))

noncomputable def annihilation (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) : Operators σ h :=
  Ch04.annihilation (ν,k)

noncomputable def creation (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) : Operators σ h :=
  Ch04.creation (ν,k)

noncomputable def rho (h : ℕ) (ν : σ) (m : ℤ) : Operators σ h :=
  ∑ z ∈ A04.validPairs (2*h) m, Ch04.hopping (ν,z.1) (ν,z.2)

noncomputable def chargeObservable (h : ℕ) (ν : σ) : Operators σ h :=
  A03.diagonal (fun S => (Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) : ℂ))

noncomputable def creatorWord (h : ℕ) (parts : σ → List ℕ) : Operators σ h :=
  ((Finset.univ : Finset σ).sort (· ≤ ·)).map
    (fun ν => ((parts ν).map (fun m => rho h ν (m : ℤ))).prod) |>.prod

noncomputable def wordState (h : ℕ) (Ns : σ → ℤ) (parts : σ → List ℕ) : FockSpace σ h :=
  creatorWord h parts (groundKet h Ns)

abbrev JointPartitions (σ : Type*) [Fintype σ] (K : ℕ) :=
  {ps : σ → Ch11.BudgetPartitions K // ∑ ν, (ps ν).1.val ≤ K}

noncomputable instance jointPartitionsFintype (K : ℕ) : Fintype (JointPartitions σ K) :=
  Fintype.ofFinite _

def jointEnergy {K : ℕ} (p : JointPartitions σ K) : ℕ := ∑ ν, (p.val ν).1.val

def jointNormalization {K : ℕ} (p : JointPartitions σ K) : ℕ :=
  ∏ ν, Ch11.partitionNormalization (p.val ν).2

noncomputable def partitionState (h : ℕ) (Ns : σ → ℤ) {K : ℕ}
    (p : JointPartitions σ K) : FockSpace σ h :=
  wordState h Ns (fun ν => Ch11.partitionList (p.val ν).2)

noncomputable def liftedAnnihilation (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (ν : σ) (x : ℤ) : Operators σ h :=
  (A01.normalization (2*h) : ℂ) •
    ∑ k : Ch01.Band (2*h), Ch06Ext.twistedCharacter (2*h) (b ν) k x • annihilation h ν k

end Bosonize.A05
```

### Proved headers

```text
omit [Fintype σ] in lemma mode_lt_iff (h : ℕ) (ν η : σ) (k l : Ch01.Band (2*h)) : (ν,k) < (η,l) ↔ ν < η ∨ ν=η ∧ k<l

lemma species_joint_configuration (h : ℕ) (Ss : σ → Ch07.Occupation h) (ν : σ) : Ch07.speciesConfiguration h (jointConfiguration h Ss) ν = Ss ν

lemma joint_species_configuration (h : ℕ) (S : Occupation σ h) : jointConfiguration h (fun ν => Ch07.speciesConfiguration h S ν) = S

lemma tensor_kets (h : ℕ) (Ss : σ → Ch07.Occupation h) : tensorVector h (fun ν => A02.ket (Ss ν)) = A02.ket (jointConfiguration h Ss)

lemma tensor_inner (h : ℕ) (vs ws : σ → Ch07.FockSpace h) : inner ℂ (tensorVector h vs) (tensorVector h ws) = ∏ ν, inner ℂ (vs ν) (ws ν)

lemma preceding_count_split (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) (S : Occupation σ h) : Ch04.precedingCount (ν,k) S = (∑ η ∈ Finset.univ.filter (· < ν), (Ch07.speciesConfiguration h S η).card) + Ch04.precedingCount k (Ch07.speciesConfiguration h S ν)

lemma hopping_tensor (h : ℕ) (ν : σ) (p k : Ch01.Band (2*h)) (vs : σ → Ch07.FockSpace h) : Ch04.hopping (ν,p) (ν,k) (tensorVector h vs) = tensorVector h (Function.update vs ν (Ch04.hopping p k (vs ν)))

lemma rho_tensor (h : ℕ) (ν : σ) (m : ℤ) (vs : σ → Ch07.FockSpace h) : rho h ν m (tensorVector h vs) = tensorVector h (Function.update vs ν (Ch09.rho h m (vs ν)))

lemma word_tensor (h : ℕ) (Ns : σ → ℤ) (hN : admissible h Ns) (parts : σ → List ℕ) : wordState h Ns parts = tensorVector h (fun ν => Ch11.wordState h (Ns ν) (hN ν) (parts ν))

lemma annihilation_car (h : ℕ) (i j : Mode σ h) : A02.anticommutator (annihilation h i.1 i.2) (annihilation h j.1 j.2) = 0

lemma creation_car (h : ℕ) (i j : Mode σ h) : A02.anticommutator (creation h i.1 i.2) (creation h j.1 j.2) = 0

lemma mixed_car (h : ℕ) (i j : Mode σ h) : A02.anticommutator (annihilation h i.1 i.2) (creation h j.1 j.2) = (if i=j then (1 : ℂ) else 0) • (1 : Operators σ h)

lemma creation_adjoint (h : ℕ) (ν : σ) (k : Ch01.Band (2*h)) : LinearMap.adjoint (annihilation h ν k) = creation h ν k

lemma rho_adjoint (h : ℕ) (ν : σ) (m : ℤ) : LinearMap.adjoint (rho h ν m) = rho h ν (-m)

lemma rho_cross_commute (h : ℕ) (ν η : σ) (hne : ν ≠ η) (m n : ℤ) : A02.commutator (rho h ν m) (rho h η n) = 0

lemma rho_positive_commute (h : ℕ) (ν : σ) (m n : ℕ) : A02.commutator (rho h ν (m : ℤ)) (rho h ν (n : ℤ)) = 0

lemma rho_budget_map (h : ℕ) (ν : σ) (m : ℤ) (Ns : σ → ℤ) (K : ℕ) (v : FockSpace σ h) (hv : v ∈ jointBudget h Ns K) : rho h ν m v ∈ Ch07.speciesBudget h Ns ((K : ℤ)+m)

lemma rho_lowering_budget_zero (h : ℕ) (hh : 0 < h) (ν : σ) (m K : ℕ) (hm : K < m) (Ns : σ → ℤ) (v : FockSpace σ h) (hv : v ∈ jointBudget h Ns K) : rho h ν (-(m : ℤ)) v = 0

lemma ground_mem_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : admissible h Ns) (K : ℕ) : groundKet h Ns ∈ jointBudget h Ns K

lemma ground_ne_zero (h : ℕ) (Ns : σ → ℤ) : groundKet h Ns ≠ 0

lemma word_mem_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : admissible h Ns) (parts : σ → List ℕ) (K : ℕ) (hE : ∑ ν, (parts ν).sum ≤ K) : wordState h Ns parts ∈ jointBudget h Ns K

lemma partition_mem_budget (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : admissible h Ns) (K : ℕ) (p : JointPartitions σ K) : partitionState h Ns p ∈ jointBudget h Ns K

omit [LinearOrder σ] in lemma joint_normalization_positive (K : ℕ) (p : JointPartitions σ K) : 0 < jointNormalization p

lemma partition_gram (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) (p q : JointPartitions σ K) : inner ℂ (partitionState h Ns p) (partitionState h Ns q) = if p=q then (jointNormalization p : ℂ) else 0

lemma partition_ne_zero (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) (p : JointPartitions σ K) : partitionState h Ns p ≠ 0

lemma partition_spanning (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) : Submodule.span ℂ (Set.range (partitionState h Ns (K := K))) = jointBudget h Ns K

lemma partition_basis (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : admissible h Ns) (K : ℕ) (hR2 : r2 h K Ns) : ∃ b : Module.Basis (JointPartitions σ K) ℂ (jointBudget h Ns K), ∀ p, (b p : FockSpace σ h) = partitionState h Ns p

lemma charge_budget (h : ℕ) (ν : σ) (Ns : σ → ℤ) (K : ℕ) (v : FockSpace σ h) (hv : v ∈ jointBudget h Ns K) : chargeObservable h ν v = (Ns ν : ℂ) • v
```


## Bosonize/Core/Ch14Mandelstam.lean

SHA-256: 0d3feed562023e5d8a20027021014cc56512d636b58848fa7a8122b61cc320fc

### Data and context

```text
module

public

import Bosonize.Core.Ch13KleinFactors

public

import Bosonize.Core.A05FiniteExponentials

@[expose] public

section

namespace Bosonize.Ch14

open scoped BigOperators Classical

section Cyclic

variable {R V W I : Type*} [Semiring R] [AddCommGroup V] [AddCommGroup W]
  [Module R V] [Module R W]

def creatorWord (G : I → Module.End R V) (is : List I) : Module.End R V :=
  (is.map G).prod

def cyclicSpan (G : I → Module.End R V) (v₀ : V) : Submodule R V :=
  Submodule.span R (Set.range (fun is : List I => creatorWord G is v₀))

end Cyclic

section FiniteCAR

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable local instance localModeLinearOrder (h : ℕ) : LinearOrder (A05.Mode σ h) := A05.speciesOrder h

noncomputable local instance localModeLT (h : ℕ) : LT (A05.Mode σ h) := (A05.speciesOrder h).toLT

noncomputable local instance localModeLE (h : ℕ) : LE (A05.Mode σ h) := (A05.speciesOrder h).toLE

noncomputable local instance localModeDecidableEq (h : ℕ) : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq

def budgetSet (h : ℕ) (Ns : σ → ℤ) (K : ℕ) : Set (A05.Occupation σ h) :=
  {S | (∀ ν, Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = Ns ν) ∧
    Ch07.totalExcitation h S ≤ (K : ℤ)}

noncomputable def projection (h : ℕ) (Ns : σ → ℤ) (K : ℕ) : A05.Operators σ h :=
  A03.coordinateProjection (budgetSet h Ns K)

noncomputable def projectedMap (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ)
    (A : A05.Operators σ h) : A05.jointBudget h Ns Kin →ₗ[ℂ] A05.jointBudget h Nt Kout :=
  (projection h Nt Kout * A).domRestrict (A05.jointBudget h Ns Kin) |>.codRestrict
    (A05.jointBudget h Nt Kout) (fun v => by
      change projection h Nt Kout (A v.val) ∈ A03.coordinateSpace (budgetSet h Nt Kout)
      rw [← A03.projection_range]
      exact ⟨A v.val, rfl⟩)

noncomputable def budgetAdjoint (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ)
    (A : A05.jointBudget h Ns Kin →ₗ[ℂ] A05.jointBudget h Nt Kout) :
    A05.jointBudget h Nt Kout →ₗ[ℂ] A05.jointBudget h Ns Kin :=
  LinearMap.adjoint (𝕜 := ℂ) (E := A05.jointBudget h Ns Kin) (F := A05.jointBudget h Nt Kout) A

noncomputable def groundVector (h : ℕ) (hh : 0<h) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns) (K : ℕ) : A05.jointBudget h Ns K :=
  ⟨A05.groundKet h Ns, A05.ground_mem_budget h hh Ns hN K⟩

noncomputable def wPlus (h M : ℕ) (ν : σ) (x : ℤ) : A05.Operators σ h :=
  ∑ m ∈ Finset.range M, (A01.integerCharacter (A01.canonicalRoot (2*h)) ((m+1 : ℕ) : ℤ) x /
    (m+1 : ℂ)) • A05.rho h ν (-((m+1 : ℕ) : ℤ))

noncomputable def wMinus (h M : ℕ) (ν : σ) (x : ℤ) : A05.Operators σ h :=
  -∑ m ∈ Finset.range M, (A01.integerCharacter (A01.canonicalRoot (2*h)) (-((m+1 : ℕ) : ℤ)) x /
    (m+1 : ℂ)) • A05.rho h ν ((m+1 : ℕ) : ℤ)

noncomputable def compressedPlus (h M : ℕ) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) : A05.Operators σ h :=
  projection h Ns K * wPlus h M ν x * projection h Ns K

noncomputable def compressedMinus (h M : ℕ) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) : A05.Operators σ h :=
  projection h Ns K * wMinus h M ν x * projection h Ns K

noncomputable def zeroScalar (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) : ℂ :=
  Ch06Ext.liftPhase (2*h) (b ν) x * A01.integerCharacter (A01.canonicalRoot (2*h)) (Ns ν) x

noncomputable def zeroMode (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (K : ℕ) : Module.End ℂ (A05.jointBudget h Ns K) :=
  zeroScalar h b Ns ν x • LinearMap.id

noncomputable def physicalMap (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kin Kout : ℕ) :
    A05.jointBudget h Ns Kin →ₗ[ℂ] A05.jointBudget h (Ch13.lowerCharge Ns ν) Kout :=
  projectedMap h Ns (Ch13.lowerCharge Ns ν) Kin Kout (A05.liftedAnnihilation h b ν x)

noncomputable def vertexCandidate (h M : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h))
    (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kin Kout : ℕ) :
    A05.jointBudget h Ns Kin →ₗ[ℂ] A05.jointBudget h (Ch13.lowerCharge Ns ν) Kout :=
  let Nt := Ch13.lowerCharge Ns ν
  (A01.normalization (2*h) : ℂ) •
    (A05Exp.finiteTaylor Kout (projectedMap h Nt Nt Kout Kout (wMinus h M ν x))).comp
      ((projectedMap h Nt Nt Kin Kout LinearMap.id).comp
        ((A05Exp.finiteTaylor Kin (projectedMap h Nt Nt Kin Kin (wPlus h M ν x))).comp
          ((projectedMap h Ns Nt Kin Kin (Ch13.kleinKernel h Ns ν Kin)).comp
            (zeroMode h b Ns ν x Kin))))

end FiniteCAR

end Bosonize.Ch14
```

### Proved headers

```text
theorem cyclic_common_residual (G : I → Module.End R V) (T : I → Module.End R W) (A B : V →ₗ[R] W) (residual : I → V →ₗ[R] W) (v₀ : V) (hcyclic : cyclicSpan G v₀ = ⊤) (hground : A v₀ = B v₀) (hA : ∀ i, A.comp (G i) = (T i).comp A + residual i) (hB : ∀ i, B.comp (G i) = (T i).comp B + residual i) : A = B

lemma projected_map_apply (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ) (A : A05.Operators σ h) (v : A05.jointBudget h Ns Kin) : (projectedMap h Ns Nt Kin Kout A v : A05.FockSpace σ h) = projection h Nt Kout (A v)

lemma projected_map_adjoint (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ) (A : A05.Operators σ h) : budgetAdjoint h Ns Nt Kin Kout (projectedMap h Ns Nt Kin Kout A) = projectedMap h Nt Ns Kout Kin (LinearMap.adjoint A)

lemma vertex_candidate_adjoint (h M : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kin Kout : ℕ) : let Nt := Ch13.lowerCharge Ns ν budgetAdjoint h Ns Nt Kin Kout (vertexCandidate h M b Ns ν x Kin Kout) = (A01.normalization (2*h) : ℂ) • (budgetAdjoint h Ns Ns Kin Kin (zeroMode h b Ns ν x Kin)).comp ((budgetAdjoint h Ns Nt Kin Kin (projectedMap h Ns Nt Kin Kin (Ch13.kleinKernel h Ns ν Kin))).comp ((budgetAdjoint h Nt Nt Kin Kin (A05Exp.finiteTaylor Kin (projectedMap h Nt Nt Kin Kin (wPlus h M ν x)))).comp ((budgetAdjoint h Nt Nt Kin Kout (projectedMap h Nt Nt Kin Kout LinearMap.id)).comp (budgetAdjoint h Nt Nt Kout Kout (A05Exp.finiteTaylor Kout (projectedMap h Nt Nt Kout Kout (wMinus h M ν x)))))))

lemma w_plus_periodic (h M : ℕ) [NeZero (2*h)] (ν : σ) (x w : ℤ) : wPlus h M ν (x+w*(2*h : ℕ)) = wPlus h M ν x

lemma w_minus_periodic (h M : ℕ) [NeZero (2*h)] (ν : σ) (x w : ℤ) : wMinus h M ν (x+w*(2*h : ℕ)) = wMinus h M ν x

lemma w_plus_adjoint (h M : ℕ) [NeZero (2*h)] (ν : σ) (x : ℤ) : LinearMap.adjoint (wPlus h M ν x) = -wMinus h M ν x

lemma w_minus_adjoint (h M : ℕ) [NeZero (2*h)] (ν : σ) (x : ℤ) : LinearMap.adjoint (wMinus h M ν x) = -wPlus h M ν x

lemma compressed_plus_nilpotent (h M : ℕ) (hh : 0<h) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) : compressedPlus h M Ns K ν x ^ (K+1) = 0

lemma compressed_minus_nilpotent (h M : ℕ) (hh : 0<h) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) : compressedMinus h M Ns K ν x ^ (K+1) = 0

lemma projected_plus_nilpotent (h M : ℕ) (hh : 0<h) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) : projectedMap h Ns Ns K K (wPlus h M ν x) ^ (K+1) = 0

lemma projected_minus_nilpotent (h M : ℕ) (hh : 0<h) (Ns : σ → ℤ) (K : ℕ) (ν : σ) (x : ℤ) : projectedMap h Ns Ns K K (wMinus h M ν x) ^ (K+1) = 0

omit [Fintype σ] [LinearOrder σ] in lemma zero_scalar_norm (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x : ℤ) : ‖zeroScalar h b Ns ν x‖ = 1

omit [Fintype σ] [LinearOrder σ] in lemma zero_scalar_winding (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x w : ℤ) : zeroScalar h b Ns ν (x+w*(2*h : ℕ)) = Ch06Ext.holonomy (2*h) (b ν)^w * zeroScalar h b Ns ν x

lemma zero_mode_winding (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x w : ℤ) (K : ℕ) : zeroMode h b Ns ν (x+w*(2*h : ℕ)) K = Ch06Ext.holonomy (2*h) (b ν)^w • zeroMode h b Ns ν x K

lemma zero_mode_adjoint (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x : ℤ) (K : ℕ) : LinearMap.adjoint (𝕜 := ℂ) (E := A05.jointBudget h Ns K) (F := A05.jointBudget h Ns K) (zeroMode h b Ns ν x K) = star (zeroScalar h b Ns ν x) • LinearMap.id

lemma zero_mode_unitary (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x : ℤ) (K : ℕ) : LinearMap.adjoint (𝕜 := ℂ) (E := A05.jointBudget h Ns K) (F := A05.jointBudget h Ns K) (zeroMode h b Ns ν x K) * zeroMode h b Ns ν x K = 1 ∧ zeroMode h b Ns ν x K * LinearMap.adjoint (𝕜 := ℂ) (E := A05.jointBudget h Ns K) (F := A05.jointBudget h Ns K) (zeroMode h b Ns ν x K) = 1

lemma klein_zero_ground (h : ℕ) (hh : 0<h) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x : ℤ) (K : ℕ) (hm : Ch13.pairMargin h K Ns ν) : Ch13.kleinKernel h Ns ν K (zeroScalar h b Ns ν x • A05.groundKet h Ns) = (zeroScalar h b Ns ν x * Ch13.kleinPhase h Ns ν) • A05.groundKet h (Ch13.lowerCharge Ns ν)

lemma physical_occupation_expansion (h : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kout : ℕ) (S : A05.Occupation σ h) : projection h (Ch13.lowerCharge Ns ν) Kout (A05.liftedAnnihilation h b ν x (A02.ket S)) = (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h), if (ν,k) ∈ S then (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) S) • projection h (Ch13.lowerCharge Ns ν) Kout (A02.ket (S.erase (ν,k))) else 0

lemma physical_ground_expansion (h : ℕ) (hh : 0<h) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ) (x : ℤ) (Kin Kout : ℕ) : (physicalMap h b Ns ν x Kin Kout (groundVector h hh Ns hN Kin) : A05.FockSpace σ h) = (A01.normalization (2*h) : ℂ) • ∑ k : Ch01.Band (2*h), if (ν,k) ∈ A05.groundConfiguration h Ns then (Ch06Ext.twistedCharacter (2*h) (b ν) k x * Ch04.fermionSign (ν,k) (A05.groundConfiguration h Ns)) • projection h (Ch13.lowerCharge Ns ν) Kout (A02.ket ((A05.groundConfiguration h Ns).erase (ν,k))) else 0

lemma projected_recurrence_residual (h : ℕ) (Ns Nt : σ → ℤ) (Kin Kout : ℕ) (c rho : A05.Operators σ h) : let Pin := projection h Ns Kin let Pout := projection h Nt Kout (Pout*c*Pin)*(Pin*rho*Pin) - (Pout*rho*Pout)*(Pout*c*Pin) = Pout*(c*rho-rho*c)*Pin - Pout*c*(1-Pin)*rho*Pin + Pout*rho*(1-Pout)*c*Pin

lemma physical_map_winding (h : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x w : ℤ) (Kin Kout : ℕ) : physicalMap h b Ns ν (x+w*(2*h : ℕ)) Kin Kout = Ch06Ext.holonomy (2*h) (b ν)^w • physicalMap h b Ns ν x Kin Kout

lemma vertex_candidate_winding (h M : ℕ) [NeZero (2*h)] (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x w : ℤ) (Kin Kout : ℕ) : vertexCandidate h M b Ns ν (x+w*(2*h : ℕ)) Kin Kout = Ch06Ext.holonomy (2*h) (b ν)^w • vertexCandidate h M b Ns ν x Kin Kout

theorem field_vertex_of_common_residual (h M : ℕ) (b : σ → Ch06Ext.BoundaryTwist (2*h)) (Ns : σ → ℤ) (ν : σ) (x : ℤ) (Kin Kout : ℕ) {I : Type*} (G : I → Module.End ℂ (A05.jointBudget h Ns Kin)) (T : I → Module.End ℂ (A05.jointBudget h (Ch13.lowerCharge Ns ν) Kout)) (residual : I → A05.jointBudget h Ns Kin →ₗ[ℂ] A05.jointBudget h (Ch13.lowerCharge Ns ν) Kout) (v₀ : A05.jointBudget h Ns Kin) (hcyclic : cyclicSpan G v₀ = ⊤) (hground : physicalMap h b Ns ν x Kin Kout v₀ = vertexCandidate h M b Ns ν x Kin Kout v₀) (hA : ∀ i, (physicalMap h b Ns ν x Kin Kout).comp (G i) = (T i).comp (physicalMap h b Ns ν x Kin Kout) + residual i) (hB : ∀ i, (vertexCandidate h M b Ns ν x Kin Kout).comp (G i) = (T i).comp (vertexCandidate h M b Ns ν x Kin Kout) + residual i) : physicalMap h b Ns ν x Kin Kout = vertexCandidate h M b Ns ν x Kin Kout
```


## Bosonize/Core/A06ChiralFields.lean

SHA-256: 77c579ff06238d2801e9861fdf65c5c1efc66fc31d0161efd18a6a386d2fa768

### Data and context

```text
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

namespace Bosonize.A06

open scoped BigOperators

inductive Orientation where
  | right
  | left
  deriving DecidableEq

def orientationSign : Orientation → ℤ
  | .right => 1
  | .left => -1

structure Branches (σ : Type*) where
  rightSpecies : σ
  leftSpecies : σ
  distinct : rightSpecies ≠ leftSpecies

def speciesOf {σ : Type*} (branches : Branches σ) : Orientation → σ
  | .right => branches.rightSpecies
  | .left => branches.leftSpecies

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

def marginAt (h M K : ℕ) (Ns : σ → ℤ) (ν : σ) : Prop :=
  2 * (M : ℤ) + (K : ℤ) + |Ns ν| ≤ (h : ℤ)

def branchMargins (h M K : ℕ) (Ns : σ → ℤ)
    (branches : Branches σ) : Prop :=
  marginAt h M K Ns branches.rightSpecies ∧
    marginAt h M K Ns branches.leftSpecies

noncomputable def latticeCharacter (h : ℕ) (ζ : ℂ) (k : ℤ)
    (x : ZMod (2 * h)) : ℂ :=
  A01.integerCharacter ζ k (x.val : ℤ)

noncomputable def skewKernel (h M : ℕ) (ζ : ℂ)
    (x y : ZMod (2 * h)) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    (latticeCharacter h ζ (m : ℤ) (x - y) -
      latticeCharacter h ζ (-(m : ℤ)) (x - y)) / (m : ℂ)

noncomputable def dirichletKernel (h M : ℕ) (ζ : ℂ)
    (x y : ZMod (2 * h)) : ℂ :=
  ((2 * h : ℕ) : ℂ)⁻¹ *
    ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      latticeCharacter h ζ m (x - y)

def opForwardDiff (h : ℕ) {V : Type*} [AddGroup V]
    (f : ZMod (2 * h) → V) : ZMod (2 * h) → V :=
  fun x => f (x + 1) - f x

def integerLift (h : ℕ) {V : Type*}
    (f : ZMod (2 * h) → V) (x : ℤ) : V :=
  f (x : ZMod (2 * h))

noncomputable def chiralField (h M : ℕ) (ζ : ℂ)
    (branches : Branches σ) (η : Orientation)
    (x : ZMod (2 * h)) : A05.Operators σ h :=
  ∑ m ∈ Finset.Icc 1 M,
    (Complex.I / (m : ℂ)) •
      ((latticeCharacter h ζ (orientationSign η * (m : ℤ)) x •
          A05.rho h (speciesOf branches η) (-(m : ℤ))) -
        (latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) x •
          A05.rho h (speciesOf branches η) (m : ℤ)))

noncomputable def chiralDifferenceExpansion (h M : ℕ) (ζ : ℂ)
    (branches : Branches σ) (η : Orientation)
    (x : ZMod (2 * h)) : A05.Operators σ h :=
  ∑ m ∈ Finset.Icc 1 M,
    (Complex.I / (m : ℂ)) •
      (((A01.integerCharacter ζ (orientationSign η * (m : ℤ)) 1 - 1) *
          latticeCharacter h ζ (orientationSign η * (m : ℤ)) x) •
          A05.rho h (speciesOf branches η) (-(m : ℤ)) -
        ((A01.integerCharacter ζ (-(orientationSign η * (m : ℤ))) 1 - 1) *
          latticeCharacter h ζ (-(orientationSign η * (m : ℤ))) x) •
          A05.rho h (speciesOf branches η) (m : ℤ))

end Bosonize.A06
```

### Proved headers

```text
lemma lattice_character_shift (h : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (k : ℤ) (x : ZMod (2 * h)) : latticeCharacter h ζ k (x + 1) = A01.integerCharacter ζ k 1 * latticeCharacter h ζ k x

lemma lattice_character_conj (h : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (k : ℤ) (x : ZMod (2 * h)) : star (latticeCharacter h ζ k x) = latticeCharacter h ζ (-k) x

lemma integer_lift_periodic (h : ℕ) {V : Type*} (f : ZMod (2 * h) → V) (x : ℤ) : integerLift h f (x + (2 * h : ℕ)) = integerLift h f x

lemma forward_diff_add (h : ℕ) {V : Type*} [AddCommGroup V] (f g : ZMod (2 * h) → V) (x : ZMod (2 * h)) : opForwardDiff h (fun y => f y + g y) x = opForwardDiff h f x + opForwardDiff h g x

lemma forward_diff_smul (h : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V] (a : ℂ) (f : ZMod (2 * h) → V) (x : ZMod (2 * h)) : opForwardDiff h (fun y => a • f y) x = a • opForwardDiff h f x

lemma forward_diff_sum_zero (h : ℕ) [NeZero (2 * h)] {V : Type*} [AddCommGroup V] (f : ZMod (2 * h) → V) : (∑ x : ZMod (2 * h), opForwardDiff h f x) = 0

lemma chiral_adjoint (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : Branches σ) (η : Orientation) (x : ZMod (2 * h)) : LinearMap.adjoint (chiralField h M ζ branches η x) = chiralField h M ζ branches η x

lemma chiral_forward_diff (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : Branches σ) (η : Orientation) (x : ZMod (2 * h)) : opForwardDiff h (chiralField h M ζ branches η) x = chiralDifferenceExpansion h M ζ branches η x

lemma joint_signed_current_commutator (h K : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ) (m n : ℤ) (hmargin : |m| + |n| + (K : ℤ) + |Ns ν| ≤ (h : ℤ)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (A05.rho h ν m) (A05.rho h ν n) v = Ch10.schwingerCoefficient m n • v

lemma chiral_cross_commute (h M : ℕ) (ζ : ℂ) (branches : Branches σ) (x y : ZMod (2 * h)) : A02.commutator (chiralField h M ζ branches .right x) (chiralField h M ζ branches .left y) = 0

lemma chiral_same_commutator_on_budget (h M K : ℕ) (hh : 0 < h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : Branches σ) (η : Orientation) (Ns : σ → ℤ) (hmargin : marginAt h M K Ns (speciesOf branches η)) (x y : ZMod (2 * h)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (chiralField h M ζ branches η x) (chiralField h M ζ branches η y) v = ((orientationSign η : ℂ) * skewKernel h M ζ x y) • v

lemma dirichlet_diagonal (h M : ℕ) (hh : 0 < h) (ζ : ℂ) : dirichletKernel h M ζ (0 : ZMod (2 * h)) 0 = ((2 * M + 1 : ℕ) : ℂ) / ((2 * h : ℕ) : ℂ)

lemma dirichlet_spatial_sum (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (hNoAlias : 2 * M < 2 * h) (x : ZMod (2 * h)) : (∑ y : ZMod (2 * h), dirichletKernel h M ζ x y) = 1

lemma skew_kernel_diff_sum_zero (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (x : ZMod (2 * h)) : (∑ y : ZMod (2 * h), opForwardDiff h (skewKernel h M ζ x) y) = 0

lemma admissible_ground_nonzero (h K : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (hN : A05.admissible h Ns) : ∃ v : A05.FockSpace σ h, v ∈ A05.jointBudget h Ns K ∧ v ≠ 0

lemma concrete_two_branch_parameters : ∃ (h M K : ℕ) (Ns : Fin 2 → ℤ) (branches : Branches (Fin 2)), 0 < h ∧ 1 ≤ M ∧ 2 * M < 2 * h ∧ A05.admissible h Ns ∧ branchMargins h M K Ns branches ∧ A05.groundKet h Ns ∈ A05.jointBudget h Ns K ∧ A05.groundKet h Ns ≠ 0
```


## Bosonize/Core/A07FiniteNormalOrdering.lean

SHA-256: 1056266f85e56868e20ef4769b8a58cfe88533845bd97db91440d6161d500996

### Data and context

```text
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

namespace Bosonize.A07

open scoped BigOperators

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

abbrev Letter (M : ℕ) := Bool × Fin M × Bool

abbrev QuadraticSymbol (M : ℕ) := (Letter M × Letter M) → ℂ

def orientation (b : Bool) : A06.Orientation :=
  if b then .left else .right

def natMode {M : ℕ} (p : Letter M) : ℕ := p.2.1.val + 1

def phaseSign {M : ℕ} (p : Letter M) : ℤ :=
  if p.2.2 then -1 else 1

def signedMode {M : ℕ} (p : Letter M) : ℤ :=
  if p.2.2 then (natMode p : ℤ) else -(natMode p : ℤ)

noncomputable def current (h M : ℕ) (branches : A06.Branches σ)
    (p : Letter M) : A05.Operators σ h :=
  A05.rho h (A06.speciesOf branches (orientation p.1)) (signedMode p)

noncomputable def rawPair (h M : ℕ) (branches : A06.Branches σ)
    (p q : Letter M) : A05.Operators σ h :=
  current h M branches p * current h M branches q

noncomputable def normalPair (h M : ℕ) (branches : A06.Branches σ)
    (p q : Letter M) : A05.Operators σ h :=
  if p.2.2 = false ∧ q.2.2 = true then
    current h M branches q * current h M branches p
  else rawPair h M branches p q

noncomputable def rawEvaluation (h M : ℕ) (branches : A06.Branches σ)
    (Q : QuadraticSymbol M) : A05.Operators σ h :=
  ∑ pq : Letter M × Letter M, (Q pq) •
    rawPair h M branches pq.1 pq.2

noncomputable def normalEvaluation (h M : ℕ) (branches : A06.Branches σ)
    (Q : QuadraticSymbol M) : A05.Operators σ h :=
  ∑ pq : Letter M × Letter M, (Q pq) •
    normalPair h M branches pq.1 pq.2

def squareSymbol {M : ℕ} (a : Letter M → ℂ) : QuadraticSymbol M :=
  fun pq => a pq.1 * a pq.2

noncomputable def gradientCoefficient (h M : ℕ) (ζ : ℂ)
    (x : ZMod (2 * h)) (p : Letter M) : ℂ :=
  let k : ℤ := phaseSign p * A06.orientationSign (orientation p.1) *
    (natMode p : ℤ)
  ((phaseSign p : ℂ) * Complex.I / (natMode p : ℂ)) *
    (A01.integerCharacter ζ k 1 - 1) *
      A06.latticeCharacter h ζ k x

noncomputable def chiralCoefficient (h M : ℕ) (ζ : ℂ)
    (η : A06.Orientation) (x : ZMod (2 * h)) (p : Letter M) : ℂ :=
  if orientation p.1 = η then gradientCoefficient h M ζ x p else 0

noncomputable def phiCoefficient (h M : ℕ) (ζ : ℂ)
    (x : ZMod (2 * h)) : Letter M → ℂ :=
  gradientCoefficient h M ζ x

noncomputable def thetaCoefficient (h M : ℕ) (ζ : ℂ)
    (x : ZMod (2 * h)) (p : Letter M) : ℂ :=
  (A06.orientationSign (orientation p.1) : ℂ) *
    gradientCoefficient h M ζ x p

noncomputable def dualSquareSymbol (h M : ℕ) (ζ : ℂ)
    (x : ZMod (2 * h)) : QuadraticSymbol M :=
  squareSymbol (phiCoefficient h M ζ x) +
    squareSymbol (thetaCoefficient h M ζ x)

end Bosonize.A07
```

### Proved headers

```text
lemma normal_evaluation_add (h M : ℕ) (branches : A06.Branches σ) (Q R : QuadraticSymbol M) : normalEvaluation h M branches (Q + R) = normalEvaluation h M branches Q + normalEvaluation h M branches R

lemma normal_evaluation_smul (h M : ℕ) (branches : A06.Branches σ) (a : ℂ) (Q : QuadraticSymbol M) : normalEvaluation h M branches (a • Q) = a • normalEvaluation h M branches Q

lemma normal_pair_contraction (h M : ℕ) (branches : A06.Branches σ) (p q : Letter M) : normalPair h M branches p q - rawPair h M branches p q = if p.2.2 = false ∧ q.2.2 = true then A02.commutator (current h M branches q) (current h M branches p) else 0

lemma contraction_on_joint_budget (h M K : ℕ) (hh : 0 < h) (branches : A06.Branches σ) (Ns : σ → ℤ) (p q : Letter M) (hp : p.2.2 = false) (hq : q.2.2 = true) (hbranch : p.1 = q.1) (hmargin : A06.marginAt h M K Ns (A06.speciesOf branches (orientation p.1))) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : (normalPair h M branches p q - rawPair h M branches p q) v = (if natMode p = natMode q then -(natMode p : ℂ) else 0) • v

lemma chiral_gradient_representation (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (η : A06.Orientation) (x : ZMod (2 * h)) : (∑ p : Letter M, (chiralCoefficient h M ζ η x p) • current h M branches p) = A06.opForwardDiff h (A06.chiralField h M ζ branches η) x

lemma dual_square_chiral_decomposition (h M : ℕ) (ζ : ℂ) (x : ZMod (2 * h)) : dualSquareSymbol h M ζ x = (2 : ℂ) • (squareSymbol (chiralCoefficient h M ζ .right x) + squareSymbol (chiralCoefficient h M ζ .left x))
```


## Bosonize/Core/A07InteractionsAndBogoliubov.lean

SHA-256: 1e96db0038b2ae7f012e16d1f6d5a98b43b33661d31f4220cdf3399530fca59f

### Data and context

```text
import Bosonize.Core.A07FiniteNormalOrdering

import Bosonize.Core.Ch16FieldHamiltonian

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

namespace Bosonize.A07Interactions

open scoped BigOperators Classical

section ScalarAndSyntax

def seaIndicator (h : ℕ) (k : Ch01.Band (2 * h)) : ℂ :=
  if k.val ≤ 0 then 1 else 0

def creatorToSeaLetter (h : ℕ) (k : Ch01.Band (2 * h)) :
    Bool × Ch01.Band (2 * h) :=
  (decide (0 < k.val), k)

def annihilatorToSeaLetter (h : ℕ) (k : Ch01.Band (2 * h)) :
    Bool × Ch01.Band (2 * h) :=
  (decide (k.val ≤ 0), k)

def seaInversions (h : ℕ) : List (Bool × Ch01.Band (2 * h)) → ℕ
  | [] => 0
  | (true, _) :: rest => seaInversions h rest
  | (false, _) :: rest => (rest.filter (fun l => l.1)).length + seaInversions h rest

def bilinearWord (h : ℕ) (a b : Ch01.Band (2 * h)) :
    List (Bool × Ch01.Band (2 * h)) :=
  [creatorToSeaLetter h a, annihilatorToSeaLetter h b]

def quarticWord (h : ℕ) (a b c d : Ch01.Band (2 * h)) :
    List (Bool × Ch01.Band (2 * h)) :=
  [creatorToSeaLetter h a, annihilatorToSeaLetter h b,
   creatorToSeaLetter h c, annihilatorToSeaLetter h d]

def seaWickWeight (h M : ℕ) (k : Ch01.Band (2 * h)) : ℤ :=
  if k.val ≤ 0 then 1 + 2 * min (M : ℤ) (-k.val)
  else 1 + 2 * min (M : ℤ) (k.val - 1)

def oppositeOrientation : A06.Orientation → A06.Orientation
  | .right => .left
  | .left => .right

structure HyperbolicParams (v1 v2 : ℝ) where
  u : ℝ
  c : ℝ
  s : ℝ
  u_pos : 0 < u
  c_pos : 0 < c
  u_sq : u ^ 2 = v1 ^ 2 - v2 ^ 2
  hyperbolic_id : c ^ 2 - s ^ 2 = 1
  match_v1 : v1 = u * (c ^ 2 + s ^ 2)
  match_v2 : v2 = 2 * u * c * s

end ScalarAndSyntax

section Operators

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def seaQuasiAnnihilator (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  if k.val ≤ 0 then A05.creation h ν k else A05.annihilation h ν k

noncomputable def seaQuasiCreator (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  if k.val ≤ 0 then A05.annihilation h ν k else A05.creation h ν k

noncomputable def evalSeaLetter (h : ℕ) (ν : σ)
    (l : Bool × Ch01.Band (2 * h)) : A05.Operators σ h :=
  if l.1 then seaQuasiCreator h ν l.2 else seaQuasiAnnihilator h ν l.2

noncomputable def seaWickWord (h : ℕ) (ν : σ)
    (w : List (Bool × Ch01.Band (2 * h))) : A05.Operators σ h :=
  let creators := w.filter (fun l => l.1)
  let annihilators := w.filter (fun l => !l.1)
  ((-1 : ℂ) ^ seaInversions h w) •
    (((creators ++ annihilators).map (evalSeaLetter h ν)).prod)

noncomputable def numberOp (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  A05.creation h ν k * A05.annihilation h ν k

noncomputable def seaSubtractedNumber (h : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  numberOp h ν k - seaIndicator h k • (1 : A05.Operators σ h)

noncomputable def seaNormalBilinear (h : ℕ) (ν : σ)
    (a b : Ch01.Band (2 * h)) : A05.Operators σ h :=
  A05.creation h ν a * A05.annihilation h ν b -
    (if a = b then seaIndicator h a else 0) • (1 : A05.Operators σ h)

noncomputable def seaNormalRho (h : ℕ) (ν : σ) (m : ℤ) :
    A05.Operators σ h :=
  ∑ z ∈ A04.validPairs (2 * h) m, seaNormalBilinear h ν z.1 z.2

noncomputable def quarticSeaWick (h : ℕ) (ν : σ)
    (a b c d : Ch01.Band (2 * h)) : A05.Operators σ h :=
  seaWickWord h ν (quarticWord h a b c d)

noncomputable def quarticContraction (h : ℕ) (ν : σ)
    (k p : Ch01.Band (2 * h)) : A05.Operators σ h :=
  seaIndicator h p • seaSubtractedNumber h ν k -
    (1 - seaIndicator h k) • seaSubtractedNumber h ν p -
    (seaIndicator h p * (1 - seaIndicator h k)) • (1 : A05.Operators σ h)

noncomputable def seaWickTerm (h M : ℕ) (ν : σ)
    (k : Ch01.Band (2 * h)) : A05.Operators σ h :=
  if k.val ≤ 0 then
    (seaWickWeight h M k : ℂ) • ((1 : A05.Operators σ h) - numberOp h ν k)
  else
    (seaWickWeight h M k : ℂ) • numberOp h ν k

noncomputable def seaWickCorrection (h M : ℕ) (ν : σ) :
    A05.Operators σ h :=
  ∑ k : Ch01.Band (2 * h), seaWickTerm h M ν k

noncomputable def computationalMomentum (h : ℕ) (ν : σ) :
    A05.Operators σ h :=
  ∑ k : Ch01.Band (2 * h), (k.val : ℂ) • seaSubtractedNumber h ν k

noncomputable def speciesRawIntra (h M : ℕ) (ν : σ) :
    A05.Operators σ h :=
  ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
    ∑ z ∈ A04.validPairs (2 * h) m,
      ∑ w ∈ A04.validPairs (2 * h) (-m),
        quarticSeaWick h ν z.1 z.2 w.1 w.2

noncomputable def rawIntraBranch (h M : ℕ) (g4 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
    (speciesRawIntra h M branches.rightSpecies +
      speciesRawIntra h M branches.leftSpecies)

noncomputable def speciesCurrentIntra (h M : ℕ) (ν : σ) :
    A05.Operators σ h :=
  (2 : ℂ) • (∑ m ∈ Finset.Icc 1 M,
    A05.rho h ν (m : ℤ) * A05.rho h ν (-(m : ℤ))) +
    A05.chargeObservable h ν * A05.chargeObservable h ν

noncomputable def currentIntraBranch (h M : ℕ) (g4 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) •
    (speciesCurrentIntra h M branches.rightSpecies +
      speciesCurrentIntra h M branches.leftSpecies)

noncomputable def rawInterBranch (h M : ℕ) (g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  ((g2 : ℂ) / ((2 * h : ℕ) : ℂ)) •
    ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      seaNormalRho h branches.rightSpecies m *
        seaNormalRho h branches.leftSpecies (-m)

noncomputable def hoppingInterBranch (h M : ℕ) (g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  ((g2 : ℂ) / ((2 * h : ℕ) : ℂ)) •
    (A05.chargeObservable h r * A05.chargeObservable h l +
      ∑ m ∈ Finset.Icc 1 M,
        (A05.rho h r (m : ℤ) * A05.rho h l (-(m : ℤ)) +
          A05.rho h r (-(m : ℤ)) * A05.rho h l (m : ℤ)))

noncomputable def pairingInterBranch (h M : ℕ) (g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  ((g2 : ℂ) / ((2 * h : ℕ) : ℂ)) •
    (A05.chargeObservable h r * A05.chargeObservable h l +
      ∑ m ∈ Finset.Icc 1 M,
        (A05.rho h r (m : ℤ) * A05.rho h l (m : ℤ) +
          A05.rho h r (-(m : ℤ)) * A05.rho h l (-(m : ℤ))))

noncomputable def hoppingMode (h m : ℕ) (v1 v2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  (v1 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h r (-(m : ℤ)) +
    A05.rho h l (m : ℤ) * A05.rho h l (-(m : ℤ))) +
  (v2 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h l (-(m : ℤ)) +
    A05.rho h l (m : ℤ) * A05.rho h r (-(m : ℤ)))

noncomputable def pairingMode (h m : ℕ) (v1 v2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  (v1 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h r (-(m : ℤ)) +
    A05.rho h l (m : ℤ) * A05.rho h l (-(m : ℤ))) +
  (v2 : ℂ) • (A05.rho h r (m : ℤ) * A05.rho h l (m : ℤ) +
    A05.rho h r (-(m : ℤ)) * A05.rho h l (-(m : ℤ)))

noncomputable def bogoliubovCreator (h m : ℕ) (c s : ℝ)
    (branches : A06.Branches σ) (η : A06.Orientation) :
    A05.Operators σ h :=
  (c : ℂ) • A05.rho h (A06.speciesOf branches η) (m : ℤ) +
    (s : ℂ) • A05.rho h (A06.speciesOf branches (oppositeOrientation η)) (-(m : ℤ))

noncomputable def bogoliubovAnnihilator (h m : ℕ) (c s : ℝ)
    (branches : A06.Branches σ) (η : A06.Orientation) :
    A05.Operators σ h :=
  (c : ℂ) • A05.rho h (A06.speciesOf branches η) (-(m : ℤ)) +
    (s : ℂ) • A05.rho h (A06.speciesOf branches (oppositeOrientation η)) (m : ℤ)

noncomputable def dressedModeNumber (h m : ℕ) (u c s : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (u : ℂ) • (bogoliubovCreator h m c s branches .right *
      bogoliubovAnnihilator h m c s branches .right +
    bogoliubovCreator h m c s branches .left *
      bogoliubovAnnihilator h m c s branches .left)

end Operators

end Bosonize.A07Interactions
```

### Proved headers

```text
theorem hyperbolic_params_exist (v1 v2 : ℝ) (hstab : |v2| < v1) : ∃ u c s : ℝ, 0 < u ∧ u ^ 2 = v1 ^ 2 - v2 ^ 2 ∧ c ^ 2 - s ^ 2 = 1 ∧ v1 = u * (c ^ 2 + s ^ 2) ∧ v2 = 2 * u * c * s

lemma sea_normal_bilinear_diag (h : ℕ) (ν : σ) (k : Ch01.Band (2 * h)) : seaNormalBilinear h ν k k = if k.val ≤ 0 then -(A05.annihilation h ν k * A05.creation h ν k) else A05.creation h ν k * A05.annihilation h ν k

lemma sea_normal_rho_nonzero (h : ℕ) (ν : σ) (m : ℤ) (hm : m ≠ 0) : seaNormalRho h ν m = A05.rho h ν m

lemma sea_normal_rho_zero (h : ℕ) (ν : σ) : seaNormalRho h ν 0 = A05.chargeObservable h ν

lemma quartic_sea_wick_identity (h : ℕ) (ν : σ) (m : ℤ) (z w : Ch01.Band (2 * h) × Ch01.Band (2 * h)) (hz : z ∈ A04.validPairs (2 * h) m) (hw : w ∈ A04.validPairs (2 * h) (-m)) : quarticSeaWick h ν z.1 z.2 w.1 w.2 = seaNormalBilinear h ν z.1 z.2 * seaNormalBilinear h ν w.1 w.2 + if w.2 = z.1 then quarticContraction h ν z.2 w.2 else 0

lemma quartic_sea_wick_zero_repeated (h : ℕ) (ν : σ) (k : Ch01.Band (2 * h)) : quarticSeaWick h ν k k k k = 0 ∧ seaNormalBilinear h ν k k * seaNormalBilinear h ν k k + quarticContraction h ν k k = 0

lemma species_raw_intra_eq_current_sub_correction (h M : ℕ) (ν : σ) : speciesRawIntra h M ν = speciesCurrentIntra h M ν - seaWickCorrection h M ν

theorem raw_intra_eq_current_sub_correction (h M : ℕ) (g4 : ℝ) (branches : A06.Branches σ) : rawIntraBranch h M g4 branches = currentIntraBranch h M g4 branches - ((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) • (seaWickCorrection h M branches.rightSpecies + seaWickCorrection h M branches.leftSpecies)

lemma sea_wick_correction_ground_zero (h M : ℕ) (hh : 0 < h) (ν : σ) : seaWickCorrection h M ν (A05.groundKet h (fun _ : σ => 0)) = 0

lemma sea_wick_correction_full_band (h M : ℕ) (hh : 0 < h) (hM : h - 1 ≤ M) (ν : σ) : seaWickCorrection h M ν = (2 : ℂ) • computationalMomentum h ν - A05.chargeObservable h ν

theorem raw_inter_eq_hopping (h M : ℕ) (g2 : ℝ) (branches : A06.Branches σ) : rawInterBranch h M g2 branches = hoppingInterBranch h M g2 branches

lemma hopping_mode_kills_ground (h m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (branches : A06.Branches σ) : (A05.rho h branches.rightSpecies (m : ℤ) * A05.rho h branches.leftSpecies (-(m : ℤ)) + A05.rho h branches.rightSpecies (-(m : ℤ)) * A05.rho h branches.leftSpecies (m : ℤ)) (A05.groundKet h Ns) = 0

lemma pairing_mode_ground_nonzero (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (branches : A06.Branches σ) (hmargin : A06.branchMargins h M m Ns branches) : (A05.rho h branches.rightSpecies (m : ℤ) * A05.rho h branches.leftSpecies (m : ℤ) + A05.rho h branches.rightSpecies (-(m : ℤ)) * A05.rho h branches.leftSpecies (-(m : ℤ))) (A05.groundKet h Ns) ≠ 0

lemma hopping_mode_self_adjoint (h m : ℕ) (v1 v2 : ℝ) (branches : A06.Branches σ) : LinearMap.adjoint (hoppingMode h m v1 v2 branches) = hoppingMode h m v1 v2 branches

lemma pairing_mode_self_adjoint (h m : ℕ) (v1 v2 : ℝ) (branches : A06.Branches σ) : LinearMap.adjoint (pairingMode h m v1 v2 branches) = pairingMode h m v1 v2 branches

lemma bogoliubov_creator_adjoint (h m : ℕ) (c s : ℝ) (branches : A06.Branches σ) (η : A06.Orientation) : LinearMap.adjoint (bogoliubovCreator h m c s branches η) = bogoliubovAnnihilator h m c s branches η

theorem bogoliubov_expansion_on_budget (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (v1 v2 : ℝ) (hp : HyperbolicParams v1 v2) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : dressedModeNumber h m hp.u hp.c hp.s branches v = pairingMode h m v1 v2 branches v + ((2 * hp.u * hp.s ^ 2 * (m : ℝ) : ℝ) : ℂ) • v

theorem bogoliubov_ccr_on_budget (h M K m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (bogoliubovAnnihilator h m c s branches η) (bogoliubovCreator h m c s branches η) v = (m : ℂ) • v
```


## Bosonize/Core/A10DiscreteSchriefferWolff.lean

SHA-256: 7ea9ac1c592eed76fc9349ff63592363c2f9efdb0876dc0c93ddf24e9f74b33f

### Data and context

```text
import Bosonize.Core.A07FiniteNormalOrdering

import Bosonize.Core.Ch16FieldHamiltonian

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

import Bosonize.Core.A07InteractionsAndBogoliubov

namespace Bosonize.A10

open scoped BigOperators Classical

section MatrixModels

noncomputable def swGeneratorMatrix {ι : Type*}
    (inLow : ι → Bool) (E : ι → ℝ) (Voff : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  fun i j =>
    if inLow i ≠ inLow j ∧ Voff i j ≠ 0 then
      Voff i j / ((E i - E j : ℝ) : ℂ)
    else 0

noncomputable def diagEnergyMatrix {ι : Type*} [DecidableEq ι]
    (E : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => ((E i : ℝ) : ℂ))

def nonResonant {ι : Type*} (inLow : ι → Bool) (E : ι → ℝ)
    (Voff : Matrix ι ι ℂ) : Prop :=
  ∀ i j : ι, inLow i ≠ inLow j → Voff i j ≠ 0 → E i ≠ E j

def swCounterH0_2x2 : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 1 ∧ j = 1 then 1 else 0

def swCounterV_2x2 : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i ≠ j then 1 else 0

def swCounterS1_2x2 : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 1 then -1 else if i = 1 ∧ j = 0 then 1 else 0

def swCounterP_2x2 : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

def swCounterH0_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    if i = j then
      if i = 0 then 0 else if i = 1 then -1 else 1
    else 0

def swCounterP_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

def swCounterQ_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = j ∧ (i = 1 ∨ i = 2) then 1 else 0

def swCounterV_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    if (i = 0 ∧ (j = 1 ∨ j = 2)) ∨ ((i = 1 ∨ i = 2) ∧ j = 0) then 1
    else 0

def swCounterS1_3x3 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    if i = 0 ∧ j = 1 then 1
    else if i = 0 ∧ j = 2 then -1
    else if i = 1 ∧ j = 0 then -1
    else if i = 2 ∧ j = 0 then 1
    else 0

def swCounterEigenvector_2x2 : Fin 2 → ℂ :=
  fun i => if i = 0 then -2 else 1

end MatrixModels

section BudgetShells

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

def exactShellSet (h : ℕ) (Ns : σ → ℤ) (K : ℕ) :
    Set (A05.Occupation σ h) :=
  {S | (∀ ν, Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = Ns ν) ∧
    Ch07.totalExcitation h S = (K : ℤ)}

noncomputable def lowShellProj (h : ℕ) (Ns : σ → ℤ) (K : ℕ) :
    A05.Operators σ h :=
  Ch14.projection h Ns (K - 1)

noncomputable def highShellProj (h : ℕ) (Ns : σ → ℤ) (K : ℕ) :
    A05.Operators σ h :=
  letI : DecidableEq (A05.Mode σ h) := (A05.speciesOrder h).toDecidableEq
  A03.coordinateProjection (exactShellSet h Ns K)

noncomputable def doubleModeOneKet (h : ℕ) (Ns : σ → ℤ) (ν : σ) :
    A05.FockSpace σ h :=
  A05.rho h ν 1 (A05.rho h ν 1 (A05.groundKet h Ns))

noncomputable def diagPart (h : ℕ) (P Q V : A05.Operators σ h) :
    A05.Operators σ h :=
  P * V * P + Q * V * Q

noncomputable def offDiagPart (h : ℕ) (P Q V : A05.Operators σ h) :
    A05.Operators σ h :=
  P * V * Q + Q * V * P

noncomputable def swSecondOrderCorrection (h : ℕ)
    (P S1 V : A05.Operators σ h) : A05.Operators σ h :=
  ((2 : ℂ)⁻¹) • (P * A02.commutator S1 V * P)

noncomputable def swEffectiveSecondOrder (h : ℕ)
    (P H0 V S1 : A05.Operators σ h) (t : ℝ) : A05.Operators σ h :=
  P * H0 * P + (t : ℂ) • (P * V * P) +
    ((t : ℂ) ^ 2) • swSecondOrderCorrection h P S1 V

noncomputable def bchSecondOrderPolynomial (h : ℕ)
    (H0 V S1 : A05.Operators σ h) (t : ℝ) : A05.Operators σ h :=
  H0 + (t : ℂ) • (V + A02.commutator S1 H0) +
    ((t : ℂ) ^ 2) • (A02.commutator S1 V +
      ((2 : ℂ)⁻¹) • A02.commutator S1 (A02.commutator S1 H0))

end BudgetShells

end Bosonize.A10
```

### Proved headers

```text
theorem sw_generator_commutator_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (inLow : ι → Bool) (E : ι → ℝ) (Voff : Matrix ι ι ℂ) (hBlock : ∀ i j : ι, inLow i = inLow j → Voff i j = 0) (hNonRes : nonResonant inLow E Voff) : swGeneratorMatrix inLow E Voff * diagEnergyMatrix E - diagEnergyMatrix E * swGeneratorMatrix inLow E Voff = -Voff

theorem sw_generator_skew_hermitian {ι : Type*} (inLow : ι → Bool) (E : ι → ℝ) (Voff : Matrix ι ι ℂ) (hHerm : Matrix.conjTranspose Voff = Voff) : Matrix.conjTranspose (swGeneratorMatrix inLow E Voff) = -swGeneratorMatrix inLow E Voff

theorem sw_2x2_truncation_witness : swCounterS1_2x2 * swCounterH0_2x2 - swCounterH0_2x2 * swCounterS1_2x2 = -swCounterV_2x2 ∧ (swCounterP_2x2 * (swCounterS1_2x2 * swCounterV_2x2 - swCounterV_2x2 * swCounterS1_2x2) * swCounterP_2x2) 0 0 = -2 ∧ ((-((2 : ℚ) / 3) ^ 2 : ℚ) ≠ (-1 / 3 : ℚ))

theorem sw_3x3_no_iff_witness : swCounterS1_3x3 * swCounterH0_3x3 - swCounterH0_3x3 * swCounterS1_3x3 = -swCounterV_3x3 ∧ swCounterP_3x3 * swCounterV_3x3 * swCounterQ_3x3 ≠ 0 ∧ swCounterP_3x3 * (swCounterS1_3x3 * swCounterV_3x3 - swCounterV_3x3 * swCounterS1_3x3) * swCounterP_3x3 = 0

theorem sw_2x2_exact_eigenpair : swCounterEigenvector_2x2 ≠ 0 ∧ (swCounterH0_2x2 + ((2 : ℂ) / 3) • swCounterV_2x2).mulVec swCounterEigenvector_2x2 = ((-1 : ℂ) / 3) • swCounterEigenvector_2x2

theorem sw_compressed_bch_second_order (h : ℕ) (P Q H0 V S1 : A05.Operators σ h) (t : ℝ) (hP : P * P = P) (hQ : Q * Q = Q) (hPartition : P + Q = 1) (hPQ : P * Q = 0) (hQP : Q * P = 0) (hBaseline : A02.commutator P H0 = 0) (hSpp : P * S1 * P = 0) (hSqq : Q * S1 * Q = 0) (hGenerator : A02.commutator S1 H0 = -offDiagPart h P Q V) : P * bchSecondOrderPolynomial h H0 V S1 t * P = swEffectiveSecondOrder h P H0 V S1 t

lemma shell_proj_partition (h K : ℕ) (hK : 1 ≤ K) (Ns : σ → ℤ) : lowShellProj h Ns K + highShellProj h Ns K = Ch14.projection h Ns K

lemma shell_proj_orthogonal (h K : ℕ) (hK : 1 ≤ K) (Ns : σ → ℤ) : lowShellProj h Ns K * highShellProj h Ns K = 0 ∧ highShellProj h Ns K * lowShellProj h Ns K = 0

lemma shell_proj_self_adjoint (h K : ℕ) (Ns : σ → ℤ) : LinearMap.adjoint (lowShellProj h Ns K) = lowShellProj h Ns K ∧ LinearMap.adjoint (highShellProj h Ns K) = highShellProj h Ns K

lemma energy_shell_discards_double_mode_one (h : ℕ) (hh : 2 ≤ h) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (ν : σ) (hR2 : A05.r2 h 2 Ns) : doubleModeOneKet h Ns ν ∈ A05.jointBudget h Ns 2 ∧ doubleModeOneKet h Ns ν ≠ 0 ∧ lowShellProj h Ns 2 (doubleModeOneKet h Ns ν) = 0 ∧ highShellProj h Ns 2 (doubleModeOneKet h Ns ν) = doubleModeOneKet h Ns ν

theorem sw_off_zero_implies_effective_exact (h : ℕ) (P Q H0 V : A05.Operators σ h) (t : ℝ) (hPVQ : P * V * Q = 0) (hQVP : Q * V * P = 0) : offDiagPart h P Q V = 0 ∧ swSecondOrderCorrection h P (0 : A05.Operators σ h) V = 0 ∧ swEffectiveSecondOrder h P H0 V (0 : A05.Operators σ h) t = P * H0 * P + (t : ℂ) • (P * V * P)
```


## Bosonize/Core/Ch15DualFields.lean

SHA-256: 30880501f9f71594b9e1cc0af6784428cbc0d48c6e70c8930c5d2c27caa9ff85

### Data and context

```text
import Bosonize.Core.A06ChiralFields

namespace Bosonize.Ch15

open scoped BigOperators

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def phiField (h M : ℕ) (ζ : ℂ)
    (branches : A06.Branches σ) (x : ZMod (2 * h)) : A05.Operators σ h :=
  A06.chiralField h M ζ branches .right x +
    A06.chiralField h M ζ branches .left x

noncomputable def thetaField (h M : ℕ) (ζ : ℂ)
    (branches : A06.Branches σ) (x : ZMod (2 * h)) : A05.Operators σ h :=
  A06.chiralField h M ζ branches .right x -
    A06.chiralField h M ζ branches .left x

end Bosonize.Ch15
```

### Proved headers

```text
lemma phi_adjoint (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (x : ZMod (2 * h)) : LinearMap.adjoint (phiField h M ζ branches x) = phiField h M ζ branches x

lemma theta_adjoint (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (x : ZMod (2 * h)) : LinearMap.adjoint (thetaField h M ζ branches x) = thetaField h M ζ branches x

lemma phi_self_commutator_on_budget (h M K : ℕ) (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (x y : ZMod (2 * h)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (phiField h M ζ branches x) (phiField h M ζ branches y) v = 0

lemma theta_self_commutator_on_budget (h M K : ℕ) (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (x y : ZMod (2 * h)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (thetaField h M ζ branches x) (thetaField h M ζ branches y) v = 0

lemma mixed_commutator_on_budget (h M K : ℕ) (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (x y : ZMod (2 * h)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (phiField h M ζ branches x) (thetaField h M ζ branches y) v = (2 * A06.skewKernel h M ζ x y) • v

lemma mixed_forward_diff_on_budget (h M K : ℕ) (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (x y : ZMod (2 * h)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : A02.commutator (phiField h M ζ branches x) (A06.opForwardDiff h (thetaField h M ζ branches) y) v = (2 * A06.opForwardDiff h (A06.skewKernel h M ζ x) y) • v

theorem zero_mode_obstruction_on_ground (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) (x : ZMod (2 * h)) (c : ℂ) (hc : c ≠ 0) : ¬ (∀ y : ZMod (2 * h), A02.commutator (phiField h M ζ branches x) (A06.opForwardDiff h (thetaField h M ζ branches) y) (A05.groundKet h Ns) = (c * A06.dirichletKernel h M ζ x y) • A05.groundKet h Ns)
```


## Bosonize/Core/Ch16FieldHamiltonian.lean

SHA-256: 54e045da25fcc31e8e18bce5b81b1318adef6955e38ca357e3b7b6c21887e787

### Data and context

```text
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

end Bosonize.Ch16
```

### Proved headers

```text
lemma field_chiral_identity (h M : ℕ) (ζ : ℂ) (branches : A06.Branches σ) (x : ZMod (2 * h)) : localFieldEnergy h M ζ branches x = (2 : ℂ) • (chiralSquare h M ζ branches .right x + chiralSquare h M ζ branches .left x)

lemma chiral_spatial_collapse_on_budget (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hmargin : A06.marginAt h M K Ns (A06.speciesOf branches η)) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : (∑ x : ZMod (2 * h), chiralSquare h M ζ branches η x) v = ((2 : ℂ) • (∑ m ∈ Finset.Icc 1 M, epsilon h ζ m • (A05.rho h (A06.speciesOf branches η) (m : ℤ) * A05.rho h (A06.speciesOf branches η) (-(m : ℤ))))) v

theorem field_weighted_on_budget (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : fieldHamiltonian h M ζ branches v = ((4 : ℂ) • weightedEnergy h M ζ branches) v

theorem field_weighted_after_excursion (h M K excursion : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : marginWithExcursion h M K excursion Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns (K + excursion)) : fieldHamiltonian h M ζ branches v = ((4 : ℂ) • weightedEnergy h M ζ branches) v

lemma error_weighted_on_budget (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hmargin : A06.branchMargins h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : errorOperator h M ζ branches v = ((4 : ℂ) • weightedError h M ζ branches) v

lemma ground_error_zero (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) : errorOperator h M ζ branches (A05.groundKet h Ns) = 0

lemma excited_ket_mem_budget (h K m : ℕ) (hh : 0 < h) (hm : m ≤ K) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (branches : A06.Branches σ) (η : A06.Orientation) : excitedKet h Ns branches η m ∈ A05.jointBudget h Ns K

lemma excited_ket_nonzero (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hcut : m ≤ M) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (branches : A06.Branches σ) (η : A06.Orientation) (hmargin : A06.marginAt h M m Ns (A06.speciesOf branches η)) : excitedKet h Ns branches η m ≠ 0

theorem single_mode_error_eigenvector (h M K m : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (hm : 1 ≤ m) (hcut : m ≤ M) (hK : m ≤ K) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) : errorOperator h M ζ branches (excitedKet h Ns branches η m) = ((4 : ℂ) * (m : ℂ) * (epsilon h ζ m - referenceWeight h ζ)) • excitedKet h Ns branches η m

theorem first_mode_error_zero (h M K : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hK : 1 ≤ K) (hNoAlias : 2 * M < 2 * h) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) : errorOperator h M ζ branches (excitedKet h Ns branches η 1) = 0

theorem error_nonzero_witness (h M K m : ℕ) [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h) (hm : 1 ≤ m) (hcut : m ≤ M) (hK : m ≤ K) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h)) (hweight : epsilon h ζ m ≠ referenceWeight h ζ) (branches : A06.Branches σ) (η : A06.Orientation) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hmargin : A06.branchMargins h M K Ns branches) : excitedKet h Ns branches η m ≠ 0 ∧ errorOperator h M ζ branches (excitedKet h Ns branches η m) ≠ 0

theorem concrete_dispersion_gap : epsilon 8 (A01.canonicalRoot 16) 2 ≠ referenceWeight 8 (A01.canonicalRoot 16)

theorem concrete_excited_error_witness : A05.admissible 8 (fun _ : Fin 2 => 0) ∧ A06.branchMargins 8 2 2 (fun _ : Fin 2 => 0) standardBranches ∧ excitedKet 8 (fun _ : Fin 2 => 0) standardBranches .right 2 ≠ 0 ∧ errorOperator 8 2 (A01.canonicalRoot 16) standardBranches (excitedKet 8 (fun _ : Fin 2 => 0) standardBranches .right 2) ≠ 0
```


## Bosonize/Core/Ch17LuttingerModels.lean

SHA-256: 9355fcc40f2ec1e5d9ac5ef07065ee8d03a957d8329ef9d5d528e7f1f2e3223c

### Data and context

```text
import Bosonize.Core.A07FiniteNormalOrdering

import Bosonize.Core.Ch16FieldHamiltonian

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

import Bosonize.Core.A07InteractionsAndBogoliubov

import Bosonize.Core.A10DiscreteSchriefferWolff

namespace Bosonize.Ch17

open scoped BigOperators Classical

section ScalarParameters

noncomputable def v1Velocity (vF g4 : ℝ) : ℝ :=
  vF + g4 / (2 * Real.pi)

noncomputable def v2Velocity (g2 : ℝ) : ℝ :=
  g2 / (2 * Real.pi)

noncomputable def canonicalMu (h : ℕ) (vF : ℝ) : ℝ :=
  Real.pi * vF / ((2 * h : ℕ) : ℝ)

def sugawaraMargin {σ : Type*} (h M K : ℕ) (Ns : σ → ℤ)
    (branches : A06.Branches σ) : Prop :=
  K ≤ M ∧
    (K : ℤ) + |Ns branches.rightSpecies| < (h : ℤ) ∧
    (K : ℤ) + |Ns branches.leftSpecies| < (h : ℤ)

noncomputable def zeroModeEnergyScalar {σ : Type*} (h : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) : ℝ :=
  let L : ℝ := ((2 * h : ℕ) : ℝ)
  let nr : ℝ := (Ns branches.rightSpecies : ℝ)
  let nl : ℝ := (Ns branches.leftSpecies : ℝ)
  (2 * Real.pi * vF / L) * (nr * (nr + 1) / 2 + nl * (nl + 1) / 2) +
    (g4 / (2 * L)) * (nr ^ 2 + nl ^ 2) +
    (g2 / L) * nr * nl -
    mu * (nr + nl)

noncomputable def symmetricZeroModeScalar {σ : Type*} (h : ℕ)
    (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) : ℝ :=
  let L : ℝ := ((2 * h : ℕ) : ℝ)
  let nr : ℝ := (Ns branches.rightSpecies : ℝ)
  let nl : ℝ := (Ns branches.leftSpecies : ℝ)
  (Real.pi * v1Velocity vF g4 / L) * (nr ^ 2 + nl ^ 2) +
    (g2 / L) * nr * nl

end ScalarParameters

section LuttingerHamiltonians

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def chemicalPotentialOp (h : ℕ) (mu : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (mu : ℂ) • (A05.chargeObservable h branches.rightSpecies +
    A05.chargeObservable h branches.leftSpecies)

noncomputable def freeSugawaraKinetic (h M : ℕ) (vF : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let r := branches.rightSpecies
  let l := branches.leftSpecies
  let prefactor : ℂ := ((2 * Real.pi * vF : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)
  prefactor • (Ch16.sugawara h M branches +
    ((2 : ℂ)⁻¹) • (A05.chargeObservable h r * (A05.chargeObservable h r + 1) +
      A05.chargeObservable h l * (A05.chargeObservable h l + 1)))

noncomputable def freeFermionKinetic (h : ℕ) (vF : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let prefactor : ℂ := ((2 * Real.pi * vF : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)
  prefactor •
    (A07Interactions.computationalMomentum h branches.rightSpecies +
      A07Interactions.computationalMomentum h branches.leftSpecies)

noncomputable def zeroModeEnergyOp (h : ℕ) (vF g4 g2 mu : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  let L : ℂ := ((2 * h : ℕ) : ℂ)
  let nr := A05.chargeObservable h branches.rightSpecies
  let nl := A05.chargeObservable h branches.leftSpecies
  (((2 * Real.pi * vF : ℝ) : ℂ) / L) •
      (((2 : ℂ)⁻¹) • (nr * (nr + 1) + nl * (nl + 1))) +
    ((g4 : ℂ) / (2 * L)) • (nr * nr + nl * nl) +
    ((g2 : ℂ) / L) • (nr * nl) -
    chemicalPotentialOp h mu branches

noncomputable def luttingerOscillatorOp (h M : ℕ) (vF g4 g2 : ℝ)
    (branches : A06.Branches σ) : A05.Operators σ h :=
  (((2 * Real.pi : ℝ) : ℂ) / ((2 * h : ℕ) : ℂ)) •
    ∑ m ∈ Finset.Icc 1 M,
      A07Interactions.pairingMode h m
        (v1Velocity vF g4) (v2Velocity g2) branches

noncomputable def luttingerBosonizedHamiltonian (h M : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    A05.Operators σ h :=
  luttingerOscillatorOp h M vF g4 g2 branches +
    zeroModeEnergyOp h vF g4 g2 mu branches

noncomputable def luttingerChosenModel (h M : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    A05.Operators σ h :=
  freeSugawaraKinetic h M vF branches +
    A07Interactions.currentIntraBranch h M g4 branches +
    A07Interactions.pairingInterBranch h M g2 branches -
    chemicalPotentialOp h mu branches

noncomputable def luttingerFermionChosenModel (h M : ℕ)
    (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) :
    A05.Operators σ h :=
  freeFermionKinetic h vF branches +
    A07Interactions.currentIntraBranch h M g4 branches +
    A07Interactions.pairingInterBranch h M g2 branches -
    chemicalPotentialOp h mu branches

end LuttingerHamiltonians

end Bosonize.Ch17
```

### Proved headers

```text
lemma zero_mode_scalar_canonical_mu {σ : Type*} (h : ℕ) (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) : zeroModeEnergyScalar h vF g4 g2 (canonicalMu h vF) branches Ns = symmetricZeroModeScalar h vF g4 g2 branches Ns

theorem luttinger_chosen_eq_bosonized (h M : ℕ) (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) : luttingerChosenModel h M vF g4 g2 mu branches = luttingerBosonizedHamiltonian h M vF g4 g2 mu branches

lemma zero_mode_op_on_budget (h K : ℕ) (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : zeroModeEnergyOp h vF g4 g2 mu branches v = (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v

theorem free_fermion_eq_sugawara_on_budget (h M K : ℕ) (hh : 0 < h) (vF : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hSug : sugawaraMargin h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : freeFermionKinetic h vF branches v = freeSugawaraKinetic h M vF branches v

theorem luttinger_hamiltonian_on_budget (h M K : ℕ) (hh : 0 < h) (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hSug : sugawaraMargin h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : luttingerFermionChosenModel h M vF g4 g2 mu branches v = luttingerOscillatorOp h M vF g4 g2 branches v + (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v

theorem luttinger_hamiltonian_canonical_mu_on_budget (h M K : ℕ) (hh : 0 < h) (vF g4 g2 : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hSug : sugawaraMargin h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : luttingerFermionChosenModel h M vF g4 g2 (canonicalMu h vF) branches v = luttingerOscillatorOp h M vF g4 g2 branches v + (symmetricZeroModeScalar h vF g4 g2 branches Ns : ℂ) • v

theorem luttinger_raw_intra_on_budget (h M K : ℕ) (hh : 0 < h) (vF g4 g2 mu : ℝ) (branches : A06.Branches σ) (Ns : σ → ℤ) (hN : A05.admissible h Ns) (hSug : sugawaraMargin h M K Ns branches) (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) : (freeFermionKinetic h vF branches + A07Interactions.rawIntraBranch h M g4 branches + A07Interactions.pairingInterBranch h M g2 branches - chemicalPotentialOp h mu branches) v = luttingerOscillatorOp h M vF g4 g2 branches v + (zeroModeEnergyScalar h vF g4 g2 mu branches Ns : ℂ) • v - (((g4 : ℂ) / (2 * ((2 * h : ℕ) : ℂ))) • (A07Interactions.seaWickCorrection h M branches.rightSpecies + A07Interactions.seaWickCorrection h M branches.leftSpecies)) v

theorem concrete_luttinger_witness : let Ns : Fin 2 → ℤ := fun _ => 0 A05.admissible 8 Ns ∧ A06.branchMargins 8 2 2 Ns Ch16.standardBranches ∧ sugawaraMargin 8 2 2 Ns Ch16.standardBranches ∧ A05.groundKet 8 Ns ∈ A05.jointBudget 8 Ns 2 ∧ A05.groundKet 8 Ns ≠ 0 ∧ luttingerBosonizedHamiltonian 8 2 1 (6 * Real.pi) (6 * Real.pi) (canonicalMu 8 1) Ch16.standardBranches (A05.groundKet 8 Ns) ≠ 0
```
