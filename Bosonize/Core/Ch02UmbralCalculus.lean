module

public import Bosonize.Core.Ch01LatticeBand
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Chapter 2: Umbral calculus core

Verified algebraic foundations following `notes/md/ch02_umbral_calculus.md`.
Definitions are complete linear maps and all lemmas have complete proofs.
Polynomial identities are formal algebraic identities over a commutative ring.
-/

@[expose] public section

namespace Bosonize.Ch02

open scoped BigOperators

-- Both source domains are abelian; do not compensate for missing domain laws with tactics.
variable {S R : Type*} [AddCommGroup S] [One S] [CommRing R]

/-- Translation by one as a linear endomorphism of functions. -/
def shift : Module.End R (S → R) where
  toFun f x := f (x + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Translation by minus one, the inverse of the shift. -/
def inverseShift : Module.End R (S → R) where
  toFun f x := f (x - 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The identity operator explicitly included in definition 2.1. -/
def identity : Module.End R (S → R) := LinearMap.id

/-- Forward difference, `Δ = E - I`. -/
def forwardDiff : Module.End R (S → R) := shift - identity

/-- Backward difference, `∇ = I - E⁻¹`. -/
def backwardDiff : Module.End R (S → R) := identity - inverseShift

/-- The discrete Laplacian is the composition `Δ ∘ ∇`. -/
def laplacian : Module.End R (S → R) := forwardDiff.comp backwardDiff

lemma shift_apply (f : S → R) (x : S) : shift f x = f (x + 1) := by
  rfl

lemma inverse_shift_apply (f : S → R) (x : S) :
    inverseShift f x = f (x - 1) := by
  rfl

omit [AddCommGroup S] [One S] in
lemma identity_apply (f : S → R) (x : S) : identity f x = f x := by
  rfl

lemma forward_diff_apply (f : S → R) (x : S) :
    forwardDiff f x = f (x + 1) - f x := by
  rfl

lemma backward_diff_apply (f : S → R) (x : S) :
    backwardDiff f x = f x - f (x - 1) := by
  rfl

lemma shift_inverse :
    (shift (S := S) (R := R)).comp inverseShift = identity := by
  ext f x
  simp [shift, inverseShift, identity]

lemma inverse_shift_shift :
    (inverseShift (S := S) (R := R)).comp shift = identity := by
  ext f x
  simp [shift, inverseShift, identity]

lemma laplacian_operator :
    laplacian (S := S) (R := R) = shift + inverseShift - (2 : ℕ) • identity := by
  ext f x
  change (f (x + 1) - f ((x + 1) - 1)) - (f x - f (x - 1)) =
    f (x + 1) + f (x - 1) - (2 : ℕ) • f x
  simp only [add_sub_cancel_right, two_nsmul]
  abel

lemma laplacian_apply (f : S → R) (x : S) :
    laplacian f x = f (x + 1) + f (x - 1) - 2 * f x := by
  simp [laplacian, forwardDiff, backwardDiff, shift, inverseShift, identity]
  ring

/-- Equation (2.8), with pointwise multiplication of functions. -/
lemma discrete_leibniz_left (f g : S → R) :
    forwardDiff (f * g) = forwardDiff f * g + shift f * forwardDiff g := by
  funext x
  simp only [forward_diff_apply, shift_apply, Pi.mul_apply, Pi.add_apply]
  ring

/-- Equation (2.9), the alternative exact Leibniz rule. -/
lemma discrete_leibniz_right (f g : S → R) :
    forwardDiff (f * g) = f * forwardDiff g + forwardDiff f * shift g := by
  funext x
  simp only [forward_diff_apply, shift_apply, Pi.mul_apply, Pi.add_apply]
  ring

/-- Equation (2.10). Translation permutes the finite periodic lattice, leaving no
boundary residual. `NeZero L` explicitly excludes the infinite `ZMod 0`. -/
lemma sum_by_parts (L : ℕ) [NeZero L] (f g : Ch01.Lattice L → R) :
    ∑ x : Ch01.Lattice L, f x * forwardDiff g x =
      - ∑ x : Ch01.Lattice L, backwardDiff f x * g x := by
  let e : Ch01.Lattice L ≃ Ch01.Lattice L :=
    { toFun := fun x ↦ x + 1
      invFun := fun x ↦ x - 1
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  have h := e.sum_comp (fun x ↦ f (x - 1) * g x)
  have hs : (∑ x, f x * g (x + 1)) = ∑ x, f (x - 1) * g x := by
    simpa [e] using h
  simp only [forward_diff_apply, backward_diff_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib, neg_sub]
  rw [hs]

/-- Equation (2.11); multiplication of endomorphisms is composition. -/
lemma newton_expansion (n : ℕ) :
    (shift (S := S) (R := R)) ^ n =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) • (forwardDiff ^ k) := by
  have h : shift (S := S) (R := R) = forwardDiff + 1 := by
    change shift = (shift - identity) + identity
    exact (sub_add_cancel _ _).symm
  rw [h]
  simpa [nsmul_eq_mul, Nat.cast_comm] using
    (Commute.one_right (forwardDiff (S := S) (R := R))).add_pow n

/-- The action of the same Newton expansion on a function. -/
lemma newton_expansion_apply (n : ℕ) (f : S → R) :
    (shift ^ n) f =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) • ((forwardDiff ^ k) f) := by
  have h := congrArg (fun E : Module.End R (S → R) ↦ E f)
    (newton_expansion (S := S) (R := R) n)
  simpa using h

/-- A constant function is annihilated by forward difference. -/
lemma forward_diff_const (r : R) :
    forwardDiff (S := S) (fun _ ↦ r) = 0 := by
  funext x
  simp [forward_diff_apply]

/-- The integer-domain witness `Δ(x)=1`, over any commutative coefficient ring. -/
lemma forward_diff_int_cast :
    forwardDiff (fun x : ℤ ↦ (x : R)) = fun _ ↦ (1 : R) := by
  funext x
  simp [forward_diff_apply]

/-- Nonzero on integer-domain functions; this is not a claim about every finite lattice. -/
lemma forward_diff_nonzero [Nontrivial R] :
    forwardDiff (S := ℤ) (R := R) ≠ 0 := by
  intro h
  have he := congrArg (fun E : Module.End R (ℤ → R) ↦ E (fun x ↦ (x : R)) 0) h
  simp [forward_diff_int_cast] at he

/-- The finite product `X (X-1) ... (X-(n-1))`. -/
noncomputable def fallingFactorial (n : ℕ) : Polynomial R :=
  ∏ k ∈ Finset.range n, (Polynomial.X - Polynomial.C (k : R))

/-- The linear extension sending the coefficient of `X^n` to the nth falling factorial. -/
noncomputable def umbralMap : Module.End R (Polynomial R) :=
  Polynomial.lsum fun n ↦ LinearMap.toSpanSingleton R (Polynomial R) (fallingFactorial n)

/-- Formal substitution `p(X) ↦ p(X+1)` as a linear map. -/
noncomputable def polyShift : Module.End R (Polynomial R) :=
  (Polynomial.aeval (Polynomial.X + 1 : Polynomial R)).toLinearMap

/-- Polynomial forward difference `p(X+1)-p(X)`. -/
noncomputable def polyForwardDiff : Module.End R (Polynomial R) :=
  polyShift - LinearMap.id

lemma falling_factorial_zero : fallingFactorial (R := R) 0 = 1 := by
  simp [fallingFactorial]

lemma falling_factorial_one :
    fallingFactorial (R := R) 1 = Polynomial.X := by
  simp [fallingFactorial]

lemma falling_factorial_succ (n : ℕ) :
    fallingFactorial (R := R) (n + 1) =
      fallingFactorial n * (Polynomial.X - Polynomial.C (n : R)) := by
  exact Finset.prod_range_succ _ n

lemma falling_factorial_monic [Nontrivial R] (n : ℕ) :
    (fallingFactorial (R := R) n).Monic := by
  induction n with
  | zero => rw [falling_factorial_zero]; exact Polynomial.monic_one
  | succ n ih =>
    rw [falling_factorial_succ]
    change (fallingFactorial n * (Polynomial.X - Polynomial.C (n : R))).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_monic_mul ih, Polynomial.leadingCoeff_X_sub_C]

/-- The umbral definition explicitly acts by a finite coefficient sum. -/
lemma umbral_map_apply (p : Polynomial R) :
    umbralMap p = ∑ n ∈ p.support, p.coeff n • fallingFactorial n := by
  rfl

/-- Equation (2.12). -/
lemma umbral_map_X_pow (n : ℕ) :
    umbralMap (Polynomial.X ^ n : Polynomial R) = fallingFactorial n := by
  rw [Polynomial.X_pow_eq_monomial]
  simp [umbralMap, Polynomial.lsum, LinearMap.toSpanSingleton]

lemma poly_shift_apply (p : Polynomial R) :
    polyShift p = p.comp (Polynomial.X + 1) := by
  rfl

lemma poly_forward_diff_apply (p : Polynomial R) :
    polyForwardDiff p = p.comp (Polynomial.X + 1) - p := by
  rfl

/-- A concrete polynomial witness for the nontrivial difference action. -/
lemma poly_forward_diff_X :
    polyForwardDiff (Polynomial.X : Polynomial R) = 1 := by
  simp [poly_forward_diff_apply]

/-- Nonzero on formal polynomials over a nontrivial ring, witnessed by `X`. -/
lemma poly_forward_diff_nonzero [Nontrivial R] :
    polyForwardDiff (R := R) ≠ 0 := by
  intro h
  have he := congrArg (fun E : Module.End R (Polynomial R) ↦ E Polynomial.X) h
  simp [poly_forward_diff_X] at he

/-- Equation (2.14), with orientation `Φ(D(p)) = Δ(Φ(p))`.
Mathlib's formal derivative is already an `R`-linear map. -/
lemma umbral_commutation :
    (umbralMap (R := R)).comp Polynomial.derivative = polyForwardDiff.comp umbralMap := by
  have hfall : ∀ n : ℕ, polyForwardDiff (fallingFactorial (R := R) (n + 1)) =
      (n + 1 : R) • fallingFactorial n := by
    intro n
    induction n with
    | zero => simp [falling_factorial_one, falling_factorial_zero, poly_forward_diff_X]
    | succ n ih =>
      have hc : (fallingFactorial (R := R) (n + 1)).comp (Polynomial.X + 1) =
          fallingFactorial (n + 1) + (n + 1 : R) • fallingFactorial n := by
        apply sub_eq_iff_eq_add'.mp
        simpa only [poly_forward_diff_apply] using ih
      rw [poly_forward_diff_apply, falling_factorial_succ (n + 1),
        Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.X_comp,
        Polynomial.C_comp, hc, falling_factorial_succ n]
      simp only [Polynomial.smul_eq_C_mul, Nat.cast_add, Nat.cast_one,
        Polynomial.C_add, Polynomial.C_1]
      ring
  apply LinearMap.ext
  intro p
  change umbralMap (Polynomial.derivative p) = polyForwardDiff (umbralMap p)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
    rw [← Polynomial.smul_X_eq_monomial]
    simp only [map_smul]
    congr 1
    cases n with
    | zero =>
      have hzero : umbralMap (1 : Polynomial R) = 1 := by
        simpa only [pow_zero, falling_factorial_zero] using
          (umbral_map_X_pow (R := R) 0)
      simp [hzero, poly_forward_diff_apply]
    | succ n =>
      rw [Polynomial.derivative_X_pow, ← Polynomial.smul_eq_C_mul, map_smul,
        umbral_map_X_pow, umbral_map_X_pow, hfall]
      simp


/-- Equation (2.13), restricted to the integer domain. -/
def posMultiplier : Module.End R (ℤ → R) where
  toFun f x := (x : R) * f (x - 1)
  map_add' f g := by
    funext x
    exact mul_add (x : R) (f (x - 1)) (g (x - 1))
  map_smul' r f := by
    funext x
    exact mul_left_comm (x : R) r (f (x - 1))

lemma pos_multiplier_apply (f : ℤ → R) (x : ℤ) :
    posMultiplier f x = (x : R) * f (x - 1) := by
  rfl

/-- Equation (2.15), as an identity of linear endomorphisms on integer-domain functions. -/
lemma heisenberg_pair_operator :
    (forwardDiff (S := ℤ) (R := R)).comp posMultiplier -
      posMultiplier.comp forwardDiff = identity := by
  ext f x
  simp [forwardDiff, shift, identity, posMultiplier]
  ring

lemma heisenberg_pair (f : ℤ → R) :
    forwardDiff (posMultiplier f) - posMultiplier (forwardDiff f) = f := by
  have h := congrArg (fun E : Module.End R (ℤ → R) ↦ E f)
    (heisenberg_pair_operator (R := R))
  exact h

/-- A positive-dimensional characteristic-zero matrix space cannot realize exact CCR. -/
lemma finite_dimensional_no_go {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (hn : 0 < n) (A B : Matrix (Fin n) (Fin n) K) :
    A * B - B * A ≠ 1 := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self, Matrix.trace_one] at ht
  simp only [Fintype.card_fin] at ht
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn) : (n : K) ≠ 0) ht.symm

end Bosonize.Ch02
