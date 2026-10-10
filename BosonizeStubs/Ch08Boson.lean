module

public import Bosonize.Core.A03EnergyBudgets
public import Bosonize.Core.Ch02UmbralCalculus
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# CH08 — Algebraic boson Fock space
Phase A: complete data and proposed theorem signatures; every theorem is unproved.
The polynomial carrier has a weighted Hermitian pairing, not an asserted Hilbert
completion. Actual adjoints below belong to finite Euclidean carriers. Composition
in `Module.End` applies the right factor first. No twist-dependent fermion/current
identification is assumed by this abstract oscillator target.
-/

@[expose] public section

namespace Bosonize.Ch08
open scoped BigOperators Classical

/-- Zero-based finite labels; physical oscillator weights are one-based. -/
abbrev Mode (M : ℕ) := Fin M

/-- Finite exponent vectors label the monomial basis, including the zero vector. -/
abbrev Exponents (M : ℕ) := Mode M →₀ ℕ

/-- The ambient algebraic carrier consists of polynomials of finite support. -/
abbrev Polynomial (M : ℕ) := MvPolynomial (Mode M) ℂ

/-- Ambient linear endomorphisms compose from right to left. -/
abbrev Operators (M : ℕ) := Module.End ℂ (Polynomial M)

/-- Every mode has strictly positive energy; mode zero has weight one. -/
def weight (M : ℕ) (i : Mode M) : ℕ :=
  i.val + 1

/-- The coefficient-one basis vector for an exponent vector. -/
noncomputable def monomial (M : ℕ) (r : Exponents M) : Polynomial M :=
  MvPolynomial.monomial r 1

/-- The empty oscillator configuration is the constant polynomial one. -/
noncomputable def vacuum (M : ℕ) : Polynomial M :=
  1

/-- Unweighted occupation count distinguishes particle number from energy. -/
def particleCount (M : ℕ) (r : Exponents M) : ℕ :=
  ∑ i : Mode M, r i

/-- Weighted occupation energy supplies the nonnegative budget grading. -/
def energy (M : ℕ) (r : Exponents M) : ℕ :=
  ∑ i : Mode M, weight M i * r i

/-- Squared Haldane norm: product of mode powers times occupation factorials. -/
def monomialNorm (M : ℕ) (r : Exponents M) : ℕ :=
  ∏ i : Mode M, weight M i ^ r i * (r i).factorial

/-- Positive real square root, embedded into complex scalars, normalizes each monomial. -/
noncomputable def normalization (M : ℕ) (r : Exponents M) : ℂ :=
  (Real.sqrt (monomialNorm M r : ℝ) : ℂ)

/-- Multiplication by a variable raises that mode; it is not an ambient nilpotent map. -/
noncomputable def creation (M : ℕ) (i : Mode M) : Operators M :=
  LinearMap.mulLeft ℂ (MvPolynomial.X i)

/-- The bundled partial derivation is viewed as a complex linear map. -/
noncomputable def derivative (M : ℕ) (i : Mode M) : Operators M :=
  (MvPolynomial.pderiv i).toLinearMap

/-- Haldane annihilation is weight times derivative, the pairing adjoint of creation. -/
noncomputable def annihilation (M : ℕ) (i : Mode M) : Operators M :=
  (weight M i : ℂ) • derivative M i

/-- Sum of X times derivative counts particles without mode weights. -/
noncomputable def numberOperator (M : ℕ) : Operators M :=
  ∑ i : Mode M, creation M i * derivative M i

/-- Sum of creator times weighted annihilator measures oscillator energy. -/
noncomputable def hamiltonian (M : ℕ) : Operators M :=
  ∑ i : Mode M, creation M i * annihilation M i

/-- Finite coefficient sum, conjugate-linear in the first slot; no completion is installed. -/
noncomputable def pairing (M : ℕ) (p q : Polynomial M) : ℂ :=
  ∑ r ∈ p.support, star (MvPolynomial.lcoeff ℂ r p) * (monomialNorm M r : ℂ) * MvPolynomial.lcoeff ℂ r q

/-- The ordered difference A B minus B A fixes the CCR sign. -/
noncomputable def commutator (M : ℕ) (A B : Operators M) : Operators M :=
  A * B - B * A

/-- Span of monomials with energy at most K; creation generally leaves this space. -/
noncomputable def budget (M K : ℕ) : Submodule ℂ (Polynomial M) :=
  Submodule.span ℂ (monomial M '' {r | energy M r ≤ K})

/-- Basis truncation retains exactly the bounded-energy monomials. -/
noncomputable def projection (M K : ℕ) : Operators M :=
  (MvPolynomial.basisMonomials (Mode M) ℂ).constr ℂ (fun r => if energy M r ≤ K then monomial M r else 0)

/-- Projection on both sides retains the finite budget and exposes leakage terms. -/
noncomputable def compressed (M K : ℕ) (A : Operators M) : Operators M :=
  projection M K * A * projection M K

/-- A finite envelope: each occupation is at most K because weights are positive. -/
abbrev ExponentBox (M K : ℕ) := Mode M → Fin (K + 1)

/-- Convert a bounded coordinate function to a finite exponent vector. -/
noncomputable def boxExponent (M K : ℕ) (a : ExponentBox M K) : Exponents M :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i).val)

/-- Retain only envelope entries whose actual weighted energy fits the cutoff. -/
abbrev BudgetIndex (M K : ℕ) :=
  {a : ExponentBox M K // energy M (boxExponent M K a) ≤ K}

/-- Read the exponent vector of a finite budget basis label. -/
noncomputable def indexExponent (M K : ℕ) (s : BudgetIndex M K) : Exponents M :=
  boxExponent M K s.val

/-- A genuine finite Hilbert carrier with the standard complex inner product. -/
abbrev FiniteFock (M K : ℕ) := EuclideanSpace ℂ (BudgetIndex M K)

/-- The orthonormal coordinate ket for a bounded configuration. -/
noncomputable def finiteKet (M K : ℕ) (s : BudgetIndex M K) : FiniteFock M K :=
  EuclideanSpace.basisFun (BudgetIndex M K) ℂ s

/-- Normalized monomials realize the finite Hilbert carrier inside the polynomial carrier. -/
noncomputable def embedding (M K : ℕ) : FiniteFock M K →ₗ[ℂ] Polynomial M :=
  (EuclideanSpace.basisFun (BudgetIndex M K) ℂ).toBasis.constr ℂ (fun s => (normalization M (indexExponent M K s))⁻¹ • monomial M (indexExponent M K s))

/-- Weighted coefficient extraction discards high-energy terms and inverts the embedding on its image. -/
noncomputable def coordinates (M K : ℕ) : Polynomial M →ₗ[ℂ] FiniteFock M K :=
  (WithLp.linearEquiv 2 ℂ (BudgetIndex M K → ℂ)).symm.toLinearMap.comp (LinearMap.pi (fun s => normalization M (indexExponent M K s) • MvPolynomial.lcoeff ℂ (indexExponent M K s)))

/-- Transport an ambient operator between embedding and coordinate projection. -/
noncomputable def finiteOperator (M K : ℕ) (A : Operators M) : Module.End ℂ (FiniteFock M K) :=
  (coordinates M K).comp (A.comp (embedding M K))

/-- The coordinate image of the polynomial vacuum supplies a nonzero-carrier witness. -/
noncomputable def finiteVacuum (M K : ℕ) : FiniteFock M K :=
  coordinates M K (vacuum M)

/-- Finite Taylor polynomial on a finite Hilbert carrier; nilpotency is not inferred. -/
noncomputable def taylor (M K : ℕ) (A : Module.End ℂ (FiniteFock M K)) (d : ℕ) : Module.End ℂ (FiniteFock M K) :=
  ∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) • A ^ j

/-- Exact finite exponential requires a certificate of power vanishing; its value is the Taylor sum. -/
noncomputable def expNil (M K : ℕ) (A : Module.End ℂ (FiniteFock M K)) (d : ℕ) (_hnil : A ^ (d + 1) = 0) : Module.End ℂ (FiniteFock M K) :=
  taylor M K A d

/-- Coefficient sequences model a central formal parameter without convergence assumptions. -/
abbrev FormalOperators (M : ℕ) := ℕ → Operators M

/-- Degree-n coefficient of the formal exponential of an ambient operator. -/
noncomputable def expCoefficient (M : ℕ) (A : Operators M) : FormalOperators M :=
  fun n => ((n.factorial : ℂ)⁻¹) • A ^ n

/-- Cauchy product preserves the noncommutative order of operator coefficients. -/
noncomputable def formalProduct (M : ℕ) (f g : FormalOperators M) : FormalOperators M :=
  fun n => ∑ j ∈ Finset.range (n + 1), f j * g (n - j)

/-- Coefficients of exp(t squared times gamma I), with odd coefficients zero. -/
noncomputable def gaussianCoefficient (M : ℕ) (γ : ℂ) : FormalOperators M :=
  fun n => if n % 2 = 0 then (γ ^ (n / 2) / ((n / 2).factorial : ℂ)) • (1 : Operators M) else 0

/-- Independent normal symbols record creator and derivative powers before evaluation. -/
abbrev NormalSymbols  := (ℕ × ℕ) →₀ ℂ

/-- Ordered linear evaluation sends (a,b) to C to power a times D to power b; no algebra homomorphism is claimed. -/
noncomputable def normalEvaluation (M : ℕ) (i : Mode M) : NormalSymbols →ₗ[ℂ] Operators M :=
  Finsupp.linearCombination ℂ (fun ab : ℕ × ℕ => creation M i ^ ab.1 * derivative M i ^ ab.2)

/-- A list of letters is in application order; true means creator, false means derivative. -/
noncomputable def wordEvaluation (M : ℕ) (i : Mode M) (letters : List Bool) : Operators M :=
  A03.applicationWord (letters.map (fun b => if b then creation M i else derivative M i))

/-- Normal binomial sum places every creator to the left of every derivative. -/
noncomputable def normalPower (M : ℕ) (i : Mode M) (n : ℕ) : Operators M :=
  ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℂ) • (creation M i ^ j * derivative M i ^ (n - j))

/-- Positive-contraction polynomials arise from (D+C) to power n on the vacuum. -/
noncomputable def wickPolynomial (M : ℕ) (i : Mode M) (n : ℕ) : Polynomial M :=
  ((derivative M i + creation M i) ^ n) (vacuum M)

/-- The probabilists Hermite convention uses (C-D), giving X squared minus one at n=2. -/
noncomputable def hermitePolynomial (M : ℕ) (i : Mode M) (n : ℕ) : Polynomial M :=
  ((creation M i - derivative M i) ^ n) (vacuum M)

/-- Strictly positive weights make every bounded-energy slice finite. -/
theorem weight_pos (M : ℕ) (i : Mode M) : 0 < weight M i := by sorry

/-- Every Haldane monomial has strictly positive squared norm. -/
theorem monomialNorm_pos (M : ℕ) (r : Exponents M) : 0 < monomialNorm M r := by sorry

/-- Normalization inverses used in the embedding are well-defined. -/
theorem normalization_ne_zero (M : ℕ) (r : Exponents M) : normalization M r ≠ 0 := by sorry

/-- Creation increments exactly one exponent with coefficient one. -/
theorem creation_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : creation M i (monomial M r) = monomial M (r + Finsupp.single i 1) := by sorry

/-- Truncated exponent subtraction is harmless when the occupation coefficient is zero. -/
theorem derivative_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : derivative M i (monomial M r) = (r i : ℂ) • monomial M (r - Finsupp.single i 1) := by sorry

/-- The annihilator includes the mode weight as well as the occupation coefficient. -/
theorem annihilation_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : annihilation M i (monomial M r) = ((weight M i * r i : ℕ) : ℂ) • monomial M (r - Finsupp.single i 1) := by sorry

/-- All annihilators kill the constant polynomial. -/
theorem annihilation_vacuum (M : ℕ) (i : Mode M) : annihilation M i (vacuum M) = 0 := by sorry

/-- Ambient creation is never nilpotent, witnessed on the vacuum at every power. -/
theorem creation_power_vacuum_ne_zero (M : ℕ) (i : Mode M) (n : ℕ) : (creation M i ^ n) (vacuum M) ≠ 0 := by sorry

/-- Number eigenvalues are unweighted occupations. -/
theorem number_monomial (M : ℕ) (r : Exponents M) : numberOperator M (monomial M r) = (particleCount M r : ℂ) • monomial M r := by sorry

/-- Hamiltonian eigenvalues are the positive weighted energy. -/
theorem hamiltonian_monomial (M : ℕ) (r : Exponents M) : hamiltonian M (monomial M r) = (energy M r : ℂ) • monomial M r := by sorry

/-- Distinct monomials are orthogonal and diagonal weights are Haldane norms. -/
theorem pairing_monomials (M : ℕ) (r s : Exponents M) : pairing M (monomial M r) (monomial M s) = if r = s then (monomialNorm M r : ℂ) else 0 := by sorry

/-- The first slot is additive. -/
theorem pairing_add_left (M : ℕ) (p q r : Polynomial M) : pairing M (p + q) r = pairing M p r + pairing M q r := by sorry

/-- The first slot conjugates scalar coefficients. -/
theorem pairing_smul_left (M : ℕ) (a : ℂ) (p q : Polynomial M) : pairing M (a • p) q = star a * pairing M p q := by sorry

/-- The second slot is additive. -/
theorem pairing_add_right (M : ℕ) (p q r : Polynomial M) : pairing M p (q + r) = pairing M p q + pairing M p r := by sorry

/-- The second slot is complex linear. -/
theorem pairing_smul_right (M : ℕ) (a : ℂ) (p q : Polynomial M) : pairing M p (a • q) = a * pairing M p q := by sorry

/-- Hermitian symmetry exchanges the two polynomial arguments. -/
theorem pairing_conjugate (M : ℕ) (p q : Polynomial M) : star (pairing M p q) = pairing M q p := by sorry

/-- Squared norm has nonnegative real part. -/
theorem pairing_self_nonnegative (M : ℕ) (p : Polynomial M) : 0 ≤ (pairing M p p).re := by sorry

/-- Definiteness is an obligation, not a consequence of a span being nonempty. -/
theorem pairing_self_eq_zero (M : ℕ) (p : Polynomial M) : pairing M p p = 0 ↔ p = 0 := by sorry

/-- The chosen vacuum has norm one. -/
theorem pairing_vacuum (M : ℕ) : pairing M (vacuum M) (vacuum M) = 1 := by sorry

/-- The Haldane pairing adjoint of creation is weighted annihilation. -/
theorem creation_pairing_adjoint (M : ℕ) (i : Mode M) (p q : Polynomial M) : pairing M (creation M i p) q = pairing M p (annihilation M i q) := by sorry

/-- The exact scalar CCR is an ambient identity. -/
theorem ccr (M : ℕ) (i j : Mode M) : commutator M (annihilation M i) (creation M j) = if i = j then (weight M i : ℂ) • (1 : Operators M) else 0 := by sorry

/-- Partial derivatives in distinct or identical modes commute. -/
theorem annihilators_commute (M : ℕ) (i j : Mode M) : commutator M (annihilation M i) (annihilation M j) = 0 := by sorry

/-- Polynomial multiplication gives commuting creators. -/
theorem creators_commute (M : ℕ) (i j : Mode M) : commutator M (creation M i) (creation M j) = 0 := by sorry

/-- Budget membership is equivalent to a supportwise energy bound. -/
theorem mem_budget_iff (M K : ℕ) (p : Polynomial M) : p ∈ budget M K ↔ ∀ r ∈ p.support, energy M r ≤ K := by sorry

/-- Increasing the energy cutoff includes the earlier budget. -/
theorem budget_mono (M K K' : ℕ) (h : K ≤ K') : budget M K ≤ budget M K' := by sorry

/-- The energy-zero vacuum is admitted even at cutoff zero. -/
theorem vacuum_mem_budget (M K : ℕ) : vacuum M ∈ budget M K := by sorry

/-- Creation raises the available energy cutoff by its mode weight. -/
theorem creation_budget (M K : ℕ) (i : Mode M) (p : Polynomial M) (h : p ∈ budget M K) : creation M i p ∈ budget M (K + weight M i) := by sorry

/-- Lowering below zero produces zero, so natural subtraction is safe for this inclusion. -/
theorem annihilation_budget (M K : ℕ) (i : Mode M) (p : Polynomial M) (h : p ∈ budget M K) : annihilation M i p ∈ budget M (K - weight M i) := by sorry

/-- If the budget is below one occupation of this mode, annihilation is identically zero there. -/
theorem annihilation_below_weight (M K : ℕ) (i : Mode M) (hK : K < weight M i) (p : Polynomial M) (hp : p ∈ budget M K) : annihilation M i p = 0 := by sorry

/-- A conservative K+1 derivative count kills the energy-K slice. -/
theorem annihilation_power_budget (M K : ℕ) (i : Mode M) (p : Polynomial M) (h : p ∈ budget M K) : (annihilation M i ^ (K + 1)) p = 0 := by sorry

/-- Projection action is the exact energy indicator on the ambient basis. -/
theorem projection_monomial (M K : ℕ) (r : Exponents M) : projection M K (monomial M r) = if energy M r ≤ K then monomial M r else 0 := by sorry

/-- Truncating twice agrees with truncating once. -/
theorem projection_idempotent (M K : ℕ) : projection M K * projection M K = projection M K := by sorry

/-- The truncation image equals the span-defined budget. -/
theorem projection_range (M K : ℕ) : LinearMap.range (projection M K) = budget M K := by sorry

/-- The basis truncation is symmetric for the Haldane pairing. -/
theorem projection_pairing (M K : ℕ) (p q : Polynomial M) : pairing M (projection M K p) q = pairing M p (projection M K q) := by sorry

/-- Normalized coordinate extraction inverts the finite embedding. -/
theorem coordinates_embedding (M K : ℕ) : (coordinates M K).comp (embedding M K) = LinearMap.id := by sorry

/-- Embedding after extraction is precisely the ambient projection. -/
theorem embedding_coordinates (M K : ℕ) : (embedding M K).comp (coordinates M K) = projection M K := by sorry

/-- The actual finite Hilbert carrier realizes the whole budget. -/
theorem embedding_range (M K : ℕ) : LinearMap.range (embedding M K) = budget M K := by sorry

/-- The standard finite inner product transports to the Haldane polynomial pairing. -/
theorem embedding_pairing (M K : ℕ) (v w : FiniteFock M K) : pairing M (embedding M K v) (embedding M K w) = inner ℂ v w := by sorry

/-- Positive weights and the finite envelope imply finite dimension. -/
theorem budget_finiteDimensional (M K : ℕ) : FiniteDimensional ℂ (budget M K) := by sorry

/-- A genuine nonzero vector rules out a vacuous scalar-CCR obstruction. -/
theorem finiteVacuum_ne_zero (M K : ℕ) : finiteVacuum M K ≠ 0 := by sorry

/-- Actual finite Hilbert adjoints identify compressed creator and annihilator. -/
theorem finite_creation_adjoint (M K : ℕ) (i : Mode M) : LinearMap.adjoint (finiteOperator M K (creation M i)) = finiteOperator M K (annihilation M i) := by sorry

/-- The finite particle number observable has its actual Hilbert adjoint. -/
theorem finite_number_selfAdjoint (M K : ℕ) : LinearMap.adjoint (finiteOperator M K (numberOperator M)) = finiteOperator M K (numberOperator M) := by sorry

/-- The finite energy observable is self-adjoint. -/
theorem finite_hamiltonian_selfAdjoint (M K : ℕ) : LinearMap.adjoint (finiteOperator M K (hamiltonian M)) = finiteOperator M K (hamiltonian M) := by sorry

/-- Energy eigenvalues survive exact finite-coordinate transport. -/
theorem finite_hamiltonian_ket (M K : ℕ) (s : BudgetIndex M K) : finiteOperator M K (hamiltonian M) (finiteKet M K s) = (energy M (indexExponent M K s) : ℂ) • finiteKet M K s := by sorry

/-- Compressed creation raises energy until it leaves the finite budget. -/
theorem finite_creation_nilpotent (M K : ℕ) (i : Mode M) : finiteOperator M K (creation M i) ^ (K + 1) = 0 := by sorry

/-- Compressed annihilation lowers occupation until it reaches zero. -/
theorem finite_annihilation_nilpotent (M K : ℕ) (i : Mode M) : finiteOperator M K (annihilation M i) ^ (K + 1) = 0 := by sorry

/-- Both leakage remainders are retained with their exact noncommutative order. -/
theorem compressed_commutator (M K : ℕ) (A B : Operators M) :
    commutator M (compressed M K A) (compressed M K B) =
      projection M K * commutator M A B * projection M K
      - projection M K * A * (1 - projection M K) * B * projection M K
      + projection M K * B * (1 - projection M K) * A * projection M K := by sorry

/-- A nonzero finite carrier cannot realize a nonzero scalar identity as a commutator. -/
theorem finite_ccr_obstruction (M K : ℕ) (i : Mode M) :
    finiteOperator M K (annihilation M i) * finiteOperator M K (creation M i)
      - finiteOperator M K (creation M i) * finiteOperator M K (annihilation M i)
      ≠ (weight M i : ℂ) • (1 : Module.End ℂ (FiniteFock M K)) := by sorry

/-- A certified nilpotent exponential is independent of any larger Taylor cutoff. -/
theorem expNil_cutoff (M K d e : ℕ) (A : Module.End ℂ (FiniteFock M K)) (hd : A ^ (d + 1) = 0) (hde : d ≤ e) : taylor M K A e = expNil M K A d hd := by sorry

/-- Negating a nilpotent operator gives the inverse finite exponential. -/
theorem expNil_inverse (M K d : ℕ) (A : Module.End ℂ (FiniteFock M K)) (hd : A ^ (d + 1) = 0) : expNil M K A d hd * taylor M K (-A) d = 1 := by sorry

/-- Taking an actual finite adjoint commutes with real factorial Taylor coefficients. -/
theorem taylor_adjoint (M K d : ℕ) (A : Module.End ℂ (FiniteFock M K)) : LinearMap.adjoint (taylor M K A d) = taylor M K (LinearMap.adjoint A) d := by sorry

/-- Coefficientwise associativity fixes the formal-series interpretation. -/
theorem formalProduct_assoc (M : ℕ) (f g h : FormalOperators M) : formalProduct M (formalProduct M f g) h = formalProduct M f (formalProduct M g h) := by sorry

/-- The central t-squared correction belongs only to the ambient scalar CCR. -/
theorem formal_bch (M : ℕ) (i j : Mode M) (α β : ℂ) (n : ℕ) :
    formalProduct M (expCoefficient M (α • annihilation M i)) (expCoefficient M (β • creation M j)) n =
      formalProduct M
        (formalProduct M (expCoefficient M (β • creation M j)) (expCoefficient M (α • annihilation M i)))
        (gaussianCoefficient M (if i = j then (weight M i : ℂ) * α * β else 0)) n := by sorry

/-- Single-mode words admit an independent normal-symbol expansion including contractions. -/
theorem word_normal_form (M : ℕ) (i : Mode M) (letters : List Bool) : ∃ s : NormalSymbols, normalEvaluation M i s = wordEvaluation M i letters := by sorry

/-- Normal-ordered powers reduce to pure creator powers on the vacuum. -/
theorem normalPower_vacuum (M : ℕ) (i : Mode M) (n : ℕ) : normalPower M i n (vacuum M) = MvPolynomial.X i ^ n := by sorry

/-- The exact Wick expansion uses unweighted D and C, whose contraction is one. -/
theorem wick_operator (M : ℕ) (i : Mode M) (n : ℕ) :
    (derivative M i + creation M i) ^ n =
      ∑ k ∈ Finset.range (n / 2 + 1),
        ((n.factorial : ℂ) / ((k.factorial : ℂ) * ((n - 2 * k).factorial : ℂ) * (2 : ℂ) ^ k))
          • normalPower M i (n - 2 * k) := by sorry

/-- The zeroth positive-contraction polynomial is the vacuum. -/
theorem wick_zero (M : ℕ) (i : Mode M) : wickPolynomial M i 0 = vacuum M := by sorry

/-- The positive contraction gives X squared plus one, not the Hermite sign. -/
theorem wick_two (M : ℕ) (i : Mode M) : wickPolynomial M i 2 = MvPolynomial.X i ^ 2 + 1 := by sorry

/-- The opposite derivative sign gives the probabilists Hermite convention. -/
theorem hermite_two (M : ℕ) (i : Mode M) : hermitePolynomial M i 2 = MvPolynomial.X i ^ 2 - 1 := by sorry

/-- The positive-contraction sequence is an Appell sequence. -/
theorem wick_derivative (M : ℕ) (i : Mode M) (n : ℕ) : derivative M i (wickPolynomial M i n) = (n : ℂ) • wickPolynomial M i (n - 1) := by sorry

/-- Vacuum polynomials satisfy the source recurrence with the positive contraction sign. -/
theorem wick_recurrence (M : ℕ) (i : Mode M) (n : ℕ) : wickPolynomial M i (n + 1) = creation M i (wickPolynomial M i n) + (n : ℂ) • wickPolynomial M i (n - 1) := by sorry

/-- The generating function exp(X t plus t squared over two) is stated coefficientwise. -/
theorem wick_coefficients (M : ℕ) (i : Mode M) (n : ℕ) :
    ((n.factorial : ℂ)⁻¹) • wickPolynomial M i n =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (((n - 2 * k).factorial : ℂ) * (k.factorial : ℂ) * (2 : ℂ) ^ k)⁻¹
          • (MvPolynomial.X i ^ (n - 2 * k)) := by sorry

end Bosonize.Ch08
