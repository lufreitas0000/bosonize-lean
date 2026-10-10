# CH08 companion notebook — algebraic boson Fock layer

Status (2026-10-09): **Phase A complete; proposed interface awaiting human review.** There are 43 complete data declarations and 62 theorem stubs, each with exactly one `:= by sorry`. No interface has been locked, no theorem has been proved, and nothing has been promoted. Core retains 457 proved theorems across eleven frozen modules. The baseline for this draft's preservation checks is `aa047eb`.

## Source reconciliation and scope

Read [CH08](../../../notes/md/ch08_boson.md), [TOC](../../../notes/md/TOC.md), [A02](../../../notes/appendices/a02_car_hilbert_and_normal_ordering.md), [A03](../../../notes/appendices/a03_energy_budgets_and_filtered_maps.md), [A05](../../../notes/appendices/a05_exponentials_klein_and_vertex_scope.md), the [appendix index](../../../notes/appendices/README.md), and [revision guide P10](../../../note/proof_suggestions_revision_2026-10-09.md). Compare A04's scope: density shifts, partitions, Gram completeness and Sugawara support CH09–CH12 rather than being prerequisites for this independent oscillator target. A04 implementation is deferred to those chapters. No chapter-specific suggestion file is available in `docs/stub_suggestion/` or `docs/proof_suggestion/`; existing deletions there are preserved.

Adopt the positive weights, Haldane norm, ambient CCR, explicit compression remainders, and positive-contraction Wick convention in the current notes. Adapt the word “Hilbert” to a weighted Hermitian pairing on the ambient algebraic polynomial space and actual finite Euclidean Hilbert spaces on budgets. The ambient polynomial space is not equipped with an asserted complete normed Hilbert structure. Reject unprojected creator nilpotency, finite-dimensional scalar CCR, an unconditional scalar BCH for compressed maps, `PowerSeries.exp operator`, convergence or parameter evaluation at t=1, and normal-ordering as an algebra homomorphism on represented words. These are scope corrections already required by the source/revision contracts; the notes are preserved.

## Type choices and explicit carriers

`Mode M = Fin M`, but `weight M i = i.val+1`. Every weight is positive, including the mode with zero-based index zero. M=0 is allowed: its polynomial carrier consists of constants, its vacuum is nonzero, and mode-indexed statements have no modes to quantify. K=0 remains a one-vacuum finite slice. No hypotheses asserting M>0 or K>0 are imposed globally.

Exponent vectors use `Fin M →₀ ℕ`. The installed `MvPolynomial.basisMonomials` supplies the actual algebraic basis, and `MvPolynomial.lcoeff ℂ r` supplies bundled coefficient maps. `MvPolynomial.coeff` is not an available namespace-qualified declaration in this installation; the inherited coefficient API has polynomial-first arguments. Creation uses `LinearMap.mulLeft`; differentiation uses `(MvPolynomial.pderiv i).toLinearMap`; annihilation is weight times differentiation. Number and energy are distinct sums.

The Haldane pairing is a finite support sum with weights `∏ i, weight i ^ r i * (r i)!`, conjugate-linear in the first argument. Its positivity, definiteness, Hermitian symmetry and adjoint pairing identities are proposed obligations. `creation_pairing_adjoint` concerns this pairing; it does not use a fictional ambient Hilbert adjoint. Under this form it is weighted annihilation, rather than the unweighted derivative at mode weight greater than one, that is the creator's adjoint.

`budget M K` is the span of bounded-energy monomials. `projection` is algebraic basis truncation. A finite envelope `Fin M → Fin (K+1)` and an energy-filtered subtype construct `BudgetIndex` without using an unproved theorem as an instance. The subtype is an abbreviation so its actual finite instances remain visible. Its coverage of all bounded-energy exponent vectors must be proved using positivity of weights. `FiniteFock` is a genuine `EuclideanSpace ℂ (BudgetIndex M K)`.

`embedding` maps orthonormal coordinate kets to monomials divided by the positive square root of their Haldane norm. `coordinates` multiplies polynomial coefficients by that same square root. Their inverse, range and pairing claims are theorem stubs. `finiteOperator A = coordinates ∘ A ∘ embedding`; for creators this includes boundary truncation, while annihilators preserve the budget. Actual finite adjoints use `LinearMap.adjoint` on this carrier.

## Grading, witnesses and boundary terms

Creation raises energy by its positive mode weight. Annihilation lowers it; the natural-subtraction inclusion is accompanied by `annihilation_below_weight`, which states that a slice smaller than that weight is killed. This is a concrete reason why the truncated subtraction is safe here. A conservative K+1 power cutoff is used for both compressed creators and annihilators; no nilpotency follows merely from finite dimension.

Vacuum normalization, `finiteVacuum_ne_zero`, positive monomial norms, and `creation_power_vacuum_ne_zero` are explicit proposed witnesses. They remain unproved. In particular, the scalar-CCR obstruction quantifies an actual mode and uses a nonzero carrier, rather than a hidden nontriviality assumption. A proof can use trace or an explicit edge action after the finite carrier witness is proved.

The exact identity for P squared=P is

`[PAP,PBP] = P[A,B]P - PA(1-P)BP + PB(1-P)AP`.

The signs and product order are preserved in `compressed_commutator`. No right-suffix numerical margins or leakage cancellation are assumed at this chapter: these are ambient oscillator constructions and exact finite compressions. Later restricted current identities will need their own input margins. The inclusion `creation_budget` does not incorrectly claim that the creator is an endomorphism of the original budget.

## Exponentials and normal symbols

`taylor` is only a finite Taylor sum. `expNil` requires the explicit certificate A^(d+1)=0 and retains it in the interface. Its cutoff independence and inverse are stubs. Adjoint compatibility is stated for the Taylor sum on actual finite Hilbert carriers and can specialize to a certified nilpotent exponential.

Formal exponentials are sequences `ℕ → Operators M` with a finite Cauchy product. This makes the central formal parameter and coefficientwise interpretation explicit without adopting an unverified noncommutative series API. The BCH correction has only even degrees: the coefficient of t^(2k) is gamma^k/k! times identity. The proposed identity swaps exp(t alpha A) and exp(t beta C) with the positive correction gamma=weight*alpha*beta on equal modes. No convergence, evaluation or compressed scalar-CCR premise is asserted.

Normal symbols are an independent finitely supported vector space on pairs (creator power, derivative power). Their evaluation is linear and ordered, not multiplicative. Single-mode Boolean words use the frozen A03 application-order convention; true means creator and false means derivative. This single-mode word statement does not claim a full multivariate normal-symbol dictionary. The explicit Wick powers and vacuum coefficients cover CH08's displayed single-mode formula. They use unweighted D, with contraction one; the Haldane annihilator A=weight D is kept distinct. The positive-contraction sequence has P2=X^2+1, and the Hermite convention has He2=X^2-1.

## Twist dependency and later selection of operators

This file constructs the abstract bosonic target, whose positive integer oscillator labels and algebraic operations do not take a fermion twist parameter. This fact alone proves no physical twist independence. CH09/A04 must construct their actual density operators from the selected CH06Ext twisted fermion family and prove any phase cancellation, grading or edge formula on those operators. CH10–CH12 must compare that family with the CH08 target on admissible budgets. Fermion transport, holonomy and twist-dependent zero modes continue to come from frozen CH06Ext; local CAR and locality infrastructure remain in CH06. CH13/CH14/A05 will retain species twist labels and source/target sectors explicitly. No arbitrary-twist isometry, density dictionary or analytic bosonization identity is smuggled into CH08's definitions.

## Proposed Phase B proof order and helper obligations

1. Establish positive weights/norms, actual monomial actions and number/energy eigenvalues. Local helpers can give energy increment/decrement, factorial norm recurrence and the square-root normalization identity.
2. Extend basis pairing identities by finite support sums; prove sesquilinearity, positivity/definiteness, creator/annihilator adjoint pairing, and ambient CCR by Leibniz.
3. Prove supportwise budget characterization and envelope coverage, then grading, below-weight vanishing, projection action/idempotence/range and bounded power vanishing.
4. Prove normalized coordinate transport, the genuine nonzero finite vacuum, finite adjoints/spectrum and nilpotency. Derive exact projection remainders and the finite scalar-CCR obstruction.
5. Prove finite exponential identities by factorial/binomial sums under the nilpotency certificate. Prove formal Cauchy associativity and coefficient BCH from ambient ordered word expansions.
6. Prove normal-word existence and Wick contraction induction, then vacuum recurrence, Appell derivative and coefficient generating identity. Check the first two nontrivial signs directly.

All of these are obligations, not completed evidence. New top-level helpers or a correction to reviewed interfaces will require the repository's review procedure in Phase B; local proof-body decompositions remain available. The primary formalizer used the repository [skill](../../../.agents/skills/formalizer/SKILL.md) and its proof-design/MCP references. No additional agents were dispatched for this draft.

## Phase A validation

- Installed compiler elaborates the draft with exactly 62 expected `sorry` warnings and no other diagnostics. Both `lake build Bosonize BosonizeStubs` targets pass.
- Native Lean MCP diagnostics return success=true, partial=false, no failed dependencies, and exactly 62 sorry-category warnings. `lean_goal` at the `formal_bch` placeholder (line 356, column 89) returns the actual proposed equality. A goal status after a sorry is not proof evidence. Local search was attempted for basis APIs and failed because the MCP child could not resolve `rg`; shell source retrieval and compiler API checks supplied the fallback. No MCP configuration was changed.
- Fresh `import BosonizeStubs` axiom inspection of all 43 named data declarations uses only the permitted standard axioms, or none, and never `sorryAx`. All 62 theorem stubs expose `sorryAx`, as required for an unproved Phase A interface.
- All 69 guard regression tests pass. Non-strict verification against `aa047eb` preserves 457 approved statements and 342 commands; all eleven complete Core hashes pass. Strict verification rejects exactly the new unlocked CH08 source (62 statements/61 commands). Full CI is therefore not claimed as passing at this review boundary.
- Active and historical lock manifests, Core sources/aggregator, toolchain and dependency manifests are unchanged. The initial unrelated note edits and three suggestion deletions are preserved byte-for-byte.

Review the weighted pairing, normalized finite carrier, projection residuals and the two exponential meanings before locking or starting Phase B. A04 will be drafted with its actual density/current dependencies after CH08's completion.

## Exact Phase A source snapshot

Source SHA-256: `78d1dea1fc2e10f5146a066695a573b3d4f3d579200322eda3f16d466c20a76a`.

```lean
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
```
