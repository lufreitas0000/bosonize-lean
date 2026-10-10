# CH08 companion notebook — algebraic boson Fock layer

Status (2026-10-10): **Phase B active: 61 of 62 theorem targets fully proved.** All 43 data declarations and the 61 completed theorem targets have fresh transitive axiom audits using only standard axioms or none. `formal_bch` is the sole remaining placeholder. Core still contains 457 proved theorems in eleven frozen modules; CH08 has not been promoted. The independently reviewed Phase B import baseline is `b229bbf`.

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

This ordered plan records the original Phase A obligations. The current Phase B evidence below supersedes its unproved status. New top-level helpers or a correction to reviewed interfaces will require the repository's review procedure in Phase B; local proof-body decompositions remain available. The primary formalizer used the repository [skill](../../../.agents/skills/formalizer/SKILL.md) and its proof-design/MCP references. No additional agents were dispatched for this draft.

## Phase A validation

- Installed compiler elaborates the draft with exactly 62 expected `sorry` warnings and no other diagnostics. Both `lake build Bosonize BosonizeStubs` targets pass.
- Native Lean MCP diagnostics return success=true, partial=false, no failed dependencies, and exactly 62 sorry-category warnings. `lean_goal` at the `formal_bch` placeholder (line 356, column 89) returns the actual proposed equality. A goal status after a sorry is not proof evidence. Local search was attempted for basis APIs and failed because the MCP child could not resolve `rg`; shell source retrieval and compiler API checks supplied the fallback. No MCP configuration was changed.
- Fresh `import BosonizeStubs` axiom inspection of all 43 named data declarations uses only the permitted standard axioms, or none, and never `sorryAx`. All 62 theorem stubs expose `sorryAx`, as required for an unproved Phase A interface.
- All 69 guard regression tests pass. Non-strict verification against `aa047eb` preserves 457 approved statements and 342 commands; all eleven complete Core hashes pass. Strict verification rejects exactly the new unlocked CH08 source (62 statements/61 commands). Full CI is therefore not claimed as passing at this review boundary.
- Active and historical lock manifests, Core sources/aggregator, toolchain and dependency manifests are unchanged. The initial unrelated note edits and three suggestion deletions are preserved byte-for-byte.

The independent review below covers the weighted pairing, normalized finite carrier, projection residuals and the two exponential meanings. Under the new automatic pipeline, chapter-development execution can establish the reviewed lock and proceed through B/C without another human phase confirmation. This workflow-update/review pass changes no theorem proofs or locks. A04 will be drafted with its actual density/current dependencies after CH08's completion.

## Independent Phase A review — 2026-10-09

Reviewer: separate agent `/root/ch08_interface_review`, dispatched by the primary formalizer at the user's request for automatic A–B–C with independent review. Verdict: **PASS** for source SHA-256 `78d1dea1fc2e10f5146a066695a573b3d4f3d579200322eda3f16d466c20a76a`. The reviewer was read-only and checked all 43 data declarations/62 signatures, source reconciliation, exact notebook mirror, weighted pairing/finite adjoints, positive-mode envelope/nonvacuity, lowering at small budgets, compression signs, BCH/Wick conventions and future twist dependencies. It found no required correction or genuine human ambiguity.

Independent exact rational checks passed: weighted BCH (weight 2, alpha 2, beta 3) through coefficient degree 6 on polynomial inputs of degree 0–4; Wick operator expansion through degree 8 on inputs of degree 0–4; projection remainders at weight 2/cutoff 5; compressed power vanishing and commutator trace zero in that example. These calculations are counterexample screening, not universal Lean proofs and not proof-body changes.

Nonblocking observations: the normal-symbol word theorem deliberately covers a single mode, while the source's opening sentence about arbitrary products is broader; this limitation is documented above. Energy increment, factorial norm recurrence, bounded-index coverage and ordered-power helpers would ease Phase B, but are optional interface extensions requiring the new independent review procedure. The current snapshot can be locked without them.

The [automatic pipeline](../../../.agents/skills/formalizer/references/pipeline.md) supersedes the former routine human phase gates. This record supplies the independent review evidence; no lock or proof transition is claimed in this workflow-update task.

## Phase B interface baseline — 2026-10-10

The user resumed chapter development under the automatic pipeline. The unchanged source matches the independent passing review hash. The local CH08 candidate lock passes strict verification (519 total statements/403 commands); all eleven Core hashes pass. Only the CH08 entry is added to the committed manifest. Prior Unicode serialization changes in the working manifest remain outside this scoped commit. Proof work starts only after this baseline is committed and checked.

## Independently reviewed Phase B import amendment — 2026-10-10

Only two public Mathlib imports are added to the active staging interface:
`Mathlib.RingTheory.Nilpotent.Exp` and `Mathlib.LinearAlgebra.Trace`.
No definitions, instances, theorem signatures, physical conventions or Core files change.
The nilpotent exponential API supplies finite rational factorial sums under an explicit
power-zero certificate. The trace API proves the finite scalar-CCR obstruction using
trace cyclicity, positive weight, and the nonzero finite vacuum; it does not infer
nilpotency from finite dimension.

Independent reviewer `/root/ch08_budget_proofs` approved both imports after reviewing
the proposed proofs and library contracts. Fresh axiom inspections of
`IsNilpotent.exp_eq_sum`, `IsNilpotent.exp_mul_exp_neg_self`,
`LinearMap.trace_mul_comm` and `LinearMap.trace_one` contain only the permitted
standard axioms. Compiler evidence was checked in external scratch files.
This amendment changes only CH08's ordered command lock. The initial Phase A
snapshot below remains historical evidence of the reviewed original draft.

## Phase B proof checkpoint — 2026-10-10

All 61 implemented proofs compile together. The sole remaining theorem stub is
`formal_bch`; it alone exposes `sorryAx` in the fresh 105-declaration audit.
The other 61 theorem targets and all 43 data declarations use only `propext`,
`Classical.choice`, and `Quot.sound`, or no axioms. In particular, the completed
`wick_coefficients` now depends on the proved `wick_operator`, not a placeholder.

Proof batches cover basis actions and ambient CCR, weighted pairing and
creator adjoint, energy budgets/projections, finite normalized transport and
actual adjoints, nilpotency/trace obstruction, certified exponentials,
formal product associativity, single-mode word normalization and Wick/Appell
identities. Wick's operator proof uses a locally proved normal-power recurrence,
a factorial coefficient recurrence with zero extension, and finite-sum induction.
No new top-level declarations or modified conclusions were needed.

Independent review by `/root/ch08_budget_proofs` checked the integrated frozen
preamble, proof scope, and fresh transitive axiom dependencies. Separate agents
`/root/ch08_finite_proofs` and `/root/ch08_exponential_proofs` contributed finite
transport, exponential, word and contraction proofs. Root integrated and compiled
the exact bodies; compiler success was confirmed after process completion.
The reviewer found no integration or mathematical scope defect.

Strict verification against `b229bbf` passes 519 statements and 407 commands;
all eleven existing Core hashes pass. `make ci` passes 69 guard regression tests
and both builds, with exactly one permitted staging placeholder warning.
This is a Phase B checkpoint, not Phase C completion. Native MCP diagnostics
worked on the integrated source; native declaration search still cannot resolve
`rg`, so shell retrieval supplied the fallback. Unrelated note edits and
suggestion deletions remain byte-for-byte unchanged.

## Current Phase B source snapshot

Source SHA-256: `6742cacb85c813329d8a21c88d25e368b61321250195099369547710e825dd1d`.
The module's introductory Phase A label is historical; the current proof status
is stated above. The original independently reviewed draft hash is recorded in
the Phase A review section.

```lean
module

public import Bosonize.Core.A03EnergyBudgets
public import Bosonize.Core.Ch02UmbralCalculus
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.LinearAlgebra.Trace

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
theorem weight_pos (M : ℕ) (i : Mode M) : 0 < weight M i := by
  exact Nat.succ_pos i.val

/-- Every Haldane monomial has strictly positive squared norm. -/
theorem monomialNorm_pos (M : ℕ) (r : Exponents M) : 0 < monomialNorm M r := by
  exact Finset.prod_pos (fun i _ => Nat.mul_pos (Nat.pow_pos (weight_pos M i)) (Nat.factorial_pos (r i)))

/-- Normalization inverses used in the embedding are well-defined. -/
theorem normalization_ne_zero (M : ℕ) (r : Exponents M) : normalization M r ≠ 0 := by
  have h : (0 : ℝ) < (monomialNorm M r : ℝ) := by exact_mod_cast monomialNorm_pos M r
  simpa [normalization] using (ne_of_gt (Real.sqrt_pos.2 h))

/-- Creation increments exactly one exponent with coefficient one. -/
theorem creation_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : creation M i (monomial M r) = monomial M (r + Finsupp.single i 1) := by
  simp [creation, monomial, LinearMap.mulLeft_apply, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, add_comm]

/-- Truncated exponent subtraction is harmless when the occupation coefficient is zero. -/
theorem derivative_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : derivative M i (monomial M r) = (r i : ℂ) • monomial M (r - Finsupp.single i 1) := by
  simp [derivative, monomial, MvPolynomial.pderiv_monomial, MvPolynomial.smul_monomial]

/-- The annihilator includes the mode weight as well as the occupation coefficient. -/
theorem annihilation_monomial (M : ℕ) (i : Mode M) (r : Exponents M) : annihilation M i (monomial M r) = ((weight M i * r i : ℕ) : ℂ) • monomial M (r - Finsupp.single i 1) := by
  simp [annihilation, derivative_monomial, smul_smul, Nat.cast_mul]

/-- All annihilators kill the constant polynomial. -/
theorem annihilation_vacuum (M : ℕ) (i : Mode M) : annihilation M i (vacuum M) = 0 := by
  simp [annihilation, derivative, vacuum]

/-- Ambient creation is never nilpotent, witnessed on the vacuum at every power. -/
theorem creation_power_vacuum_ne_zero (M : ℕ) (i : Mode M) (n : ℕ) : (creation M i ^ n) (vacuum M) ≠ 0 := by
  have h : (creation M i ^ n) (vacuum M) = MvPolynomial.X i ^ n := by
    induction n with
    | zero => simp [vacuum]
    | succ n ih => rw [pow_succ', Module.End.mul_apply, ih]; simp [creation, pow_succ']
  rw [h, MvPolynomial.X_pow_eq_monomial]
  simp [MvPolynomial.monomial_eq_zero]

/-- Number eigenvalues are unweighted occupations. -/
theorem number_monomial (M : ℕ) (r : Exponents M) : numberOperator M (monomial M r) = (particleCount M r : ℂ) • monomial M r := by
  have hact (i : Mode M) : (creation M i * derivative M i) (monomial M r) = (r i : ℂ) • monomial M r := by
    change MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.monomial r (1 : ℂ)) = _
    simpa only [Nat.cast_smul_eq_nsmul, monomial] using (MvPolynomial.X_mul_pderiv_monomial (i := i) (m := r) (r := (1 : ℂ)))
  simp only [numberOperator, LinearMap.sum_apply, hact, ← Finset.sum_smul, particleCount, Nat.cast_sum]

/-- Hamiltonian eigenvalues are the positive weighted energy. -/
theorem hamiltonian_monomial (M : ℕ) (r : Exponents M) : hamiltonian M (monomial M r) = (energy M r : ℂ) • monomial M r := by
  have hact (i : Mode M) : (creation M i * annihilation M i) (monomial M r) = (weight M i * r i : ℂ) • monomial M r := by
    change MvPolynomial.X i * ((weight M i : ℂ) • MvPolynomial.pderiv i (MvPolynomial.monomial r (1 : ℂ))) = _
    rw [mul_smul_comm, MvPolynomial.X_mul_pderiv_monomial, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    rfl
  simp only [hamiltonian, LinearMap.sum_apply, hact, ← Finset.sum_smul, energy, Nat.cast_sum, Nat.cast_mul]

/-- Distinct monomials are orthogonal and diagonal weights are Haldane norms. -/
theorem pairing_monomials (M : ℕ) (r s : Exponents M) : pairing M (monomial M r) (monomial M s) = if r = s then (monomialNorm M r : ℂ) else 0 := by
  classical
  simp [pairing, monomial, MvPolynomial.lcoeff_apply, MvPolynomial.coeff_monomial]
  split_ifs <;> simp_all

/-- The first slot is additive. -/
theorem pairing_add_left (M : ℕ) (p q r : Polynomial M) : pairing M (p + q) r = pairing M p r + pairing M q r := by
  classical
  change ((MvPolynomial.basisMonomials (Mode M) ℂ).repr (p + q)).sum (fun v a => star a * (monomialNorm M v : ℂ) * MvPolynomial.lcoeff ℂ v r) = _
  rw [map_add, Finsupp.sum_add_index']
  · rfl
  · intro v; simp
  · intro v a b; simp [add_mul]

/-- The first slot conjugates scalar coefficients. -/
theorem pairing_smul_left (M : ℕ) (a : ℂ) (p q : Polynomial M) : pairing M (a • p) q = star a * pairing M p q := by
  classical
  by_cases ha : a = 0
  · subst a; simp [pairing]
  · have hs : (a • p).support = p.support := MvPolynomial.support_smul_eq ha p
    simp only [pairing, hs, map_smul, smul_eq_mul, star_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring

/-- The second slot is additive. -/
theorem pairing_add_right (M : ℕ) (p q r : Polynomial M) : pairing M p (q + r) = pairing M p q + pairing M p r := by
  classical
  simp only [pairing, map_add, mul_add, Finset.sum_add_distrib]

/-- The second slot is complex linear. -/
theorem pairing_smul_right (M : ℕ) (a : ℂ) (p q : Polynomial M) : pairing M p (a • q) = a * pairing M p q := by
  classical
  simp only [pairing, map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Hermitian symmetry exchanges the two polynomial arguments. -/
theorem pairing_conjugate (M : ℕ) (p q : Polynomial M) : star (pairing M p q) = pairing M q p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial r a =>
    have he : MvPolynomial.monomial r a = a • monomial M r := by simp [monomial, MvPolynomial.smul_monomial]
    rw [he, pairing_smul_left, pairing_smul_right, star_mul, star_star]
    induction q using MvPolynomial.induction_on' with
    | monomial s b =>
      have hs : MvPolynomial.monomial s b = b • monomial M s := by simp [monomial, MvPolynomial.smul_monomial]
      rw [hs, pairing_smul_right, pairing_smul_left, pairing_monomials, pairing_monomials]
      by_cases hrs : r = s
      · subst s; simp [star_mul, mul_comm]
      · simp [hrs, Ne.symm hrs]
    | add p q hp hq => simp only [pairing_add_left, pairing_add_right, star_add, mul_add, add_mul] at *; exact congrArg₂ (· + ·) hp hq
  | add p q hp hq => simp [pairing_add_left, pairing_add_right, star_add, hp, hq]

/-- Squared norm has nonnegative real part. -/
theorem pairing_self_nonnegative (M : ℕ) (p : Polynomial M) : 0 ≤ (pairing M p p).re := by
  classical
  have term (z : ℂ) (n : ℕ) : (star z * (n : ℂ) * z).re = Complex.normSq z * (n : ℝ) := by
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.natCast_re, Complex.natCast_im, Complex.normSq_apply]
    ring
  unfold pairing
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro r hr
  rw [term]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

/-- Definiteness is an obligation, not a consequence of a span being nonempty. -/
theorem pairing_self_eq_zero (M : ℕ) (p : Polynomial M) : pairing M p p = 0 ↔ p = 0 := by
  classical
  have term (z : ℂ) (n : ℕ) : (star z * (n : ℂ) * z).re = Complex.normSq z * (n : ℝ) := by
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.natCast_re, Complex.natCast_im, Complex.normSq_apply]
    ring
  constructor
  · intro h
    have hz : ∑ r ∈ p.support, Complex.normSq (MvPolynomial.lcoeff ℂ r p) * (monomialNorm M r : ℝ) = 0 := by
      have hh := congrArg Complex.re h
      simpa only [pairing, Complex.re_sum, term, Complex.zero_re] using hh
    have each := (Finset.sum_eq_zero_iff_of_nonneg (fun r (_ : r ∈ p.support) => mul_nonneg (Complex.normSq_nonneg (MvPolynomial.lcoeff ℂ r p)) (Nat.cast_nonneg (monomialNorm M r)))).mp hz
    apply MvPolynomial.ext
    intro r
    change MvPolynomial.lcoeff ℂ r p = 0
    by_cases hr : r ∈ p.support
    · have hn : (0 : ℝ) < (monomialNorm M r : ℝ) := Nat.cast_pos.mpr (monomialNorm_pos M r)
      exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp (each r hr)).resolve_right (ne_of_gt hn))
    · exact MvPolynomial.notMem_support_iff.mp hr
  · rintro rfl
    simp [pairing]

/-- The chosen vacuum has norm one. -/
theorem pairing_vacuum (M : ℕ) : pairing M (vacuum M) (vacuum M) = 1 := by
  have hz : vacuum M = monomial M 0 := by simp [vacuum, monomial]
  rw [hz, pairing_monomials]
  simp [monomialNorm]

/-- The Haldane pairing adjoint of creation is weighted annihilation. -/
theorem creation_pairing_adjoint (M : ℕ) (i : Mode M) (p q : Polynomial M) : pairing M (creation M i p) q = pairing M p (annihilation M i q) := by
  classical
  have norm_step (r : Exponents M) : monomialNorm M (r + Finsupp.single i 1) = weight M i * (r i + 1) * monomialNorm M r := by
    have ht : (∏ j ∈ Finset.univ.erase i, weight M j ^ ((r + Finsupp.single i 1 : Exponents M) j) * (((r + Finsupp.single i 1 : Exponents M) j)).factorial) = ∏ j ∈ Finset.univ.erase i, weight M j ^ r j * (r j).factorial := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [Finsupp.add_apply, (Finset.mem_erase.mp hj).1]
    unfold monomialNorm
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← Finset.mul_prod_erase Finset.univ (fun j => weight M j ^ r j * (r j).factorial) (Finset.mem_univ i), ht]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, pow_succ, Nat.factorial_succ]
    ring
  have on_basis (r s : Exponents M) : pairing M (creation M i (monomial M r)) (monomial M s) = pairing M (monomial M r) (annihilation M i (monomial M s)) := by
    rw [creation_monomial, annihilation_monomial, pairing_smul_right, pairing_monomials, pairing_monomials]
    by_cases hs : s i = 0
    · have hn : r + Finsupp.single i 1 ≠ s := by
        intro he
        have := congrArg (fun v : Exponents M => v i) he
        simp [hs] at this
      simp [hs, hn]
    · have er : s - Finsupp.single i 1 = r ↔ s = r + Finsupp.single i 1 := by
        constructor
        · intro he
          rw [← he]
          ext j
          by_cases hj : j = i
          · subst j; simp; omega
          · simp [hj]
        · intro he; rw [he]; simp
      by_cases he : s = r + Finsupp.single i 1
      · subst s
        simp only [Finsupp.add_apply, Finsupp.single_eq_same, add_tsub_cancel_right, ite_true]
        rw [norm_step]
        push_cast
        ring
      · have hn : r ≠ s - Finsupp.single i 1 := by intro hh; exact he (er.mp hh.symm)
        simp [Ne.symm he, hn]
  induction p using MvPolynomial.induction_on' with
  | monomial r a =>
    have he : MvPolynomial.monomial r a = a • monomial M r := by simp [monomial, MvPolynomial.smul_monomial]
    rw [he, map_smul, pairing_smul_left, pairing_smul_left]
    congr 1
    induction q using MvPolynomial.induction_on' with
    | monomial s b =>
      have hs : MvPolynomial.monomial s b = b • monomial M s := by simp [monomial, MvPolynomial.smul_monomial]
      rw [hs, map_smul, pairing_smul_right, pairing_smul_right, on_basis]
    | add p q hp hq => simp [pairing_add_right, hp, hq]
  | add p q hp hq => simp [pairing_add_left, hp, hq]

/-- The exact scalar CCR is an ambient identity. -/
theorem ccr (M : ℕ) (i j : Mode M) : commutator M (annihilation M i) (creation M j) = if i = j then (weight M i : ℂ) • (1 : Operators M) else 0 := by
  classical
  ext p
  by_cases h : i = j
  · subst j
    simp [commutator, annihilation, creation, derivative, Module.End.mul_apply, smul_add, smul_eq_mul]
  · simp [commutator, annihilation, creation, derivative, Module.End.mul_apply, MvPolynomial.pderiv_X_of_ne (Ne.symm h), h, smul_eq_mul]

/-- Partial derivatives in distinct or identical modes commute. -/
theorem annihilators_commute (M : ℕ) (i j : Mode M) : commutator M (annihilation M i) (annihilation M j) = 0 := by
  have hc (p : Polynomial M) : MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p k hp =>
      by_cases hi : k = i <;> by_cases hj : k = j <;>
        simp_all [MvPolynomial.pderiv_X] <;> ring
  apply LinearMap.ext
  intro p
  change (weight M i : ℂ) • MvPolynomial.pderiv i ((weight M j : ℂ) • MvPolynomial.pderiv j p) - (weight M j : ℂ) • MvPolynomial.pderiv j ((weight M i : ℂ) • MvPolynomial.pderiv i p) = 0
  simp only [Derivation.map_smul, smul_smul]
  rw [hc]
  simp [mul_comm]


/-- Polynomial multiplication gives commuting creators. -/
theorem creators_commute (M : ℕ) (i j : Mode M) : commutator M (creation M i) (creation M j) = 0 := by
  ext p
  simp [commutator, creation, Module.End.mul_apply, mul_left_comm]

/-- Budget membership is equivalent to a supportwise energy bound. -/
theorem mem_budget_iff (M K : ℕ) (p : Polynomial M) : p ∈ budget M K ↔ ∀ r ∈ p.support, energy M r ≤ K := by
  classical
  change p ∈ Submodule.span ℂ ((MvPolynomial.basisMonomials (Mode M) ℂ) '' {r | energy M r ≤ K}) ↔ _
  rw [Module.Basis.mem_span_image]
  rfl

/-- Increasing the energy cutoff includes the earlier budget. -/
theorem budget_mono (M K K' : ℕ) (h : K ≤ K') : budget M K ≤ budget M K' := by
  apply Submodule.span_mono
  rintro _ ⟨r, hr, rfl⟩
  exact ⟨r, le_trans hr h, rfl⟩

/-- The energy-zero vacuum is admitted even at cutoff zero. -/
theorem vacuum_mem_budget (M K : ℕ) : vacuum M ∈ budget M K := by
  apply Submodule.subset_span
  refine ⟨0, ?_, ?_⟩
  · simp [energy]
  · simp [monomial, vacuum]

/-- Creation raises the available energy cutoff by its mode weight. -/
theorem creation_budget (M K : ℕ) (i : Mode M) (p : Polynomial M) (h : p ∈ budget M K) : creation M i p ∈ budget M (K + weight M i) := by
  classical
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    rw [creation_monomial]
    apply Submodule.subset_span
    refine ⟨r + Finsupp.single i 1, ?_, rfl⟩
    have he : energy M (r + Finsupp.single i 1) = energy M r + weight M i := by
      simp [energy, Finsupp.add_apply, Nat.mul_add, Finset.sum_add_distrib, Finsupp.single_apply]
    simpa [he] using Nat.add_le_add_right hr (weight M i)
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (budget M (K + weight M i)).add_mem ihx ihy
  | smul a x hx ih => simpa using (budget M (K + weight M i)).smul_mem a ih

/-- Lowering below zero produces zero, so natural subtraction is safe for this inclusion. -/
theorem annihilation_budget (M K : ℕ) (i : Mode M) (p : Polynomial M) (h : p ∈ budget M K) : annihilation M i p ∈ budget M (K - weight M i) := by
  classical
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    rw [annihilation_monomial]
    by_cases hi : r i = 0
    · simp [hi]
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨r - Finsupp.single i 1, ?_, rfl⟩
      have er : r = (r - Finsupp.single i 1) + Finsupp.single i 1 := by
        ext j
        by_cases hj : j = i
        · subst j; simp; omega
        · simp [hj]
      have he : energy M r = energy M (r - Finsupp.single i 1) + weight M i := by
        conv_lhs => rw [er]
        simp [energy, Finsupp.add_apply, Nat.mul_add, Finset.sum_add_distrib, Finsupp.single_apply]
      simp only [Set.mem_ofPred_eq] at hr ⊢
      omega
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (budget M (K - weight M i)).add_mem ihx ihy
  | smul a x hx ih => simpa using (budget M (K - weight M i)).smul_mem a ih

/-- If the budget is below one occupation of this mode, annihilation is identically zero there. -/
theorem annihilation_below_weight (M K : ℕ) (i : Mode M) (hK : K < weight M i) (p : Polynomial M) (hp : p ∈ budget M K) : annihilation M i p = 0 := by
  classical
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    have hi : r i = 0 := by
      have bound : weight M i * r i ≤ energy M r := Finset.single_le_sum (fun j _ => Nat.zero_le (weight M j * r j)) (Finset.mem_univ i)
      have pos := weight_pos M i
      simp only [Set.mem_ofPred_eq] at hr
      by_contra hh
      have : weight M i ≤ weight M i * r i := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hh)
      omega
    simp [annihilation_monomial, hi]
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul a x hx ih => simp [ih]

/-- A conservative K+1 derivative count kills the energy-K slice. -/
theorem annihilation_power_budget (M K : ℕ) (i : Mode M) (p : Polynomial M) (h : p ∈ budget M K) : (annihilation M i ^ (K + 1)) p = 0 := by
  induction K generalizing p with
  | zero =>
    simpa using annihilation_below_weight M 0 i (weight_pos M i) p h
  | succ K ih =>
    have ha := annihilation_budget M (K + 1) i p h
    have hm : K + 1 - weight M i ≤ K := by have := weight_pos M i; omega
    have hb := budget_mono M (K + 1 - weight M i) K hm ha
    simpa [pow_succ, Module.End.mul_apply] using ih (annihilation M i p) hb

/-- Projection action is the exact energy indicator on the ambient basis. -/
theorem projection_monomial (M K : ℕ) (r : Exponents M) : projection M K (monomial M r) = if energy M r ≤ K then monomial M r else 0 := by
  exact (MvPolynomial.basisMonomials (Mode M) ℂ).constr_basis ℂ _ r

/-- Truncating twice agrees with truncating once. -/
theorem projection_idempotent (M K : ℕ) : projection M K * projection M K = projection M K := by
  apply (MvPolynomial.basisMonomials (Mode M) ℂ).ext
  intro r
  change projection M K (projection M K (monomial M r)) = projection M K (monomial M r)
  rw [projection_monomial]
  split_ifs with h
  · simp [projection_monomial, h]
  · simp

/-- The truncation image equals the span-defined budget. -/
theorem projection_range (M K : ℕ) : LinearMap.range (projection M K) = budget M K := by
  classical
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    induction p using MvPolynomial.induction_on' with
    | monomial r a =>
      have he : MvPolynomial.monomial r a = a • monomial M r := by simp [monomial, MvPolynomial.smul_monomial]
      rw [he, map_smul, projection_monomial]
      split_ifs with hr
      · exact (budget M K).smul_mem a (Submodule.subset_span ⟨r, hr, rfl⟩)
      · simp
    | add p q hp hq => simpa using (budget M K).add_mem hp hq
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, hr, rfl⟩
    change energy M r ≤ K at hr
    exact ⟨monomial M r, by simp [projection_monomial, hr]⟩

/-- The basis truncation is symmetric for the Haldane pairing. -/
theorem projection_pairing (M K : ℕ) (p q : Polynomial M) : pairing M (projection M K p) q = pairing M p (projection M K q) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial r a =>
    have he : MvPolynomial.monomial r a = a • monomial M r := by simp [monomial, MvPolynomial.smul_monomial]
    rw [he, map_smul, pairing_smul_left, pairing_smul_left]
    congr 1
    induction q using MvPolynomial.induction_on' with
    | monomial s b =>
      have hs : MvPolynomial.monomial s b = b • monomial M s := by simp [monomial, MvPolynomial.smul_monomial]
      rw [hs, map_smul, pairing_smul_right, pairing_smul_right]
      congr 1
      rw [projection_monomial, projection_monomial]
      by_cases hrs : r = s
      · subst s; split_ifs <;> simp [pairing, monomial]
      · by_cases hr : energy M r ≤ K <;> by_cases hs : energy M s ≤ K <;>
          simp [hr, hs, hrs, pairing, monomial]
    | add p q hp hq => simp [pairing_add_right, hp, hq]
  | add p q hp hq => simp [pairing_add_left, hp, hq]

/-- Normalized coordinate extraction inverts the finite embedding. -/
theorem coordinates_embedding (M K : ℕ) : (coordinates M K).comp (embedding M K) = LinearMap.id := by
  classical
  have hinj : Function.Injective (indexExponent M K) := by
    intro s t h
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun r : Exponents M => r i) h
  apply (EuclideanSpace.basisFun (BudgetIndex M K) ℂ).toBasis.ext
  intro s
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  change coordinates M K ((embedding M K) ((EuclideanSpace.basisFun (BudgetIndex M K) ℂ).toBasis s)) = _
  rw [embedding, Module.Basis.constr_basis]
  apply (WithLp.linearEquiv 2 ℂ (BudgetIndex M K → ℂ)).injective
  funext t
  change normalization M (indexExponent M K t) *
    MvPolynomial.lcoeff ℂ (indexExponent M K t)
      ((normalization M (indexExponent M K s))⁻¹ • monomial M (indexExponent M K s)) =
    (EuclideanSpace.basisFun (BudgetIndex M K) ℂ s) t
  simp only [map_smul, smul_eq_mul]
  by_cases h : s = t
  · subst t
    simp [monomial, normalization_ne_zero, EuclideanSpace.basisFun_apply]
  · have he : indexExponent M K s ≠ indexExponent M K t := fun he => h (hinj he)
    simp [monomial, he, h, EuclideanSpace.basisFun_apply]


/-- Embedding after extraction is precisely the ambient projection. -/
theorem embedding_coordinates (M K : ℕ) : (embedding M K).comp (coordinates M K) = projection M K := by
  classical
  apply (MvPolynomial.basisMonomials (Mode M) ℂ).ext
  intro r
  change embedding M K (coordinates M K (monomial M r)) = projection M K (monomial M r)
  rw [projection_monomial]
  by_cases hr : energy M r ≤ K
  · have hbound (i : Mode M) : r i < K + 1 := by
      have hw : 1 ≤ weight M i := weight_pos M i
      have hi : weight M i * r i ≤ energy M r :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (weight M j * r j)) (Finset.mem_univ i)
      have hx : r i ≤ weight M i * r i := by simpa using Nat.mul_le_mul_right (r i) hw
      omega
    let s : BudgetIndex M K := ⟨fun i => ⟨r i, hbound i⟩, by simpa [boxExponent] using hr⟩
    have hs : indexExponent M K s = r := by ext i; rfl
    have hinj : Function.Injective (indexExponent M K) := by
      intro a b h
      apply Subtype.ext
      funext i
      apply Fin.ext
      exact congrArg (fun r : Exponents M => r i) h
    have hc : coordinates M K (monomial M r) = normalization M r • finiteKet M K s := by
      apply (WithLp.linearEquiv 2 ℂ (BudgetIndex M K → ℂ)).injective
      funext t
      change normalization M (indexExponent M K t) * MvPolynomial.lcoeff ℂ (indexExponent M K t) (monomial M r) =
        normalization M r * (finiteKet M K s) t
      by_cases h : s = t
      · subst t; simp [finiteKet, monomial, hs, EuclideanSpace.basisFun_apply]
      · have he : r ≠ indexExponent M K t := by rw [← hs]; exact fun he => h (hinj he)
        simp [finiteKet, monomial, he, h, EuclideanSpace.basisFun_apply]
    rw [hc, map_smul]
    change normalization M r • ((EuclideanSpace.basisFun (BudgetIndex M K) ℂ).toBasis.constr ℂ
      (fun s => (normalization M (indexExponent M K s))⁻¹ • monomial M (indexExponent M K s)))
        ((EuclideanSpace.basisFun (BudgetIndex M K) ℂ).toBasis s) = _
    rw [Module.Basis.constr_basis, hs]
    simp [hr, smul_smul, normalization_ne_zero]
  · have hc : coordinates M K (monomial M r) = 0 := by
      apply (WithLp.linearEquiv 2 ℂ (BudgetIndex M K → ℂ)).injective
      funext t
      have he : r ≠ indexExponent M K t := by
        intro h
        exact hr (h ▸ t.property)
      change normalization M (indexExponent M K t) * MvPolynomial.lcoeff ℂ (indexExponent M K t) (monomial M r) = 0
      simp [monomial, he]
    simp [hc, hr]


/-- The actual finite Hilbert carrier realizes the whole budget. -/
theorem embedding_range (M K : ℕ) : LinearMap.range (embedding M K) = budget M K := by
  rw [← projection_range M K, ← embedding_coordinates M K]
  apply le_antisymm
  · rintro p ⟨v, rfl⟩
    refine ⟨embedding M K v, ?_⟩
    have h := LinearMap.congr_fun (coordinates_embedding M K) v
    simpa using congrArg (embedding M K) h
  · exact LinearMap.range_comp_le_range _ _


/-- The standard finite inner product transports to the Haldane polynomial pairing. -/
theorem embedding_pairing (M K : ℕ) (v w : FiniteFock M K) : pairing M (embedding M K v) (embedding M K w) = inner ℂ v w := by
  classical
  let b := EuclideanSpace.basisFun (BudgetIndex M K) ℂ
  have he (s : BudgetIndex M K) : embedding M K (b s) =
      (normalization M (indexExponent M K s))⁻¹ • monomial M (indexExponent M K s) := by
    exact b.toBasis.constr_basis ℂ _ s
  have hinj : Function.Injective (indexExponent M K) := by
    intro s t h
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun r : Exponents M => r i) h
  have hb (s t : BudgetIndex M K) : pairing M (embedding M K (b s)) (embedding M K (b t)) = inner ℂ (b s) (b t) := by
    rw [he, he, pairing_smul_left, pairing_smul_right, pairing_monomials]
    by_cases h : s = t
    · subst t
      have hsq : normalization M (indexExponent M K s) * normalization M (indexExponent M K s) = (monomialNorm M (indexExponent M K s) : ℂ) := by
        simp only [normalization, ← Complex.ofReal_mul]
        congr 1
        nlinarith [Real.sq_sqrt (show 0 ≤ (monomialNorm M (indexExponent M K s) : ℝ) by positivity)]
      have hz := normalization_ne_zero M (indexExponent M K s)
      simp only [normalization, star_inv₀, Complex.star_def, Complex.conj_ofReal]
      rw [← normalization, ← hsq]
      have hii : inner ℂ (b s) (b s) = 1 := by rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 s]; norm_num
      rw [hii]
      simp only [ite_true]
      field_simp
    · have hr : indexExponent M K s ≠ indexExponent M K t := fun hr => h (hinj hr)
      have hij : inner ℂ (b s) (b t) = 0 := b.orthonormal.2 h
      simp [hr, hij]
  have hsum_left {ι : Type} (S : Finset ι) (f : ι → Polynomial M) (q : Polynomial M) :
      pairing M (∑ i ∈ S, f i) q = ∑ i ∈ S, pairing M (f i) q := by
    induction S using Finset.induction_on with
    | empty => simp [pairing]
    | @insert a S ha ih => simp only [Finset.sum_insert ha, pairing_add_left, ih]
  have hsum_right {ι : Type} (S : Finset ι) (f : ι → Polynomial M) (p : Polynomial M) :
      pairing M p (∑ i ∈ S, f i) = ∑ i ∈ S, pairing M p (f i) := by
    induction S using Finset.induction_on with
    | empty => simp [pairing]
    | @insert a S ha ih => simp only [Finset.sum_insert ha, pairing_add_right, ih]
  nth_rw 1 [← b.sum_repr v, ← b.sum_repr w]
  simp only [map_sum, map_smul]
  rw [hsum_left]
  simp_rw [pairing_smul_left, hsum_right, pairing_smul_right, hb]
  nth_rw 2 [← b.sum_repr v, ← b.sum_repr w]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, RCLike.star_def,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring


/-- Positive weights and the finite envelope imply finite dimension. -/
theorem budget_finiteDimensional (M K : ℕ) : FiniteDimensional ℂ (budget M K) := by
  rw [← embedding_range M K]
  exact FiniteDimensional.of_surjective (embedding M K).rangeRestrict (by rintro ⟨p, v, hv⟩; exact ⟨v, Subtype.ext hv⟩)


/-- A genuine nonzero vector rules out a vacuous scalar-CCR obstruction. -/
theorem finiteVacuum_ne_zero (M K : ℕ) : finiteVacuum M K ≠ 0 := by
  intro h
  have hp : projection M K (vacuum M) = vacuum M := by
    have hv : vacuum M = monomial M 0 := by simp [vacuum, monomial]
    rw [hv, projection_monomial]
    simp [energy]
  have he := LinearMap.congr_fun (embedding_coordinates M K) (vacuum M)
  rw [LinearMap.comp_apply, ← finiteVacuum, h, map_zero, hp] at he
  simp [vacuum] at he


/-- Actual finite Hilbert adjoints identify compressed creator and annihilator. -/
theorem finite_creation_adjoint (M K : ℕ) (i : Mode M) : LinearMap.adjoint (finiteOperator M K (creation M i)) = finiteOperator M K (annihilation M i) := by
  have hp (v : FiniteFock M K) : projection M K (embedding M K v) = embedding M K v := by
    have he := LinearMap.congr_fun (embedding_coordinates M K) (embedding M K v)
    have hc := LinearMap.congr_fun (coordinates_embedding M K) v
    change coordinates M K (embedding M K v) = v at hc
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, hc] using he.symm
  have hleft (A : Operators M) (v w : FiniteFock M K) :
      inner ℂ (finiteOperator M K A v) w = pairing M (A (embedding M K v)) (embedding M K w) := by
    rw [← embedding_pairing]
    change pairing M ((embedding M K).comp (coordinates M K) (A (embedding M K v))) (embedding M K w) = _
    rw [embedding_coordinates, projection_pairing, hp]
  have hright (A : Operators M) (v w : FiniteFock M K) :
      inner ℂ v (finiteOperator M K A w) = pairing M (embedding M K v) (A (embedding M K w)) := by
    rw [← embedding_pairing]
    change pairing M (embedding M K v) ((embedding M K).comp (coordinates M K) (A (embedding M K w))) = _
    rw [embedding_coordinates, ← projection_pairing, hp]
  apply LinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro w
  rw [LinearMap.adjoint_inner_right, hleft, hright]
  exact creation_pairing_adjoint M i _ _


/-- The finite particle number observable has its actual Hilbert adjoint. -/
theorem finite_number_selfAdjoint (M K : ℕ) : LinearMap.adjoint (finiteOperator M K (numberOperator M)) = finiteOperator M K (numberOperator M) := by
  classical
  have he (s : BudgetIndex M K) : embedding M K (finiteKet M K s) =
      (normalization M (indexExponent M K s))⁻¹ • monomial M (indexExponent M K s) := by
    exact (EuclideanSpace.basisFun (BudgetIndex M K) ℂ).toBasis.constr_basis ℂ _ s
  have hd (s : BudgetIndex M K) : finiteOperator M K (numberOperator M) (finiteKet M K s) =
      (particleCount M (indexExponent M K s) : ℂ) • finiteKet M K s := by
    have hc : coordinates M K ((normalization M (indexExponent M K s))⁻¹ • monomial M (indexExponent M K s)) = finiteKet M K s := by
      rw [← he]
      exact LinearMap.congr_fun (coordinates_embedding M K) _
    simp only [finiteOperator, LinearMap.comp_apply, he, map_smul, number_monomial]
    rw [smul_smul, mul_comm, ← smul_smul, ← map_smul, hc]
  apply Eq.symm
  apply (LinearMap.eq_adjoint_iff_basis
    (EuclideanSpace.basisFun (BudgetIndex M K) ℂ).toBasis
    (EuclideanSpace.basisFun (BudgetIndex M K) ℂ).toBasis _ _).mpr
  intro s t
  change inner ℂ (finiteOperator M K (numberOperator M) (finiteKet M K s)) (finiteKet M K t) =
    inner ℂ (finiteKet M K s) (finiteOperator M K (numberOperator M) (finiteKet M K t))
  rw [hd, hd, inner_smul_left, inner_smul_right]
  by_cases h : s = t
  · subst t; simp
  · have hi : inner ℂ (finiteKet M K s) (finiteKet M K t) = 0 :=
      (EuclideanSpace.basisFun (BudgetIndex M K) ℂ).orthonormal.2 h
    simp [hi]


/-- The finite energy observable is self-adjoint. -/
theorem finite_hamiltonian_selfAdjoint (M K : ℕ) : LinearMap.adjoint (finiteOperator M K (hamiltonian M)) = finiteOperator M K (hamiltonian M) := by
  classical
  have he (s : BudgetIndex M K) : embedding M K (finiteKet M K s) =
      (normalization M (indexExponent M K s))⁻¹ • monomial M (indexExponent M K s) := by
    exact (EuclideanSpace.basisFun (BudgetIndex M K) ℂ).toBasis.constr_basis ℂ _ s
  have hd (s : BudgetIndex M K) : finiteOperator M K (hamiltonian M) (finiteKet M K s) =
      (energy M (indexExponent M K s) : ℂ) • finiteKet M K s := by
    have hc : coordinates M K ((normalization M (indexExponent M K s))⁻¹ • monomial M (indexExponent M K s)) = finiteKet M K s := by
      rw [← he]
      exact LinearMap.congr_fun (coordinates_embedding M K) _
    simp only [finiteOperator, LinearMap.comp_apply, he, map_smul, hamiltonian_monomial]
    rw [smul_smul, mul_comm, ← smul_smul, ← map_smul, hc]
  apply Eq.symm
  apply (LinearMap.eq_adjoint_iff_basis
    (EuclideanSpace.basisFun (BudgetIndex M K) ℂ).toBasis
    (EuclideanSpace.basisFun (BudgetIndex M K) ℂ).toBasis _ _).mpr
  intro s t
  change inner ℂ (finiteOperator M K (hamiltonian M) (finiteKet M K s)) (finiteKet M K t) =
    inner ℂ (finiteKet M K s) (finiteOperator M K (hamiltonian M) (finiteKet M K t))
  rw [hd, hd, inner_smul_left, inner_smul_right]
  by_cases h : s = t
  · subst t; simp
  · have hi : inner ℂ (finiteKet M K s) (finiteKet M K t) = 0 :=
      (EuclideanSpace.basisFun (BudgetIndex M K) ℂ).orthonormal.2 h
    simp [hi]


/-- Energy eigenvalues survive exact finite-coordinate transport. -/
theorem finite_hamiltonian_ket (M K : ℕ) (s : BudgetIndex M K) : finiteOperator M K (hamiltonian M) (finiteKet M K s) = (energy M (indexExponent M K s) : ℂ) • finiteKet M K s := by
  classical
  have he : embedding M K (finiteKet M K s) =
      (normalization M (indexExponent M K s))⁻¹ • monomial M (indexExponent M K s) := by
    exact (EuclideanSpace.basisFun (BudgetIndex M K) ℂ).toBasis.constr_basis ℂ _ s
  have hc : coordinates M K ((normalization M (indexExponent M K s))⁻¹ • monomial M (indexExponent M K s)) = finiteKet M K s := by
    rw [← he]
    exact LinearMap.congr_fun (coordinates_embedding M K) _
  simp only [finiteOperator, LinearMap.comp_apply, he, map_smul, hamiltonian_monomial]
  rw [smul_smul, mul_comm, ← smul_smul, ← map_smul, hc]


/-- Compressed creation raises energy until it leaves the finite budget. -/
theorem finite_creation_nilpotent (M K : ℕ) (i : Mode M) : finiteOperator M K (creation M i) ^ (K + 1) = 0 := by
  have ha : finiteOperator M K (annihilation M i) ^ (K + 1) = 0 := by
    have hfix (p : Polynomial M) (hp : p ∈ budget M K) : projection M K p = p := by
      rw [← projection_range M K] at hp
      rcases hp with ⟨q, rfl⟩
      exact LinearMap.congr_fun (projection_idempotent M K) q
    have hmem (v : FiniteFock M K) : embedding M K v ∈ budget M K := by
      rw [← embedding_range M K]
      exact ⟨v, rfl⟩
    have hinter (v : FiniteFock M K) : embedding M K (finiteOperator M K (annihilation M i) v) =
        annihilation M i (embedding M K v) := by
      change (embedding M K).comp (coordinates M K) (annihilation M i (embedding M K v)) = _
      rw [embedding_coordinates]
      exact hfix _ (budget_mono M (K - weight M i) K (Nat.sub_le _ _) (annihilation_budget M K i _ (hmem v)))
    have hpow (n : ℕ) (v : FiniteFock M K) : embedding M K ((finiteOperator M K (annihilation M i) ^ n) v) =
        (annihilation M i ^ n) (embedding M K v) := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hinter, ih]
    apply LinearMap.ext
    intro v
    have he : embedding M K ((finiteOperator M K (annihilation M i) ^ (K + 1)) v) = 0 := by
      rw [hpow]
      exact annihilation_power_budget M K i _ (hmem v)
    have hc := LinearMap.congr_fun (coordinates_embedding M K) ((finiteOperator M K (annihilation M i) ^ (K + 1)) v)
    change coordinates M K (embedding M K _) = _ at hc
    rw [he, map_zero] at hc
    exact hc.symm
  have h := congrArg LinearMap.adjoint ha
  rw [← finite_creation_adjoint M K i] at h
  change star (star (finiteOperator M K (creation M i)) ^ (K + 1)) = star (0 : Module.End ℂ (FiniteFock M K)) at h
  simpa only [star_pow, star_star, star_zero] using h


/-- Compressed annihilation lowers occupation until it reaches zero. -/
theorem finite_annihilation_nilpotent (M K : ℕ) (i : Mode M) : finiteOperator M K (annihilation M i) ^ (K + 1) = 0 := by
  have hfix (p : Polynomial M) (hp : p ∈ budget M K) : projection M K p = p := by
    rw [← projection_range M K] at hp
    rcases hp with ⟨q, rfl⟩
    exact LinearMap.congr_fun (projection_idempotent M K) q
  have hmem (v : FiniteFock M K) : embedding M K v ∈ budget M K := by
    rw [← embedding_range M K]
    exact ⟨v, rfl⟩
  have hinter (v : FiniteFock M K) : embedding M K (finiteOperator M K (annihilation M i) v) =
      annihilation M i (embedding M K v) := by
    change (embedding M K).comp (coordinates M K) (annihilation M i (embedding M K v)) = _
    rw [embedding_coordinates]
    exact hfix _ (budget_mono M (K - weight M i) K (Nat.sub_le _ _) (annihilation_budget M K i _ (hmem v)))
  have hpow (n : ℕ) (v : FiniteFock M K) : embedding M K ((finiteOperator M K (annihilation M i) ^ n) v) =
      (annihilation M i ^ n) (embedding M K v) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hinter, ih]
  apply LinearMap.ext
  intro v
  have he : embedding M K ((finiteOperator M K (annihilation M i) ^ (K + 1)) v) = 0 := by
    rw [hpow]
    exact annihilation_power_budget M K i _ (hmem v)
  have hc := LinearMap.congr_fun (coordinates_embedding M K) ((finiteOperator M K (annihilation M i) ^ (K + 1)) v)
  change coordinates M K (embedding M K _) = _ at hc
  rw [he, map_zero] at hc
  exact hc.symm


/-- Both leakage remainders are retained with their exact noncommutative order. -/
theorem compressed_commutator (M K : ℕ) (A B : Operators M) :
    commutator M (compressed M K A) (compressed M K B) =
      projection M K * commutator M A B * projection M K
      - projection M K * A * (1 - projection M K) * B * projection M K
      + projection M K * B * (1 - projection M K) * A * projection M K := by
  have hP := projection_idempotent M K
  unfold commutator compressed
  noncomm_ring [hP]
  simp only [← mul_assoc (projection M K) (projection M K), hP]

/-- A nonzero finite carrier cannot realize a nonzero scalar identity as a commutator. -/
theorem finite_ccr_obstruction (M K : ℕ) (i : Mode M) :
    finiteOperator M K (annihilation M i) * finiteOperator M K (creation M i)
      - finiteOperator M K (creation M i) * finiteOperator M K (annihilation M i)
      ≠ (weight M i : ℂ) • (1 : Module.End ℂ (FiniteFock M K)) := by
  classical
  let : Nontrivial (FiniteFock M K) := ⟨⟨finiteVacuum M K, 0, finiteVacuum_ne_zero M K⟩⟩
  intro h
  have ht := congrArg (LinearMap.trace ℂ (FiniteFock M K)) h
  simp only [map_sub, map_smul, LinearMap.trace_mul_comm,
    sub_self, LinearMap.trace_one, smul_eq_mul] at ht
  have hw : (weight M i : ℂ) ≠ 0 := by exact_mod_cast (weight_pos M i).ne'
  have hn : (Module.finrank ℂ (FiniteFock M K) : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := FiniteFock M K)).ne'
  exact mul_ne_zero hw hn ht.symm


/-- A certified nilpotent exponential is independent of any larger Taylor cutoff. -/
theorem expNil_cutoff (M K d e : ℕ) (A : Module.End ℂ (FiniteFock M K)) (hd : A ^ (d + 1) = 0) (hde : d ≤ e) : taylor M K A e = expNil M K A d hd := by
  have hz (j : ℕ) (hj : d + 1 ≤ j) : A ^ j = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [pow_add, hd, zero_mul]
  unfold expNil
  unfold taylor
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hde 1))
  intro j hj hnot
  rw [hz j (by simpa only [Finset.mem_range, not_lt] using hnot), smul_zero]

/-- Negating a nilpotent operator gives the inverse finite exponential. -/
theorem expNil_inverse (M K d : ℕ) (A : Module.End ℂ (FiniteFock M K)) (hd : A ^ (d + 1) = 0) : expNil M K A d hd * taylor M K (-A) d = 1 := by
  have hneg : (-A) ^ (d + 1) = 0 := by rw [neg_pow, hd, mul_zero]
  have bridge (B : Module.End ℂ (FiniteFock M K)) (hB : B ^ (d + 1) = 0) :
      IsNilpotent.exp B = taylor M K B d := by
    rw [IsNilpotent.exp_eq_sum hB]
    unfold taylor
    apply Finset.sum_congr rfl
    intro j hj
    simpa using ratCast_smul_eq ℚ ℂ ((j.factorial : ℚ)⁻¹) (B ^ j)
  rw [expNil, ← bridge A hd, ← bridge (-A) hneg]
  exact IsNilpotent.exp_mul_exp_neg_self ⟨d + 1, hd⟩

/-- Taking an actual finite adjoint commutes with real factorial Taylor coefficients. -/
theorem taylor_adjoint (M K d : ℕ) (A : Module.End ℂ (FiniteFock M K)) : LinearMap.adjoint (taylor M K A d) = taylor M K (LinearMap.adjoint A) d := by
  simp [taylor, ← LinearMap.star_eq_adjoint]

/-- Coefficientwise associativity fixes the formal-series interpretation. -/
theorem formalProduct_assoc (M : ℕ) (f g h : FormalOperators M) : formalProduct M (formalProduct M f g) h = formalProduct M f (formalProduct M g h) := by
  funext n
  simp only [formalProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun (x : Σ _ : ℕ, ℕ) _ => (⟨x.2, x.1 - x.2⟩ : Σ _ : ℕ, ℕ))
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_sigma, Finset.mem_range] at ha hb
    have h₁ := congrArg Sigma.fst hab
    change a.2 = b.2 at h₁
    have h₂ : a.1 - a.2 = b.1 - b.2 := by simpa using congrArg (fun (x : Σ _ : ℕ, ℕ) => x.2) hab
    apply Sigma.ext
    · omega
    · simp only [heq_eq_eq]
      exact h₁
  · intro b hb
    simp only [Finset.mem_sigma, Finset.mem_range] at hb
    refine ⟨⟨b.1 + b.2, b.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · simp
  · intro a ha
    simp only [Finset.mem_sigma, Finset.mem_range] at ha
    have hs : n - a.2 - (a.1 - a.2) = n - a.1 := by omega
    simp only [hs, mul_assoc]

/-- The central t-squared correction belongs only to the ambient scalar CCR. -/
theorem formal_bch (M : ℕ) (i j : Mode M) (α β : ℂ) (n : ℕ) :
    formalProduct M (expCoefficient M (α • annihilation M i)) (expCoefficient M (β • creation M j)) n =
      formalProduct M
        (formalProduct M (expCoefficient M (β • creation M j)) (expCoefficient M (α • annihilation M i)))
        (gaussianCoefficient M (if i = j then (weight M i : ℂ) * α * β else 0)) n := by sorry

/-- Single-mode words admit an independent normal-symbol expansion including contractions. -/
theorem word_normal_form (M : ℕ) (i : Mode M) (letters : List Bool) : ∃ s : NormalSymbols, normalEvaluation M i s = wordEvaluation M i letters := by
  let C := creation M i
  let D := derivative M i
  let v : ℕ × ℕ → Operators M := fun ab => C ^ ab.1 * D ^ ab.2
  let S : Submodule ℂ (Operators M) := Submodule.span ℂ (Set.range v)
  have gen (a b : ℕ) : C ^ a * D ^ b ∈ S :=
    Submodule.subset_span ⟨(a, b), rfl⟩
  have dc (a b : ℕ) : D * (C ^ a * D ^ b) =
      C ^ a * D ^ (b + 1) + (a : ℂ) • (C ^ (a - 1) * D ^ b) := by
    apply LinearMap.ext
    intro p
    simp [C, D, creation, derivative, Module.End.mul_apply, pow_succ',
      MvPolynomial.smul_eq_C_mul]
    ring
  have closedC (x : Operators M) (hx : x ∈ S) : C * x ∈ S := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a,b⟩, rfl⟩ := hx
      simpa [v, pow_succ', mul_assoc] using gen (a + 1) b
    | zero => simp
    | add x y hx hy ihx ihy => simpa [mul_add] using S.add_mem ihx ihy
    | smul a x hx ih => simpa [mul_smul_comm] using S.smul_mem a ih
  have closedD (x : Operators M) (hx : x ∈ S) : D * x ∈ S := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a,b⟩, rfl⟩ := hx
      change D * (C ^ a * D ^ b) ∈ S
      rw [dc]
      exact S.add_mem (gen a (b + 1)) (S.smul_mem _ (gen (a - 1) b))
    | zero => simp
    | add x y hx hy ihx ihy => simpa [mul_add] using S.add_mem ihx ihy
    | smul a x hx ih => simpa [mul_smul_comm] using S.smul_mem a ih
  have hw : wordEvaluation M i letters ∈ S := by
    induction letters using List.reverseRecOn with
    | nil => simpa [wordEvaluation, A03.applicationWord] using gen 0 0
    | append_singleton l b ih =>
      cases b with
      | false =>
        simpa [wordEvaluation, A03.applicationWord, List.reverse_append, List.prod_append, D]
          using closedD _ ih
      | true =>
        simpa [wordEvaluation, A03.applicationWord, List.reverse_append, List.prod_append, C]
          using closedC _ ih
  have hr : (normalEvaluation M i).range = S := Finsupp.range_linearCombination ℂ
  rw [← hr] at hw
  exact LinearMap.mem_range.mp hw

/-- Normal-ordered powers reduce to pure creator powers on the vacuum. -/
theorem normalPower_vacuum (M : ℕ) (i : Mode M) (n : ℕ) : normalPower M i n (vacuum M) = MvPolynomial.X i ^ n := by
  have hc (k : ℕ) : (creation M i ^ k) (vacuum M) = MvPolynomial.X i ^ k := by
    simp [creation, vacuum]
  have hd (k : ℕ) (hk : 0 < k) : (derivative M i ^ k) (vacuum M) = 0 := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [pow_succ, Module.End.mul_apply]
    simp [derivative, vacuum]
  unfold normalPower
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_single n]
  · simp [hc]
  · intro j hj hjn
    have hlt : j < n := by have := Finset.mem_range.mp hj; omega
    simp [Module.End.mul_apply, hd (n - j) (by omega)]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim

/-- The exact Wick expansion uses unweighted D and C, whose contraction is one. -/
theorem wick_operator (M : ℕ) (i : Mode M) (n : ℕ) :
    (derivative M i + creation M i) ^ n =
      ∑ k ∈ Finset.range (n / 2 + 1),
        ((n.factorial : ℂ) / ((k.factorial : ℂ) * ((n - 2 * k).factorial : ℂ) * (2 : ℂ) ^ k))
          • normalPower M i (n - 2 * k) := by
  classical
  let T : Operators M := derivative M i + creation M i
  let N : ℕ → Operators M := normalPower M i
  have h0 : N 0 = 1 := by simp [N, normalPower]
  have hs (n : ℕ) :
      (derivative M i + creation M i) * normalPower M i (n + 1) =
        normalPower M i (n + 2) + ((n + 1 : ℕ) : ℂ) • normalPower M i n := by
    let C := creation M i
    let D := derivative M i
    have dc (a b : ℕ) : D * (C ^ a * D ^ b) =
        C ^ a * D ^ (b + 1) + (a : ℂ) • (C ^ (a - 1) * D ^ b) := by
      apply LinearMap.ext
      intro p
      simp [C, D, creation, derivative, Module.End.mul_apply, pow_succ', MvPolynomial.smul_eq_C_mul]
      ring
    have pascal (m : ℕ) : normalPower M i (m + 1) =
        C * normalPower M i m + ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℂ) • (C ^ j * D ^ (m - j + 1)) := by
      change (∑ j ∈ Finset.range (m + 2), (Nat.choose (m + 1) j : ℂ) • (C ^ j * D ^ (m + 1 - j))) = _
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, one_smul, pow_zero, one_mul, Nat.sub_zero]
      simp_rw [Nat.choose_succ_succ', Nat.cast_add, add_smul]
      rw [Finset.sum_add_distrib]
      have hc : (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℂ) • (C ^ (j + 1) * D ^ (m + 1 - (j + 1)))) = C * normalPower M i m := by
        unfold normalPower
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp [C, D, Nat.add_sub_add_right, pow_succ', mul_assoc]
      rw [hc]
      have hz : (∑ j ∈ Finset.range (m + 1), (Nat.choose m (j + 1) : ℂ) • (C ^ (j + 1) * D ^ (m + 1 - (j + 1)))) + D ^ (m + 1) =
          ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℂ) • (C ^ j * D ^ (m - j + 1)) := by
        rw [Finset.sum_range_succ]
        simp only [Nat.choose_succ_self, Nat.cast_zero, zero_smul, add_zero]
        rw [Finset.sum_range_succ']
        simp only [Nat.choose_zero_right, Nat.cast_one, one_smul, pow_zero, one_mul, Nat.sub_zero]
        apply congrArg₂ (· + ·) ?_ rfl
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        congr 1
        have hjm : j < m := Finset.mem_range.mp hj
        omega
      rw [add_assoc, hz]
    change (D + C) * normalPower M i (n + 1) = _
    rw [add_mul]
    nth_rw 1 [normalPower]
    rw [Finset.mul_sum]
    change (∑ j ∈ Finset.range (n + 2), D * ((Nat.choose (n + 1) j : ℂ) • (C ^ j * D ^ (n + 1 - j)))) + C * normalPower M i (n + 1) = _
    simp_rw [mul_smul_comm, dc, smul_add]
    rw [Finset.sum_add_distrib]
    have corr : (∑ j ∈ Finset.range (n + 2), (Nat.choose (n + 1) j : ℂ) • ((j : ℂ) • (C ^ (j - 1) * D ^ (n + 1 - j)))) =
        ((n + 1 : ℕ) : ℂ) • normalPower M i n := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_smul, smul_zero, add_zero]
      unfold normalPower
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [smul_smul, smul_smul]
      have coeff : (Nat.choose (n + 1) (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) * (Nat.choose n j : ℂ) := by
        exact_mod_cast (Nat.add_one_mul_choose_eq n j).symm
      rw [coeff]
      simp [C, D]
    rw [corr]
    rw [pascal (n + 1)]
    change _ = C * _ + _ + _
    abel
  have hrec (m : ℕ) : T * N m = N (m + 1) + (m : ℂ) • N (m - 1) := by
    cases m with
    | zero => simp [T, N, normalPower, Finset.sum_range_succ, add_comm]
    | succ m => simpa [T, N, Nat.add_assoc] using hs m
  let a (n k : ℕ) : ℂ :=
    if 2*k ≤ n then (n.factorial : ℂ) / ((k.factorial : ℂ) * ((n-2*k).factorial : ℂ) * (2 : ℂ)^k) else 0
  have a_zero (n : ℕ) : a n 0 = 1 := by
    simp [a, Nat.factorial_ne_zero]
  have a_succ (n k : ℕ) : a (n+1) (k+1) = a n (k+1) + ((n-2*k : ℕ) : ℂ)*a n k := by
    have hf (a : ℕ) : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
    by_cases h : 2*(k+1) ≤ n
    · have hk : 2*k ≤ n := by omega
      have hnk : n-2*k = (n-2*(k+1))+2 := by omega
      have hnk' : n+1-2*(k+1) = (n-2*(k+1))+1 := by omega
      simp only [a, ite_eq_left h, ite_eq_left (by omega : 2*(k+1)≤n+1), ite_eq_left hk]
      field_simp [hf]
      rw [hnk, hnk']
      simp only [Nat.factorial_succ, pow_succ]
      push_cast
      have hnc : (n:ℂ) = ((n-2*(k+1):ℕ):ℂ) + 2*(k+1) := by
        exact_mod_cast (show n = n-2*(k+1)+2*(k+1) by omega)
      rw [hnc]
      ring
    · by_cases he : 2*(k+1) = n+1
      · have hk : 2*k≤n := by omega
        have hnk : n-2*k=1 := by omega
        have hnk' : n+1-2*(k+1)=0 := by omega
        simp only [a, ite_eq_right h, ite_eq_left (by omega : 2*(k+1)≤n+1), ite_eq_left hk]
        field_simp [hf]
        rw [hnk, hnk']
        simp only [Nat.factorial_succ, pow_succ]
        push_cast
        norm_num
        have hnc : (n:ℂ)+1 = 2*((k:ℂ)+1) := by exact_mod_cast he.symm
        rw [hnc]
        ring
      · have hx : ¬2*(k+1)≤n+1 := by omega
        simp only [a, ite_eq_right h, ite_eq_right hx, zero_add]
        by_cases hk : 2*k≤n
        · have hnk : n-2*k=0 := by omega
          simp [hnk]
        · simp [hk]
  have hseq (n : ℕ) : T^n = ∑ k ∈ Finset.range (n+1), a n k • N (n-2*k) := by
    induction n with
    | zero => simp [a,h0]
    | succ n ih =>
      have hbound : a n (n+1) = 0 := by simp [a]; omega
      have harg1 (k : ℕ) : a n k • N ((n-2*k)+1) = a n k • N (n+1-2*k) := by
        by_cases hk : 2*k≤n
        · congr 2; omega
        · simp [a,hk]
      have harg2 (k : ℕ) : a n k • ((n-2*k:ℕ):ℂ) • N ((n-2*k)-1) =
         (((n-2*k:ℕ):ℂ)*a n k) • N (n+1-2*(k+1)) := by
        have hn : (n-2*k)-1 = n+1-2*(k+1) := by omega
        rw [hn,smul_smul,mul_comm]
      rw [pow_succ',ih,Finset.mul_sum]
      simp_rw [mul_smul_comm,hrec,smul_add,harg1,harg2]
      rw [Finset.sum_add_distrib]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [a_zero,one_smul,mul_zero,Nat.sub_zero]
      simp_rw [a_succ,add_smul]
      rw [Finset.sum_add_distrib]
      have hf : ∑ k ∈ Finset.range (n+1), a n k • N (n+1-2*k) =
        N (n+1) + ∑ k ∈ Finset.range (n+1), a n (k+1) • N (n+1-2*(k+1)) := by
        have hpad : ∑ k ∈ Finset.range (n+2), a n k • N (n+1-2*k) =
            ∑ k ∈ Finset.range (n+1), a n k • N (n+1-2*k) := by
          rw [show n+2 = (n+1)+1 by omega,Finset.sum_range_succ,hbound,zero_smul,add_zero]
        rw [← hpad,Finset.sum_range_succ']
        simp [a_zero,add_comm]
      rw [hf]
      abel
  change T^n = ∑ k ∈ Finset.range (n/2+1),
    ((n.factorial : ℂ) / ((k.factorial : ℂ) * ((n-2*k).factorial : ℂ) * (2 : ℂ)^k)) • N (n-2*k)
  rw [hseq n]
  have hsub : Finset.range (n/2+1) ⊆ Finset.range (n+1) := by
    apply Finset.range_mono
    have hd := Nat.div_le_self n 2
    omega
  have hs := Finset.sum_subset (f := fun k => a n k • N (n-2*k)) hsub
    (fun k hk hkn => by
      have hkn' := Finset.mem_range.not.mp hkn
      have hbad : ¬2*k≤n := by omega
      simp [a,hbad])
  rw [← hs]
  apply Finset.sum_congr rfl
  intro k hk
  have hkp : 2*k≤n := by have := Finset.mem_range.mp hk; omega
  simp [a,hkp]


/-- The zeroth positive-contraction polynomial is the vacuum. -/
theorem wick_zero (M : ℕ) (i : Mode M) : wickPolynomial M i 0 = vacuum M := by
  simp [wickPolynomial]

/-- The positive contraction gives X squared plus one, not the Hermite sign. -/
theorem wick_two (M : ℕ) (i : Mode M) : wickPolynomial M i 2 = MvPolynomial.X i ^ 2 + 1 := by
  simp [wickPolynomial, pow_two, Module.End.mul_apply, creation, derivative, vacuum, add_comm]

/-- The opposite derivative sign gives the probabilists Hermite convention. -/
theorem hermite_two (M : ℕ) (i : Mode M) : hermitePolynomial M i 2 = MvPolynomial.X i ^ 2 - 1 := by
  simp [hermitePolynomial, pow_two, Module.End.mul_apply, creation, derivative, vacuum]

/-- The positive-contraction sequence is an Appell sequence. -/
theorem wick_derivative (M : ℕ) (i : Mode M) (n : ℕ) : derivative M i (wickPolynomial M i n) = (n : ℂ) • wickPolynomial M i (n - 1) := by
  let T := derivative M i + creation M i
  have step (p : Polynomial M) : derivative M i (T p) = T (derivative M i p) + p := by
    dsimp [T, derivative, creation]
    simp only [map_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self, one_mul]
    abel
  have aux (r : ℕ) (p : Polynomial M) :
      derivative M i ((T ^ (r + 1)) p) =
        (T ^ (r + 1)) (derivative M i p) + (r + 1 : ℂ) • (T ^ r) p := by
    induction r with
    | zero => simpa using step p
    | succ r ih =>
      rw [pow_succ', Module.End.mul_apply, step, ih, map_add, map_smul]
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      simp only [pow_succ', Module.End.mul_apply]
      abel
  cases n with
  | zero => simp [wickPolynomial, derivative, vacuum]
  | succ r =>
    simpa [wickPolynomial, T, derivative, vacuum] using aux r (vacuum M)

/-- Vacuum polynomials satisfy the source recurrence with the positive contraction sign. -/
theorem wick_recurrence (M : ℕ) (i : Mode M) (n : ℕ) : wickPolynomial M i (n + 1) = creation M i (wickPolynomial M i n) + (n : ℂ) • wickPolynomial M i (n - 1) := by
  rw [wickPolynomial, pow_succ', Module.End.mul_apply, LinearMap.add_apply]
  rw [show ((derivative M i + creation M i) ^ n) (vacuum M) = wickPolynomial M i n from rfl,
    wick_derivative]
  exact add_comm _ _

/-- The generating function exp(X t plus t squared over two) is stated coefficientwise. -/
theorem wick_coefficients (M : ℕ) (i : Mode M) (n : ℕ) :
    ((n.factorial : ℂ)⁻¹) • wickPolynomial M i n =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (((n - 2 * k).factorial : ℂ) * (k.factorial : ℂ) * (2 : ℂ) ^ k)⁻¹
          • (MvPolynomial.X i ^ (n - 2 * k)) := by
  rw [wickPolynomial, wick_operator, LinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [LinearMap.smul_apply, normalPower_vacuum, smul_smul]
  congr 1
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnf : ((n - 2 * k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - 2 * k)
  field_simp

end Bosonize.Ch08
```
