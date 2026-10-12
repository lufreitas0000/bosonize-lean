module

public import Bosonize.Core.Ch08Boson

/-!
# A05 — Exact finite Taylor operators on actual complex modules

These polynomials act on the supplied module itself. Finite dimensionality does
not certify nilpotency: every inverse or cutoff theorem retains a power-vanishing
hypothesis. Multiplication of endomorphisms applies its right factor first.
The adjoint statement uses an actual finite-dimensional inner-product structure.
No infinite series, convergence, physical phase nilpotency, or vertex identity is
asserted by this foundation.
-/

@[expose] public section

namespace Bosonize.A05Exp
open scoped BigOperators Classical

/-- The Taylor polynomial through degree `d`, with factorial coefficients in ℂ.
It is meaningful on any complex module; the cutoff is part of the data, rather
than a claim that the supplied operator has nilpotency degree `d + 1`. -/
noncomputable def finiteTaylor {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) : Module.End ℂ V :=
  ∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) • A ^ j

/-- Degree zero consists of the constant identity term, even for nonnilpotent
operators. This base case fixes the polynomial convention. -/
theorem finite_taylor_zero_cutoff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) : finiteTaylor 0 A = 1 := by sorry

/-- The zero endomorphism has Taylor polynomial equal to the identity at every
cutoff. Positive powers vanish while its zeroth power remains the identity. -/
theorem finite_taylor_zero_operator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) : finiteTaylor d (0 : Module.End ℂ V) = 1 := by sorry

/-- Evaluating the polynomial is the finite sum of the actual power actions on
`v`; the endomorphism is not replaced by a separately postulated exponential. -/
theorem finite_taylor_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (v : V) :
    finiteTaylor d A v = ∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) • (A ^ j) v := by sorry

/-- An operator commutes with its own Taylor polynomial. This algebraic fact
needs neither a Hilbert structure nor a nilpotency certificate. -/
theorem finite_taylor_commute {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) : Commute A (finiteTaylor d A) := by sorry

/-- A genuine intertwining map transports every power and hence the Taylor
polynomial. The map may connect different actual source and target modules. -/
theorem finite_taylor_intertwine {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (d : ℕ) (A : Module.End ℂ V)
    (B : Module.End ℂ W) (T : V →ₗ[ℂ] W) (hT : T.comp A = B.comp T) :
    T.comp (finiteTaylor d A) = (finiteTaylor d B).comp T := by sorry

/-- Once the specified power vanishes, every larger cutoff gives exactly the
same operator. The hypothesis concerns the actual ambient endomorphism. -/
theorem finite_taylor_cutoff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d e : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) (hde : d ≤ e) :
    finiteTaylor e A = finiteTaylor d A := by sorry

/-- The Taylor polynomial of `-A` is a right inverse when the actual operator
has the stated vanishing power. This is an exact finite algebraic identity. -/
theorem finite_taylor_mul_neg {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) :
    finiteTaylor d A * finiteTaylor d (-A) = 1 := by sorry

/-- The same negative polynomial is also a left inverse. Both directions are
stated because downstream typed compositions must use the appropriate order. -/
theorem finite_taylor_neg_mul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) :
    finiteTaylor d (-A) * finiteTaylor d A = 1 := by sorry

/-- The proved left inverse makes the nilpotent Taylor action injective on the
supplied module; no finite-dimensional argument or abstract substitute is used. -/
theorem finite_taylor_injective {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) :
    Function.Injective (finiteTaylor d A) := by sorry

/-- The proved right inverse makes the nilpotent Taylor action surjective, even
on an infinite-dimensional module. The preimage is given by the negative polynomial. -/
theorem finite_taylor_surjective {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) :
    Function.Surjective (finiteTaylor d A) := by sorry

/-- A nonzero vector remains nonzero under the certified nilpotent Taylor
operator. This is the usable nondegeneracy consequence for vertex factors. -/
theorem finite_taylor_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0)
    (v : V) (hv : v ≠ 0) : finiteTaylor d A v ≠ 0 := by sorry

/-- Real factorial coefficients commute with taking the actual Hilbert adjoint.
For products of such factors, adjoints still reverse their multiplication order;
this statement alone does not permit commuting different phase operators. -/
theorem finite_taylor_adjoint {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (d : ℕ) (A : Module.End ℂ V) :
    LinearMap.adjoint (finiteTaylor d A) = finiteTaylor d (LinearMap.adjoint A) := by sorry

/-- An explicitly bounded filtration certifies nilpotency: its bottom level is
zero, its top level is the whole actual module, and each application lowers one
level. No monotonicity or finite-dimensionality is assumed or used. Physical
compressed phases must separately prove these mapping hypotheses for their
chosen filtration, rather than infer them from an input budget. -/
theorem filtration_nilpotent {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (F : ℕ → Submodule ℂ V)
    (hbottom : F 0 = ⊥) (htop : F (d + 1) = ⊤)
    (hlower : ∀ n ≤ d, ∀ v ∈ F (n + 1), A v ∈ F n) :
    A ^ (d + 1) = 0 := by sorry

end Bosonize.A05Exp
