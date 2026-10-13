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
    (A : Module.End ℂ V) : finiteTaylor 0 A = 1 := by
  simp [finiteTaylor]

/-- The zero endomorphism has Taylor polynomial equal to the identity at every
cutoff. Positive powers vanish while its zeroth power remains the identity. -/
theorem finite_taylor_zero_operator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) : finiteTaylor d (0 : Module.End ℂ V) = 1 := by
  induction d with
  | zero => simp [finiteTaylor]
  | succ d ih =>
    unfold finiteTaylor at *
    rw [Finset.sum_range_succ, ih]
    simp

/-- Evaluating the polynomial is the finite sum of the actual power actions on
`v`; the endomorphism is not replaced by a separately postulated exponential. -/
theorem finite_taylor_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (v : V) :
    finiteTaylor d A v = ∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) • (A ^ j) v := by
  simp [finiteTaylor, LinearMap.sum_apply]

/-- An operator commutes with its own Taylor polynomial. This algebraic fact
needs neither a Hilbert structure nor a nilpotency certificate. -/
theorem finite_taylor_commute {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) : Commute A (finiteTaylor d A) := by
  unfold finiteTaylor
  apply Commute.sum_right
  intro j hj
  exact (Commute.refl A).pow_right j |>.smul_right _

/-- A genuine intertwining map transports every power and hence the Taylor
polynomial. The map may connect different actual source and target modules. -/
theorem finite_taylor_intertwine {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (d : ℕ) (A : Module.End ℂ V)
    (B : Module.End ℂ W) (T : V →ₗ[ℂ] W) (hT : T.comp A = B.comp T) :
    T.comp (finiteTaylor d A) = (finiteTaylor d B).comp T := by
  have hp (j : ℕ) : T.comp (A ^ j) = (B ^ j).comp T := by
    induction j with
    | zero => ext v; simp only [pow_zero, LinearMap.comp_apply, Module.End.one_apply]
    | succ j ih =>
      rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, hT, ← LinearMap.comp_assoc]
  ext v
  simp only [LinearMap.comp_apply, finite_taylor_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show T ((A ^ j) v) = (B ^ j) (T v) from congrArg (fun f : V →ₗ[ℂ] W => f v) (hp j)]

/-- Once the specified power vanishes, every larger cutoff gives exactly the
same operator. The hypothesis concerns the actual ambient endomorphism. -/
theorem finite_taylor_cutoff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d e : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) (hde : d ≤ e) :
    finiteTaylor e A = finiteTaylor d A := by
  have hz (j : ℕ) (hj : d + 1 ≤ j) : A ^ j = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [pow_add, hnil, zero_mul]
  unfold finiteTaylor
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hde 1))
  intro j hj hnot
  rw [hz j (by simpa only [Finset.mem_range, not_lt] using hnot), smul_zero]

/-- The Taylor polynomial of `-A` is a right inverse when the actual operator
has the stated vanishing power. This is an exact finite algebraic identity. -/
theorem finite_taylor_mul_neg {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) :
    finiteTaylor d A * finiteTaylor d (-A) = 1 := by
  let : Module ℚ (Module.End ℂ V) := Module.compHom _ (algebraMap ℚ ℂ)
  let : IsScalarTower ℚ ℂ (Module.End ℂ V) := IsScalarTower.of_compHom ℚ ℂ _
  have hneg : (-A) ^ (d + 1) = 0 := by rw [neg_pow, hnil, mul_zero]
  have bridge (B : Module.End ℂ V) (hB : B ^ (d + 1) = 0) :
      IsNilpotent.exp B = finiteTaylor d B := by
    rw [IsNilpotent.exp_eq_sum hB]
    unfold finiteTaylor
    apply Finset.sum_congr rfl
    intro j hj
    simpa using ratCast_smul_eq ℚ ℂ ((j.factorial : ℚ)⁻¹) (B ^ j)
  rw [← bridge A hnil, ← bridge (-A) hneg]
  exact IsNilpotent.exp_mul_exp_neg_self ⟨d + 1, hnil⟩

/-- The same negative polynomial is also a left inverse. Both directions are
stated because downstream typed compositions must use the appropriate order. -/
theorem finite_taylor_neg_mul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) :
    finiteTaylor d (-A) * finiteTaylor d A = 1 := by
  have hneg : (-A) ^ (d + 1) = 0 := by rw [neg_pow, hnil, mul_zero]
  simpa using finite_taylor_mul_neg d (-A) hneg

/-- The proved left inverse makes the nilpotent Taylor action injective on the
supplied module; no finite-dimensional argument or abstract substitute is used. -/
theorem finite_taylor_injective {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) :
    Function.Injective (finiteTaylor d A) := by
  intro v w hvw
  have hi := finite_taylor_neg_mul d A hnil
  have hv := congrArg (fun T : Module.End ℂ V => T v) hi
  have hw := congrArg (fun T : Module.End ℂ V => T w) hi
  simpa only [Module.End.mul_apply, Module.End.one_apply] using hv.symm.trans ((congrArg (finiteTaylor d (-A)) hvw).trans hw)

/-- The proved right inverse makes the nilpotent Taylor action surjective, even
on an infinite-dimensional module. The preimage is given by the negative polynomial. -/
theorem finite_taylor_surjective {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0) :
    Function.Surjective (finiteTaylor d A) := by
  intro v
  refine ⟨finiteTaylor d (-A) v, ?_⟩
  have hi := congrArg (fun T : Module.End ℂ V => T v) (finite_taylor_mul_neg d A hnil)
  simpa only [Module.End.mul_apply, Module.End.one_apply] using hi

/-- A nonzero vector remains nonzero under the certified nilpotent Taylor
operator. This is the usable nondegeneracy consequence for vertex factors. -/
theorem finite_taylor_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (hnil : A ^ (d + 1) = 0)
    (v : V) (hv : v ≠ 0) : finiteTaylor d A v ≠ 0 := by
  intro hz
  apply hv
  exact finite_taylor_injective d A hnil (hz.trans (map_zero _).symm)

/-- Real factorial coefficients commute with taking the actual Hilbert adjoint.
For products of such factors, adjoints still reverse their multiplication order;
this statement alone does not permit commuting different phase operators. -/
theorem finite_taylor_adjoint {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (d : ℕ) (A : Module.End ℂ V) :
    LinearMap.adjoint (finiteTaylor d A) = finiteTaylor d (LinearMap.adjoint A) := by
  simp [finiteTaylor, ← LinearMap.star_eq_adjoint]

/-- An explicitly bounded filtration certifies nilpotency: its bottom level is
zero, its top level is the whole actual module, and each application lowers one
level. No monotonicity or finite-dimensionality is assumed or used. Physical
compressed phases must separately prove these mapping hypotheses for their
chosen filtration, rather than infer them from an input budget. -/
theorem filtration_nilpotent {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : ℕ) (A : Module.End ℂ V) (F : ℕ → Submodule ℂ V)
    (hbottom : F 0 = ⊥) (htop : F (d + 1) = ⊤)
    (hlower : ∀ n ≤ d, ∀ v ∈ F (n + 1), A v ∈ F n) :
    A ^ (d + 1) = 0 := by
  have hz : ∀ n, n ≤ d + 1 → ∀ v ∈ F n, (A ^ n) v = 0 := by
    intro n
    induction n with
    | zero =>
      intro hn v hv
      rw [hbottom, Submodule.mem_bot] at hv
      simp [hv]
    | succ n ih =>
      intro hn v hv
      have hav : A v ∈ F n := hlower n (by omega) v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih (by omega) (A v) hav
  ext v
  change (A ^ (d + 1)) v = 0
  exact hz (d + 1) le_rfl v (by rw [htop]; trivial)

end Bosonize.A05Exp
