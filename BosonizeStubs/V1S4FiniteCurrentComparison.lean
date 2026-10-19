import Bosonize.Core.A05MultiSpecies
import Bosonize.Core.A08OscillatorStates

/-! V1-S4: exact finite current-word comparison on certified paths.
The actual free finite sea realizes selected ordinary and inverse-Bogoliubov
word moments, with explicit weighted-energy and regulator hypotheses.
-/

@[expose] public section
namespace Bosonize.V1S4

open scoped BigOperators

noncomputable local instance orientationFintype : Fintype Bosonize.A06.Orientation :=
  ⟨⟨{.right, .left}, by decide⟩, fun o => by cases o <;> simp⟩

abbrev Generator (M : ℕ) := Bosonize.A08.OscGen M
abbrev Word (M : ℕ) := List (Generator M)
abbrev Algebra (M : ℕ) := Bosonize.A08.OscAlgebra M

/-- Positive integer transfer attached to a finite oscillator mode. -/
def weight {M : ℕ} (g : Generator M) : ℕ := g.2.2.val + 1

def energyUpdate {σ : Type*} [DecidableEq σ]
    (species : Bosonize.A06.Orientation → σ)
    {M : ℕ} (g : Generator M) (E : σ → ℤ) : σ → ℤ :=
  Function.update E (species g.2.1)
    (E (species g.2.1) + if g.1 then (weight g : ℤ) else -(weight g : ℤ))

def energyTotal {σ : Type*} (species : Bosonize.A06.Orientation → σ)
    (E : σ → ℤ) : ℤ := E (species .right) + E (species .left)

def nonnegativeEnergies {σ : Type*} (species : Bosonize.A06.Orientation → σ)
    (E : σ → ℤ) : Prop := 0 ≤ E (species .right) ∧ 0 ≤ E (species .left)

/-- A structural right-to-left path certificate. A live annihilation requires
the exact species margin. A first impossible annihilation is recorded as a
zero branch, after which the remaining left prefix acts on zero. -/
def BranchPath {σ : Type*} [DecidableEq σ]
    (h M : ℕ) (Ns : σ → ℤ) (species : Bosonize.A06.Orientation → σ)
    (K : ℕ) : List (Generator M) → (σ → ℤ) → Prop
  | [], E => nonnegativeEnergies species E ∧ energyTotal species E ≤ K
  | g :: tail, E =>
      nonnegativeEnergies species E ∧
        if g.1 then
          energyTotal species (energyUpdate species g E) ≤ K ∧
            BranchPath h M Ns species K tail (energyUpdate species g E)
        else
          (weight g : ℤ) + E (species g.2.1) +
              |Ns (species g.2.1)| ≤ h ∧
            if E (species g.2.1) < (weight g : ℤ) then
              True
            else
              energyTotal species (energyUpdate species g E) ≤ K ∧
                BranchPath h M Ns species K tail (energyUpdate species g E)

/-- The finite set of all branches in the inverse Bogoliubov expansion.
Each generator independently keeps or flips its orientation and creation bit. -/
def flipGenerator {M : ℕ} (g : Generator M) : Generator M :=
  (!g.1, (Bosonize.A07Interactions.oppositeOrientation g.2.1, g.2.2))

def inverseBranches {M : ℕ} : Word M → Finset (Word M)
  | [] => {[]}
  | g :: tail => (inverseBranches tail).biUnion fun branch =>
      {g :: branch, flipGenerator g :: branch}

/-- The explicit path certificate for one ordinary word. -/
def PathCovered {σ : Type*} [Fintype σ] [DecidableEq σ] {M : ℕ}
    (h : ℕ) (Ns : σ → ℤ) (species : Bosonize.A06.Orientation → σ)
    (K : ℕ) (w : Word M) : Prop :=
  species .right ≠ species .left ∧
    BranchPath h M Ns species K w.reverse (fun _ => 0)

/-- Derived uniform sufficient condition for all length-at-most-d words and
all inverse-substitution branches. -/
def UniformMargin {σ : Type*} (h d M : ℕ) (Ns : σ → ℤ) : Prop :=
  ∀ ν, 2 * d * M + |Ns ν| ≤ h

theorem uniform_margin_local_annihilation {σ : Type*}
    (h d M m E : ℕ) (Ns : σ → ℤ) (ν : σ)
    (hd : 0 < d) (hm : m ≤ M) (hE : E ≤ d * M)
    (hU : UniformMargin h d M Ns) :
    (m : ℤ) + E + |Ns ν| ≤ h := by
  have hbound := hU ν
  have hm' : (m : ℤ) ≤ M := by exact_mod_cast hm
  have hE' : (E : ℤ) ≤ d * M := by exact_mod_cast hE
  have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hM : (M : ℤ) ≤ d * M := by nlinarith
  nlinarith

theorem uniform_margin_implies_r2 {σ : Type*} (h d M K : ℕ)
    (Ns : σ → ℤ) (hU : UniformMargin h d M Ns) (hK : K ≤ d * M) :
    ∀ ν, 2 * K + |Ns ν| ≤ h := by
  intro ν
  have := hU ν
  have hK' : (K : ℤ) ≤ ((d * M : ℕ) : ℤ) := by exact_mod_cast hK
  nlinarith

def monomialDegree {M : ℕ} (r : Bosonize.A08.OscMode M →₀ ℕ) : ℕ :=
  r.sum fun _ n => n

/-- Weighted oscillator excitation energy; mode `(ν,i)` contributes `i+1`
per factor, as in A08's derivative and the finite current transfer. -/
def weightedEnergy {M : ℕ} (r : Bosonize.A08.OscMode M →₀ ℕ) : ℕ :=
  r.sum fun mode n => n * (mode.2.val + 1)

def PolynomialDomain {M : ℕ} (K : ℕ) (p : Bosonize.A08.OscPoly M) : Prop :=
  ∀ r ∈ p.support, weightedEnergy r ≤ K

/-- All syntactic branches with nonzero coefficient in the actual free-algebra
expansion at parameter `(c,s)`. -/
def branchCoefficient {M : ℕ} (c s : ℝ) (w v : Word M) : ℂ :=
  ((List.zip w v).map fun p =>
    if p.1 = p.2 then (c : ℂ)
    else if flipGenerator p.1 = p.2 then (s : ℂ) else 0).prod

noncomputable def survivingBranches {M : ℕ} (c s : ℝ) (w : Word M) : Finset (Word M) := by
  classical
  exact (inverseBranches w).filter (fun v => branchCoefficient c s w v ≠ 0)

/-- Exact finite multilinear expansion of the actual A08 inverse substitution.
Its proof includes word-order preservation and all branch coefficients. -/
theorem inverse_expansion_contract {M : ℕ} (c s : ℝ) (w : Word M) :
    ∑ v ∈ inverseBranches w,
      branchCoefficient c s w v • Bosonize.A08.wordElement M v =
        Bosonize.A08.bogoliubovMap M c s
          (Bosonize.A08.wordElement M w) := by
  classical
  have hne (g : Generator M) : g ≠ flipGenerator g := by
    intro he
    have hb := congrArg Prod.fst he
    cases g.1 <;> simp [flipGenerator] at hb
  have hbranches (g : Generator M) (t : Word M) :
      inverseBranches (g :: t) =
        (inverseBranches t).image (List.cons g) ∪
          (inverseBranches t).image (List.cons (flipGenerator g)) := by
    ext v
    simp only [inverseBranches, Finset.mem_biUnion, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_union, Finset.mem_image]
    aesop
  induction w with
  | nil => simp [inverseBranches, branchCoefficient, Bosonize.A08.wordElement]
  | cons g t ih =>
    rw [hbranches, Finset.sum_union]
    · rw [Finset.sum_image (by intro a ha b hb he; exact List.cons.inj he |>.2),
        Finset.sum_image (by intro a ha b hb he; exact List.cons.inj he |>.2)]
      have hkeep (v : Word M) :
          branchCoefficient c s (g::t) (g::v) = (c : ℂ) * branchCoefficient c s t v := by
        simp [branchCoefficient]
      have hflip (v : Word M) :
          branchCoefficient c s (g::t) (flipGenerator g::v) =
            (s : ℂ) * branchCoefficient c s t v := by
        simp [branchCoefficient, hne g]
      simp_rw [hkeep, hflip, Bosonize.A08.wordElement, List.map_cons, List.prod_cons]
      have hterm (a : ℂ) (x y : Algebra M) (b : ℂ) :
          (a * b) • (x * y) = (a • x) * (b • y) := by
        simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_comm]
      simp_rw [hterm]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      change ((c : ℂ) • FreeAlgebra.ι ℂ g) *
          (∑ v ∈ inverseBranches t, branchCoefficient c s t v • Bosonize.A08.wordElement M v) +
        ((s : ℂ) • FreeAlgebra.ι ℂ (flipGenerator g)) *
          (∑ v ∈ inverseBranches t, branchCoefficient c s t v • Bosonize.A08.wordElement M v) = _
      rw [ih]
      simp [Bosonize.A08.wordElement, Bosonize.A08.bogoliubovMap,
        flipGenerator, add_mul]
    · apply Finset.disjoint_left.mpr
      intro v hv hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hw
      exact hne g (List.cons.inj he).1.symm

/-- Actual finite-current substitution on A05's ordinary multispecies Fock
carrier. `true` maps to positive transfer and `false` to negative transfer. -/
noncomputable def theta {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (species : Bosonize.A06.Orientation → σ) :
    Algebra M →ₐ[ℂ] Module.End ℂ (Bosonize.A05.FockSpace σ h) := by
  classical
  exact FreeAlgebra.lift ℂ (fun g =>
    Bosonize.A05.rho h (species g.2.1)
      (if g.1 then (weight g : ℤ) else -(weight g : ℤ)))

/-- The ordered positive-current word attached to one oscillator multi-index.
Parts are grouped by species and then by ascending mode; same-sign currents
commute globally, so this realizes the multi-index without a square root. -/
noncomputable def multiIndexParts {σ : Type*} [Fintype σ] [LinearOrder σ]
    (M : ℕ) (species : Bosonize.A06.Orientation → σ)
    (r : Bosonize.A08.OscMode M →₀ ℕ) : σ → List ℕ := by
  classical
  exact fun ν =>
    (if species .right = ν then
      (List.finRange M).flatMap fun i =>
        List.replicate (r (Bosonize.A06.Orientation.right, i)) (i.val + 1)
     else []) ++
    (if species .left = ν then
      (List.finRange M).flatMap fun i =>
        List.replicate (r (Bosonize.A06.Orientation.left, i)) (i.val + 1)
     else [])

/-- Unnormalized polynomial-to-current-state map. Each coefficient is sent to
the actual A05 current word in the corresponding finite free sea. -/
noncomputable def monomialState {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (Ns : σ → ℤ)
    (species : Bosonize.A06.Orientation → σ)
    (r : Bosonize.A08.OscMode M →₀ ℕ) : Bosonize.A05.FockSpace σ h :=
  Bosonize.A05.wordState h Ns (multiIndexParts M species r)

noncomputable def polynomialState {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (Ns : σ → ℤ)
    (species : Bosonize.A06.Orientation → σ)
    (p : Bosonize.A08.OscPoly M) : Bosonize.A05.FockSpace σ h := by
  classical
  exact ∑ r ∈ p.support,
    (MvPolynomial.lcoeff ℂ r p) • monomialState h M Ns species r

namespace Support
def parts {M : ℕ} (r : Bosonize.A08.OscMode M →₀ ℕ)
    (o : Bosonize.A06.Orientation) : List ℕ :=
  (List.finRange M).flatMap fun i => List.replicate (r (o,i)) (i.val+1)
lemma count_parts {M : ℕ} (r : Bosonize.A08.OscMode M →₀ ℕ)
    (o : Bosonize.A06.Orientation) (m : ℕ) :
    (parts r o).count m = ∑ i : Fin M, if m=i.val+1 then r (o,i) else 0 := by
  unfold parts
  rw [List.count_flatMap]
  simp only [List.finRange, List.map_ofFn, Function.comp_apply, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases he : m = i.val+1
  · simp [← he]
  · have hne : i.val+1 ≠ m := Ne.symm he
    simp [List.count_replicate, he, hne]
lemma count_parts_mode {M : ℕ} (r : Bosonize.A08.OscMode M →₀ ℕ)
    (o : Bosonize.A06.Orientation) (i : Fin M) :
    (parts r o).count (i.val+1) = r (o,i) := by
  rw [count_parts]
  have he (j : Fin M) : (i.val+1=j.val+1) ↔ i=j := by omega
  simp_rw [he]
  simp
lemma parts_pos {M : ℕ} (r : Bosonize.A08.OscMode M →₀ ℕ)
    (o : Bosonize.A06.Orientation) : ∀ n ∈ parts r o, 0<n := by
  intro n hn
  obtain ⟨i, hi, hn⟩ := List.mem_flatMap.mp hn
  obtain ⟨_, rfl⟩ := List.mem_replicate.mp hn
  omega
lemma parts_sum {M : ℕ} (r : Bosonize.A08.OscMode M →₀ ℕ)
    (o : Bosonize.A06.Orientation) :
    (parts r o).sum = ∑ i : Fin M, r (o,i) * (i.val+1) := by
  have hf : ∀ is : List (Fin M),
      (is.flatMap fun i => List.replicate (r (o,i)) (i.val+1)).sum =
      (is.map fun i => r (o,i) * (i.val+1)).sum := by
    intro is
    induction is with
    | nil => simp
    | cons i is ih => simp [ih, Nat.mul_comm]
  unfold parts
  rw [hf]
  simp only [List.finRange, List.map_ofFn, Function.comp_apply, List.sum_ofFn]
lemma parts_zero {M : ℕ} (o : Bosonize.A06.Orientation) :
    parts (0 : Bosonize.A08.OscMode M →₀ ℕ) o = [] := by
  simp [parts]
lemma parts_single_add {M : ℕ} (r : Bosonize.A08.OscMode M →₀ ℕ)
    (a : Bosonize.A08.OscMode M) (o : Bosonize.A06.Orientation) :
    (parts (r+Finsupp.single a 1) o : Multiset ℕ) =
      (parts r o : Multiset ℕ) + if o=a.1 then {a.2.val+1} else 0 := by
  apply Multiset.ext.mpr
  intro m
  simp only [Multiset.count_add, Multiset.coe_count]
  rw [count_parts, count_parts]
  simp only [Finsupp.add_apply]
  have ht (i : Fin M) :
      (if m=i.val+1 then (r (o,i) + Finsupp.single a 1 (o,i)) else 0) =
        (if m=i.val+1 then r (o,i) else 0) +
        (if m=i.val+1 then Finsupp.single a 1 (o,i) else 0) := by
    split_ifs <;> simp
  simp_rw [ht]
  rw [Finset.sum_add_distrib]
  congr 1
  have hs (i : Fin M) :
      (if m=i.val+1 then Finsupp.single a 1 (o,i) else 0) =
        if i=a.2 then (if o=a.1 ∧ m=a.2.val+1 then 1 else 0) else 0 := by
    rcases a with ⟨v,j⟩
    by_cases ho : o=v <;> by_cases hi : i=j <;>
      simp [ho, hi, Prod.mk.injEq]
  simp_rw [hs]
  simp
  split_ifs <;> simp_all
lemma parts_single_sub {M : ℕ} (r : Bosonize.A08.OscMode M →₀ ℕ)
    (a : Bosonize.A08.OscMode M) (hr : 0 < r a)
    (o : Bosonize.A06.Orientation) :
    (parts (r-Finsupp.single a 1) o : Multiset ℕ) =
      if o=a.1 then (parts r o : Multiset ℕ).erase (a.2.val+1)
      else (parts r o : Multiset ℕ) := by
  have hle : Finsupp.single a 1 ≤ r := by
    intro b
    by_cases hb : b=a
    · subst b; simpa using (Nat.succ_le_of_lt hr)
    · simp [hb]
  have hadd := parts_single_add (r-Finsupp.single a 1) a o
  rw [tsub_add_cancel_of_le hle] at hadd
  by_cases ho : o=a.1
  · rw [ite_eq_left ho] at hadd ⊢
    exact (Multiset.add_singleton_eq_iff.mp hadd.symm).2
  · rw [ite_eq_right ho] at hadd ⊢
    simpa using hadd.symm
lemma parts_equal_iff {M : ℕ} (r t : Bosonize.A08.OscMode M →₀ ℕ) :
    (∀ o, (parts r o : Multiset ℕ) = (parts t o : Multiset ℕ)) ↔ r=t := by
  constructor
  · intro h
    ext ⟨o,i⟩
    have hc := congrArg (Multiset.count (i.val+1)) (h o)
    simpa only [Multiset.coe_count, count_parts_mode] using hc
  · rintro rfl; simp
lemma parts_total {M : ℕ} (r : Bosonize.A08.OscMode M →₀ ℕ) :
    (∑ o : Bosonize.A06.Orientation, (parts r o).sum) = weightedEnergy r := by
  simp_rw [parts_sum]
  rw [weightedEnergy, Finsupp.sum_fintype _ _ (by intro mode; simp),
    Fintype.sum_prod_type]
lemma orientation_univ : (Finset.univ : Finset Bosonize.A06.Orientation) =
    {.right, .left} := by ext o; cases o <;> simp
lemma multi_active {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (o : Bosonize.A06.Orientation) :
    multiIndexParts M species r (species o) = parts r o := by
  cases o <;> simp [multiIndexParts, parts, hinj.eq_iff]
lemma multi_other {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (ν : σ)
    (hr : species .right ≠ ν) (hl : species .left ≠ ν) :
    multiIndexParts M species r ν = [] := by
  simp [multiIndexParts, hr, hl]
lemma multi_pos {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (ν : σ) :
    ∀ m ∈ multiIndexParts M species r ν, 0<m := by
  by_cases hr : species .right = ν
  · subst ν; rw [multi_active species hinj]; exact parts_pos r _
  by_cases hl : species .left = ν
  · subst ν; rw [multi_active species hinj]; exact parts_pos r _
  rw [multi_other species r ν hr hl]; simp
lemma multi_bound {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (ν : σ) :
    (multiIndexParts M species r ν).sum ≤ weightedEnergy r := by
  have hb (o : Bosonize.A06.Orientation) : (parts r o).sum ≤ weightedEnergy r := by
    rw [← parts_total]
    exact Finset.single_le_sum (f := fun o => (parts r o).sum) (fun _ _ => Nat.zero_le _) (Finset.mem_univ o)
  by_cases hr : species .right = ν
  · subst ν; rw [multi_active species hinj]; exact hb _
  by_cases hl : species .left = ν
  · subst ν; rw [multi_active species hinj]; exact hb _
  rw [multi_other species r ν hr hl]; exact Nat.zero_le _
lemma multi_equal_iff {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (r t : Bosonize.A08.OscMode M →₀ ℕ) :
    (∀ ν, (multiIndexParts M species r ν : Multiset ℕ) =
      (multiIndexParts M species t ν : Multiset ℕ)) ↔ r=t := by
  constructor
  · intro he
    apply (parts_equal_iff r t).mp
    intro o
    simpa only [multi_active species hinj] using he (species o)
  · rintro rfl; simp
lemma multi_hall_prod {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (r : Bosonize.A08.OscMode M →₀ ℕ) :
    (∏ ν : σ, Bosonize.Ch11.hallFactor
      (multiIndexParts M species r ν : Multiset ℕ)) =
      ∏ o : Bosonize.A06.Orientation, Bosonize.Ch11.hallFactor (parts r o : Multiset ℕ) := by
  have ht (ν : σ) : Bosonize.Ch11.hallFactor
      (multiIndexParts M species r ν : Multiset ℕ) =
      (if species .right=ν then Bosonize.Ch11.hallFactor (parts r .right : Multiset ℕ) else 1) *
      (if species .left=ν then Bosonize.Ch11.hallFactor (parts r .left : Multiset ℕ) else 1) := by
    by_cases hr : species .right=ν
    · subst ν
      simp [multi_active species hinj, hinj.eq_iff]
    by_cases hl : species .left=ν
    · subst ν
      simp [multi_active species hinj, hinj.eq_iff]
    rw [multi_other species r ν hr hl]
    simp [hr, hl, Bosonize.Ch11.hallFactor]
  simp_rw [ht]
  rw [Finset.prod_mul_distrib]
  simp [orientation_univ]
end Support

namespace Support
lemma polynomial_monomial {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (Ns : σ → ℤ) (species : Bosonize.A06.Orientation → σ)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (c : ℂ) :
    polynomialState h M Ns species (MvPolynomial.monomial r c) =
      c • monomialState h M Ns species r := by
  classical
  by_cases hc : c=0
  · simp [hc, polynomialState]
  · simp [polynomialState, MvPolynomial.support_monomial, hc,
      MvPolynomial.lcoeff_apply, MvPolynomial.coeff_monomial]
lemma monomial_zero {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (Ns : σ → ℤ) (species : Bosonize.A06.Orientation → σ) :
    monomialState h M Ns species 0 = Bosonize.A05.groundKet h Ns := by
  classical
  have hz : multiIndexParts M species (0 : Bosonize.A08.OscMode M →₀ ℕ) = fun _ => [] := by
    funext ν
    simp only [multiIndexParts, Finsupp.zero_apply, List.replicate_zero]
    simp [List.flatMap_eq_nil_iff]
  rw [monomialState, hz]
  simp [Bosonize.A05.wordState, Bosonize.A05.creatorWord]
lemma multi_add {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (a : Bosonize.A08.OscMode M) (ν : σ) :
    (multiIndexParts M species (r+Finsupp.single a 1) ν : Multiset ℕ) =
      (multiIndexParts M species r ν : Multiset ℕ) +
        if ν=species a.1 then {a.2.val+1} else 0 := by
  classical
  by_cases hr : species .right=ν
  · subst ν
    rw [multi_active species hinj, multi_active species hinj, parts_single_add]
    simp only [hinj.eq_iff]
  by_cases hl : species .left=ν
  · subst ν
    rw [multi_active species hinj, multi_active species hinj, parts_single_add]
    simp only [hinj.eq_iff]
  rw [multi_other species _ ν hr hl, multi_other species _ ν hr hl]
  have he : ν ≠ species a.1 := by cases a.1 <;> exact Ne.symm (by assumption)
  simp [he]
lemma multi_sub {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (a : Bosonize.A08.OscMode M)
    (hr : 0<r a) (ν : σ) :
    (multiIndexParts M species (r-Finsupp.single a 1) ν : Multiset ℕ) =
        if ν=species a.1 then (multiIndexParts M species r ν : Multiset ℕ).erase (a.2.val+1)
        else (multiIndexParts M species r ν : Multiset ℕ) := by
  classical
  by_cases hR : species .right=ν
  · subst ν
    rw [multi_active species hinj, multi_active species hinj, parts_single_sub r a hr]
    simp only [hinj.eq_iff]
  by_cases hL : species .left=ν
  · subst ν
    rw [multi_active species hinj, multi_active species hinj, parts_single_sub r a hr]
    simp only [hinj.eq_iff]
  rw [multi_other species _ ν hR hL, multi_other species _ ν hR hL]
  simp
lemma tensor_update_smul {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h : ℕ) (vs : σ → Bosonize.Ch07.FockSpace h) (ν : σ)
    (x : Bosonize.Ch07.FockSpace h) (c : ℂ) :
    Bosonize.A05.tensorVector h (Function.update vs ν (c • x)) =
      c • Bosonize.A05.tensorVector h (Function.update vs ν x) := by
  classical
  let : DecidableEq (Bosonize.A05.Mode σ h) := (Bosonize.A05.speciesOrder h).toDecidableEq
  apply (Bosonize.A02.coordinates (Bosonize.A05.Mode σ h)).injective
  funext S
  simp only [Bosonize.A05.tensorVector, map_smul, LinearEquiv.apply_symm_apply,
    Pi.smul_apply]
  have hf (y : Bosonize.Ch07.FockSpace h) :
      (∏ η, Function.update vs ν y η (Bosonize.Ch07.speciesConfiguration h S η)) =
        y (Bosonize.Ch07.speciesConfiguration h S ν) *
          ∏ η ∈ (Finset.univ : Finset σ).erase ν, vs η (Bosonize.Ch07.speciesConfiguration h S η) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ν)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro η hη
    rw [Function.update_of_ne (Finset.mem_erase.mp hη).1]
  rw [hf, hf]
  simp [PiLp.smul_apply, smul_eq_mul, mul_assoc]
lemma mono_creation {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (Ns : σ → ℤ) (hN : Bosonize.A05.admissible h Ns)
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (a : Bosonize.A08.OscMode M) :
    Bosonize.A05.rho h (species a.1) (a.2.val+1 : ℕ)
      (monomialState h M Ns species r) =
      monomialState h M Ns species (r+Finsupp.single a 1) := by
  classical
  rw [monomialState, monomialState, Bosonize.A05.word_tensor h Ns hN,
    Bosonize.A05.word_tensor h Ns hN, Bosonize.A05.rho_tensor]
  congr 1
  funext ν
  by_cases he : ν=species a.1
  · subst ν
    simp only [Function.update_self]
    rw [← Bosonize.Ch11.word_state_cons]
    have hp : ((a.2.val+1) :: multiIndexParts M species r (species a.1)).Perm
        (multiIndexParts M species (r+Finsupp.single a 1) (species a.1)) := by
      apply Multiset.coe_eq_coe.mp
      rw [multi_add species hinj]
      simp [add_comm]
    exact congrArg (fun op => op (Bosonize.Ch07.groundKet h (Ns (species a.1)) (hN _)))
      (Bosonize.Ch11.creator_word_perm h _ _ hp)
  · rw [Function.update_of_ne he]
    have hp : (multiIndexParts M species r ν).Perm
        (multiIndexParts M species (r+Finsupp.single a 1) ν) := by
      apply Multiset.coe_eq_coe.mp
      rw [multi_add species hinj]
      simp [he]
    exact congrArg (fun op => op (Bosonize.Ch07.groundKet h (Ns ν) (hN _)))
      (Bosonize.Ch11.creator_word_perm h _ _ hp)
lemma mono_lowering {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M K : ℕ) (Ns : σ → ℤ) (hh : 0<h)
    (hN : Bosonize.A05.admissible h Ns)
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (hR2 : ∀ ν, 2*K+|Ns ν| ≤ h)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (hr : weightedEnergy r ≤ K)
    (a : Bosonize.A08.OscMode M) :
    Bosonize.A05.rho h (species a.1) (-(a.2.val+1 : ℕ) : ℤ)
      (monomialState h M Ns species r) =
      ((a.2.val+1 : ℕ) * r a : ℂ) •
        monomialState h M Ns species (r-Finsupp.single a 1) := by
  classical
  let ν := species a.1
  let m := a.2.val+1
  let ps := multiIndexParts M species r
  have hc : (ps ν).count m = r a := by
    dsimp [ps, ν, m]
    rw [multi_active species hinj]
    exact count_parts_mode r a.1 a.2
  have hE : (ps ν).sum ≤ K := (multi_bound species hinj r ν).trans hr
  have hlower : Bosonize.Ch09.rho h (-(m : ℤ))
      (Bosonize.Ch11.wordState h (Ns ν) (hN ν) (ps ν)) =
      ((m * r a : ℕ) : ℂ) •
        Bosonize.Ch11.wordState h (Ns ν) (hN ν) ((ps ν).erase m) := by
    by_cases hm : m ≤ K
    · have ht := Bosonize.Ch11.lowering_through_word_erase h hh (Ns ν) (hN ν)
        K m (by dsimp [m]; omega) hm (ps ν)
        (multi_pos species hinj r ν) hE (hR2 ν)
      rw [hc] at ht
      simpa only [← Nat.cast_smul_eq_nsmul ℂ] using ht
    · have hzero := Bosonize.Ch09.rho_lowering_budget_zero h hh (m : ℤ) (Ns ν)
        ((ps ν).sum : ℤ) (by omega)
        _ (Bosonize.Ch11.word_state_mem_budget h hh (Ns ν) (hN ν) (ps ν)
          (ps ν).sum (le_refl _))
      have hcount : r a = 0 := by
        by_contra hn
        have hmem : m ∈ ps ν := List.count_pos_iff.mp (by rw [hc]; omega)
        have hle : m ≤ (ps ν).sum := List.single_le_sum (fun _ _ => Nat.zero_le _) m hmem
        omega
      simp [hzero, hcount]
  rw [monomialState, Bosonize.A05.word_tensor h Ns hN, Bosonize.A05.rho_tensor]
  change Bosonize.A05.tensorVector h
    (Function.update (fun η => Bosonize.Ch11.wordState h (Ns η) (hN η) (ps η)) ν
      (Bosonize.Ch09.rho h (-(m : ℤ))
        (Bosonize.Ch11.wordState h (Ns ν) (hN ν) (ps ν)))) = _
  rw [hlower, tensor_update_smul]
  by_cases hra : r a=0
  · simp [hra]
  · simp only [Nat.cast_mul]
    apply congrArg (fun v => ((m:ℂ) * (r a:ℂ)) • v)
    rw [monomialState, Bosonize.A05.word_tensor h Ns hN]
    congr 1
    funext η
    by_cases he : η=ν
    · subst η
      simp only [Function.update_self]
      have hp : ((ps ν).erase m).Perm
          (multiIndexParts M species (r-Finsupp.single a 1) ν) := by
        apply Multiset.coe_eq_coe.mp
        rw [multi_sub species hinj r a (by omega)]
        simp [ν, m, ps, Multiset.coe_erase]
      exact congrArg (fun op => op (Bosonize.Ch07.groundKet h (Ns ν) (hN ν)))
        (Bosonize.Ch11.creator_word_perm h _ _ hp)
    · rw [Function.update_of_ne he]
      have hp : (ps η).Perm (multiIndexParts M species (r-Finsupp.single a 1) η) := by
        apply Multiset.coe_eq_coe.mp
        rw [multi_sub species hinj r a (by omega)]
        simp [show η ≠ species a.1 from he, ps]
      exact congrArg (fun op => op (Bosonize.Ch07.groundKet h (Ns η) (hN η)))
        (Bosonize.Ch11.creator_word_perm h _ _ hp)
noncomputable def monoE {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ) (r : Bosonize.A08.OscMode M →₀ ℕ) : σ → ℤ :=
  fun ν => (multiIndexParts M species r ν).sum
lemma monoE_total {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (r : Bosonize.A08.OscMode M →₀ ℕ) :
    energyTotal species (monoE species r) = weightedEnergy r := by
  have h : (parts r .right).sum + (parts r .left).sum = weightedEnergy r := by
    have ht := parts_total r
    simpa [orientation_univ] using ht
  simp only [energyTotal, monoE, multi_active species hinj]
  exact_mod_cast h
lemma monoE_zero {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ) :
    monoE species (0 : Bosonize.A08.OscMode M →₀ ℕ) = fun _ => 0 := by
  have hz : multiIndexParts M species (0 : Bosonize.A08.OscMode M →₀ ℕ) = fun _ => [] := by
    funext ν
    simp only [multiIndexParts, Finsupp.zero_apply, List.replicate_zero]
    simp [List.flatMap_eq_nil_iff]
  funext ν
  simp only [monoE, hz, List.sum_nil, Nat.cast_zero]
lemma monoE_add {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (a : Bosonize.A08.OscMode M) :
    monoE species (r+Finsupp.single a 1) =
      energyUpdate species (true,a) (monoE species r) := by
  classical
  funext ν
  have he := congrArg Multiset.sum (multi_add species hinj r a ν)
  simp only [Multiset.sum_add, Multiset.sum_coe] at he
  by_cases hν : ν=species a.1
  · subst ν
    simp only [ite_true, Multiset.sum_singleton] at he
    simp only [energyUpdate, Function.update_self, ↓reduceIte, weight, monoE]
    exact_mod_cast he
  · simp only [ite_eq_right hν, Multiset.sum_zero, add_zero] at he
    simp only [energyUpdate, Function.update_of_ne hν, monoE]
    exact_mod_cast he
lemma monoE_sub {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (a : Bosonize.A08.OscMode M)
    (hr : 0<r a) :
    monoE species (r-Finsupp.single a 1) =
      energyUpdate species (false,a) (monoE species r) := by
  classical
  have hle : Finsupp.single a 1 ≤ r := by
    intro b
    by_cases hb : b=a
    · subst b; simpa using Nat.succ_le_of_lt hr
    · simp [hb]
  have he := monoE_add species hinj (r-Finsupp.single a 1) a
  rw [tsub_add_cancel_of_le hle] at he
  funext ν
  have hv := congrArg (fun E => E ν) he
  by_cases hν : ν=species a.1
  · subst ν
    simp [energyUpdate, weight] at hv ⊢
    omega
  · simpa only [energyUpdate, Function.update_of_ne hν] using hv.symm
lemma monoE_mode_le {σ : Type*} [Fintype σ] [LinearOrder σ] {M : ℕ}
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (a : Bosonize.A08.OscMode M)
    (hr : 0<r a) : (a.2.val+1 : ℕ) ≤ monoE species r (species a.1) := by
  have hc : (parts r a.1).count (a.2.val+1) > 0 := by rw [count_parts_mode]; exact hr
  have hm := List.count_pos_iff.mp hc
  have he := List.single_le_sum (fun _ _ => Nat.zero_le _) (a.2.val+1) hm
  simp only [monoE, multi_active species hinj]
  exact_mod_cast he
end Support
namespace Support
lemma osc_create_monomial (M : ℕ) (a : Bosonize.A08.OscMode M)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (c : ℂ) :
    Bosonize.A08.oscRep M (FreeAlgebra.ι ℂ (true,a)) (MvPolynomial.monomial r c) =
      MvPolynomial.monomial (r+Finsupp.single a 1) c := by
  classical
  simp only [Bosonize.A08.oscRep, FreeAlgebra.lift_ι_apply, ↓reduceIte,
    Bosonize.A08.oscCreation, LinearMap.mulLeft_apply]
  rw [add_comm r, MvPolynomial.monomial_single_add, pow_one]
lemma osc_lower_monomial (M : ℕ) (a : Bosonize.A08.OscMode M)
    (r : Bosonize.A08.OscMode M →₀ ℕ) (c : ℂ) :
    Bosonize.A08.oscRep M (FreeAlgebra.ι ℂ (false,a)) (MvPolynomial.monomial r c) =
      MvPolynomial.monomial (r-Finsupp.single a 1) ((a.2.val+1 : ℕ) * (c * r a)) := by
  classical
  simp [Bosonize.A08.oscRep, Bosonize.A08.oscAnnihilation,
    Bosonize.A08.oscWeight, MvPolynomial.smul_monomial]
lemma execution_action {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M K : ℕ) (Ns : σ → ℤ) (hh : 0<h)
    (hN : Bosonize.A05.admissible h Ns)
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (hR2 : ∀ ν, 2*K+|Ns ν| ≤ h)
    (xs : Word M) (r : Bosonize.A08.OscMode M →₀ ℕ) (c : ℂ)
    (hr : weightedEnergy r ≤ K)
    (hpath : BranchPath h M Ns species K xs (monoE species r)) :
    theta h M species (Bosonize.A08.wordElement M xs.reverse)
      (c • monomialState h M Ns species r) =
      polynomialState h M Ns species
        (Bosonize.A08.oscRep M (Bosonize.A08.wordElement M xs.reverse)
          (MvPolynomial.monomial r c)) := by
  classical
  have hw (g : Generator M) (t : Word M) :
      Bosonize.A08.wordElement M (g::t).reverse =
        Bosonize.A08.wordElement M t.reverse * FreeAlgebra.ι ℂ g := by
    simp [Bosonize.A08.wordElement]
  induction xs generalizing r c with
  | nil => simp [Bosonize.A08.wordElement, polynomial_monomial]
  | cons g xs ih =>
    rw [hw, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    rcases g with ⟨b,a⟩
    cases b with
    | false =>
      rw [osc_lower_monomial]
      have hc : theta h M species (FreeAlgebra.ι ℂ (false,a))
          (c • monomialState h M Ns species r) =
          ((a.2.val+1 : ℕ) * (c * r a) : ℂ) •
            monomialState h M Ns species (r-Finsupp.single a 1) := by
        simp only [theta, FreeAlgebra.lift_ι_apply, Bool.false_eq_true, ↓reduceIte, weight]
        rw [map_smul, mono_lowering h M K Ns hh hN species hinj hR2 r hr a, smul_smul]
        congr 1
        ring
      rw [hc]
      by_cases hra : r a=0
      · simp [hra, polynomialState]
      · have hmode := monoE_mode_le species hinj r a (by omega)
        have ht : BranchPath h M Ns species K xs
            (monoE species (r-Finsupp.single a 1)) ∧
            weightedEnergy (r-Finsupp.single a 1) ≤ K := by
          simp only [BranchPath, Bool.false_eq_true, ↓reduceIte] at hpath
          have hn : ¬ monoE species r (species a.1) < (weight (false,a) : ℤ) := by
            simpa only [weight] using not_lt_of_ge hmode
          have hs := (ite_eq_right hn ▸ hpath.2.2)
          rw [← monoE_sub species hinj r a (by omega)] at hs
          exact ⟨hs.2, by rw [monoE_total species hinj] at hs; exact_mod_cast hs.1⟩
        exact ih _ _ ht.2 ht.1
    | true =>
      rw [osc_create_monomial]
      have hc : theta h M species (FreeAlgebra.ι ℂ (true,a))
          (c • monomialState h M Ns species r) =
          c • monomialState h M Ns species (r+Finsupp.single a 1) := by
        simp only [theta, FreeAlgebra.lift_ι_apply, ↓reduceIte, weight]
        rw [map_smul, mono_creation h M Ns hN species hinj]
      rw [hc]
      simp only [BranchPath, ↓reduceIte] at hpath
      have hs := hpath.2
      rw [← monoE_add species hinj r a] at hs
      exact ih _ _ (by rw [monoE_total species hinj] at hs; exact_mod_cast hs.1) hs.2
end Support

namespace Support
lemma vacuum_monomial {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (Ns : σ → ℤ) (hh : 0<h)
    (hN : Bosonize.A05.admissible h Ns)
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (r : Bosonize.A08.OscMode M →₀ ℕ) :
    inner ℂ (Bosonize.A05.groundKet h Ns) (monomialState h M Ns species r) =
      if r=0 then 1 else 0 := by
  classical
  by_cases he : r=0
  · subst r
    rw [monomial_zero]
    change inner ℂ (Bosonize.A02.ket (Bosonize.A05.groundConfiguration h Ns))
      (Bosonize.A02.ket (Bosonize.A05.groundConfiguration h Ns)) = 1
    simpa only [ite_true] using Bosonize.A02.ket_inner
      (Bosonize.A05.groundConfiguration h Ns) (Bosonize.A05.groundConfiguration h Ns)
  · rw [ite_eq_right he, ← monomial_zero h M Ns species,
      monomialState, monomialState, Bosonize.A05.word_tensor h Ns hN,
      Bosonize.A05.word_tensor h Ns hN, Bosonize.A05.tensor_inner]
    obtain ⟨a,ha⟩ := Finsupp.ne_iff.mp he
    apply Finset.prod_eq_zero (Finset.mem_univ (species a.1))
    rw [multi_active species hinj, parts_zero, Bosonize.Ch11.word_state_nil,
      multi_active species hinj]
    apply Bosonize.Ch11.ground_inner_word_zero h hh (Ns (species a.1)) (hN _)
    have hc : 0 < (parts r a.1).count (a.2.val+1) := by rw [count_parts_mode]; simpa using Nat.pos_of_ne_zero ha
    have hm := List.count_pos_iff.mp hc
    have he := List.single_le_sum (fun _ _ => Nat.zero_le _) (a.2.val+1) hm
    omega
lemma vacuum_polynomial {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (Ns : σ → ℤ) (hh : 0<h)
    (hN : Bosonize.A05.admissible h Ns)
    (species : Bosonize.A06.Orientation → σ) (hinj : Function.Injective species)
    (p : Bosonize.A08.OscPoly M) :
    inner ℂ (Bosonize.A05.groundKet h Ns) (polynomialState h M Ns species p) =
      MvPolynomial.lcoeff ℂ 0 p := by
  classical
  unfold polynomialState
  simp only [inner_sum, inner_smul_right, vacuum_monomial h M Ns hh hN species hinj]
  by_cases hz : 0 ∈ p.support
  · simp [hz]
  · have hc := MvPolynomial.notMem_support_iff.mp hz
    simp [hz, hc]
end Support

open Support

/-- The polynomial map's explicit truncated range: the span of current
partition states whose oscillator modes lie below the cutoff. -/
noncomputable def cutoffRange {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M K : ℕ) (Ns : σ → ℤ)
    (species : Bosonize.A06.Orientation → σ) :
    Submodule ℂ (Bosonize.A05.FockSpace σ h) :=
  Submodule.span ℂ (Set.range fun r : {r : Bosonize.A08.OscMode M →₀ ℕ // weightedEnergy r ≤ K} =>
    monomialState h M Ns species r.1)

theorem polynomial_state_range_contract {σ : Type*} [Fintype σ] [LinearOrder σ]
    {M h K : ℕ} (Ns : σ → ℤ)
    (species : Bosonize.A06.Orientation → σ)
    (p : Bosonize.A08.OscPoly M) (hp : PolynomialDomain K p) :
    polynomialState h M Ns species p ∈ cutoffRange h M K Ns species := by
  classical
  unfold polynomialState cutoffRange
  apply Submodule.sum_mem
  intro r hr
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range.mpr ⟨⟨r, hp r hr⟩, rfl⟩)

/-- Weighted monomial Gram factor agrees with the partition/Haldane norm. -/
theorem oscillator_monomial_norm_eq_haldane_contract {M : ℕ}
    (r : Bosonize.A08.OscMode M →₀ ℕ) :
    Bosonize.A08.oscMonomialNorm r =
      ∏ ν : Bosonize.A06.Orientation,
        Bosonize.Ch11.hallFactor
          (((List.finRange M).flatMap fun i =>
            List.replicate (r (ν, i)) (i.val + 1) : List ℕ) : Multiset ℕ) := by
  classical
  have hall (ν : Bosonize.A06.Orientation) :
      Bosonize.Ch11.hallFactor
          (((List.finRange M).flatMap fun i =>
            List.replicate (r (ν, i)) (i.val + 1) : List ℕ) : Multiset ℕ) =
        ∏ i : Fin M, (i.val+1) ^ r (ν,i) * (r (ν,i)).factorial := by
    let parts := (List.finRange M).flatMap fun i =>
      List.replicate (r (ν,i)) (i.val+1)
    have hc (m : ℕ) : parts.count m =
        ∑ i : Fin M, if m=i.val+1 then r (ν,i) else 0 := by
      dsimp [parts]
      rw [List.count_flatMap]
      simp only [List.finRange, List.map_ofFn, Function.comp_apply, List.sum_ofFn]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases he : m = i.val+1
      · simp [← he]
      · have hne : i.val+1 ≠ m := Ne.symm he
        simp [List.count_replicate, he, hne]
    have hci (i : Fin M) : parts.count (i.val+1) = r (ν,i) := by
      rw [hc]
      have he (j : Fin M) : (i.val+1=j.val+1) ↔ i=j := by omega
      simp_rw [he]
      simp
    have hs : parts.toFinset ⊆ (Finset.univ.image fun i : Fin M => i.val+1) := by
      intro m hm
      have hm' : m ∈ parts := by simpa using hm
      obtain ⟨i, hi, hm⟩ := List.mem_flatMap.mp hm'
      have hm'' : m=i.val+1 := (List.mem_replicate.mp hm).2
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hm''.symm⟩
    change Bosonize.Ch11.hallFactor (parts : Multiset ℕ) = _
    simp only [Bosonize.Ch11.hallFactor, Multiset.coe_count]
    change (∏ m ∈ parts.toFinset, m ^ parts.count m * (parts.count m).factorial) = _
    rw [Finset.prod_subset hs]
    · rw [Finset.prod_image (by intro a ha b hb he; apply Fin.ext; change a.val+1=b.val+1 at he; omega)]
      simp_rw [hci]
    · intro m hm hn
      have hzero : parts.count m = 0 := by
        exact List.count_eq_zero.mpr (by simpa using hn)
      simp [hzero]
  simp_rw [hall]
  rw [Bosonize.A08.oscMonomialNorm,
    Finsupp.prod_fintype _ _ (by intro mode; simp), Fintype.prod_prod_type]
  rfl

/-- On the explicit weighted-energy-`K` polynomial domain, the unnormalized state map
has the exact weighted oscillator Gram form. -/
theorem polynomial_state_gram_contract {σ : Type*} [Fintype σ] [LinearOrder σ]
    {M h K : ℕ} (Ns : σ → ℤ)
    (species : Bosonize.A06.Orientation → σ)
    (hh : 0 < h)
    (hinj : Function.Injective species)
    (hN : Bosonize.A05.admissible h Ns)
    (hR2 : ∀ ν, 2 * K + |Ns ν| ≤ h)
    (p q : Bosonize.A08.OscPoly M)
    (hp : PolynomialDomain K p) (hq : PolynomialDomain K q) :
    inner ℂ (polynomialState h M Ns species p)
      (polynomialState h M Ns species q) =
      Bosonize.A08.oscPairing M p q := by
  classical
  have hm (r t : Bosonize.A08.OscMode M →₀ ℕ)
      (hr : weightedEnergy r ≤ K) (ht : weightedEnergy t ≤ K) :
      inner ℂ (monomialState h M Ns species r) (monomialState h M Ns species t) =
        if r=t then (Bosonize.A08.oscMonomialNorm r : ℂ) else 0 := by
    rw [monomialState, monomialState, Bosonize.A05.word_tensor h Ns hN,
      Bosonize.A05.word_tensor h Ns hN, Bosonize.A05.tensor_inner]
    have hg (ν : σ) := Bosonize.Ch11.word_gram h hh (Ns ν) (hN ν) K
      (multiIndexParts M species r ν) (multiIndexParts M species t ν)
      (multi_pos species hinj r ν) (multi_pos species hinj t ν)
      ((multi_bound species hinj r ν).trans hr)
      ((multi_bound species hinj t ν).trans ht) (hR2 ν)
    simp_rw [hg]
    by_cases he : r=t
    · subst t
      simp only [ite_true]
      rw [← Nat.cast_prod, multi_hall_prod species hinj]
      exact congrArg (fun n : ℕ => (n : ℂ))
        (oscillator_monomial_norm_eq_haldane_contract r).symm
    · rw [ite_eq_right he]
      have hn : ¬ ∀ ν, (multiIndexParts M species r ν : Multiset ℕ) =
          (multiIndexParts M species t ν : Multiset ℕ) := by
        simpa only [multi_equal_iff species hinj] using he
      push Not at hn
      obtain ⟨ν,hν⟩ := hn
      exact Finset.prod_eq_zero (Finset.mem_univ ν) (ite_eq_right hν)
  unfold polynomialState Bosonize.A08.oscPairing
  rw [sum_inner]
  simp only [inner_smul_left, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro r hr
  have hs : (∑ t ∈ q.support, MvPolynomial.lcoeff ℂ t q *
      inner ℂ (monomialState h M Ns species r) (monomialState h M Ns species t)) =
      (Bosonize.A08.oscMonomialNorm r : ℂ) * MvPolynomial.lcoeff ℂ r q := by
    have hterm (t) (ht : t ∈ q.support) := hm r t (hp r hr) (hq t ht)
    trans ∑ t ∈ q.support, MvPolynomial.lcoeff ℂ t q *
      (if r=t then (Bosonize.A08.oscMonomialNorm r : ℂ) else 0)
    · exact Finset.sum_congr rfl (fun t ht => by rw [hterm t ht])
    · by_cases hmem : r ∈ q.support
      · simp [hmem, mul_comm]
      · have hz : MvPolynomial.lcoeff ℂ r q = 0 := MvPolynomial.notMem_support_iff.mp hmem
        simp [hmem, hz]
  calc
    _ = star (MvPolynomial.lcoeff ℂ r p) *
        (∑ t ∈ q.support, MvPolynomial.lcoeff ℂ t q *
          inner ℂ (monomialState h M Ns species r) (monomialState h M Ns species t)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      change _ * (star _ * _) = star _ * (_ * _)
      ring
    _ = _ := by rw [hs]; ring

/-- The map lands in the actual fixed-charge total-energy budget. -/
theorem polynomial_state_budget_contract {σ : Type*} [Fintype σ] [LinearOrder σ]
    {M h K : ℕ} (Ns : σ → ℤ)
    (species : Bosonize.A06.Orientation → σ)
    (hh : 0 < h) (hN : Bosonize.A05.admissible h Ns)
    (p : Bosonize.A08.OscPoly M) (hp : PolynomialDomain K p) :
    polynomialState h M Ns species p ∈ Bosonize.A05.jointBudget h Ns K := by
  classical
  have list_rep_energy (r : Bosonize.A08.OscMode M →₀ ℕ)
      (o : Bosonize.A06.Orientation) :
      (List.flatMap (fun i : Fin M =>
        List.replicate (r (o,i)) (i.val+1)) (List.finRange M)).sum =
      ((List.finRange M).map (fun i => r (o,i) * (i.val+1))).sum := by
    have hf : ∀ is : List (Fin M),
        (List.flatMap (fun i => List.replicate (r (o,i)) (i.val+1)) is).sum =
          (is.map (fun i => r (o,i) * (i.val+1))).sum := by
      intro is
      induction is with
      | nil => simp
      | cons i is ih =>
        simp only [List.flatMap_cons, List.sum_append, List.sum_replicate,
          List.map_cons, List.sum_cons]
        rw [ih]
        simp [Nat.mul_comm]
    exact hf _
  have parts_energy (r : Bosonize.A08.OscMode M →₀ ℕ) :
      (∑ ν : σ, (multiIndexParts M species r ν).sum) = weightedEnergy r := by
    have hterm (a : σ) (l : List ℕ) :
        (∑ ν : σ, (if a = ν then l else []).sum) = l.sum := by
      have ht (ν : σ) : (if a = ν then l else []).sum = if a = ν then l.sum else 0 := by
        by_cases h : a = ν <;> simp [h]
      simp_rw [ht]
      simp
    rw [weightedEnergy, Finsupp.sum_fintype r
      (fun mode n => n * (mode.2.val+1)) (by simp)]
    simp only [multiIndexParts, List.sum_append, Finset.sum_add_distrib]
    rw [hterm (species .right) (List.flatMap _ (List.finRange M))]
    rw [hterm (species .left) (List.flatMap _ (List.finRange M))]
    rw [list_rep_energy, list_rep_energy]
    simp only [List.finRange, List.map_ofFn, Function.comp_apply, List.sum_ofFn]
    rw [Fintype.sum_prod_type]
    let e : Bosonize.A06.Orientation ≃ Bool := {
      toFun := fun o => match o with | .right => false | .left => true
      invFun := fun b => match b with | false => .right | true => .left
      left_inv := by intro o; cases o <;> rfl
      right_inv := by intro b; cases b <;> rfl }
    have hequiv :
        (∑ o : Bosonize.A06.Orientation, ∑ i : Fin M, r (o,i) * (i.val+1)) =
          (∑ i : Fin M, r (.right,i) * (i.val+1)) +
            (∑ i : Fin M, r (.left,i) * (i.val+1)) := by
      rw [Fintype.sum_equiv e
        (fun o => ∑ i : Fin M, r (o,i) * (i.val+1))
        (fun b => ∑ i : Fin M, r (e.symm b,i) * (i.val+1))
        (by intro o; cases o <;> rfl)]
      simp [e]
      ac_rfl
    rw [← hequiv]
  have hmono (r : Bosonize.A08.OscMode M →₀ ℕ) (hr : weightedEnergy r ≤ K) :
      monomialState h M Ns species r ∈ Bosonize.A05.jointBudget h Ns K := by
    unfold monomialState
    apply Bosonize.A05.word_mem_budget h hh Ns hN (multiIndexParts M species r) K
    rw [parts_energy r]
    exact hr
  unfold polynomialState
  apply Submodule.sum_mem
  intro r hr
  apply Submodule.smul_mem
  exact hmono r (hp r hr)

/-- Finite path intertwining under explicit branch coverage and the actual
sector/budget margin. -/
theorem covered_word_action_contract {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (Ns : σ → ℤ)
    (species : Bosonize.A06.Orientation → σ) (w : Word M)
    (hh : 0 < h)
    (hN : Bosonize.A05.admissible h Ns)
    (K : ℕ) (hR2 : ∀ ν, 2 * K + |Ns ν| ≤ h)
    (hinj : Function.Injective species) (hPath : PathCovered h Ns species K w) :
    theta (σ := σ) h M species (Bosonize.A08.wordElement M w)
      (Bosonize.A05.groundKet h Ns) =
      polynomialState h M Ns species
        (Bosonize.A08.oscRep M (Bosonize.A08.wordElement M w) 1) := by
  have he := execution_action h M K Ns hh hN species hinj hR2 w.reverse 0 1
    (by simp [weightedEnergy]) (by simpa only [monoE_zero] using hPath.2)
  simpa only [List.reverse_reverse, monomial_zero, one_smul,
    MvPolynomial.monomial_zero', map_one] using he

/-- Selected finite sea matrix element equals A08's unsqueezed vacuum
functional on every covered word. -/
theorem covered_word_moment_contract {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (Ns : σ → ℤ)
    (species : Bosonize.A06.Orientation → σ) (w : Word M)
    (hh : 0 < h) (hN : Bosonize.A05.admissible h Ns)
    (K : ℕ) (hR2 : ∀ ν, 2 * K + |Ns ν| ≤ h)
    (hinj : Function.Injective species) (hPath : PathCovered h Ns species K w) :
    inner ℂ (Bosonize.A05.groundKet h Ns)
      (theta (σ := σ) h M species (Bosonize.A08.wordElement M w)
        (Bosonize.A05.groundKet h Ns)) =
      Bosonize.A08.omega0 M (Bosonize.A08.wordElement M w) := by
  rw [covered_word_action_contract h M Ns species w hh hN K hR2 hinj hPath,
    vacuum_polynomial h M Ns hh hN species hinj]
  rfl

/-- Bogoliubov-dressed comparison: branch hypotheses cover the complete
inverse expansion, so the result is omegaP on the original displayed word. -/
theorem covered_dressed_moment_contract {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (Ns : σ → ℤ) (hp : Bosonize.Ch18.HyperbolicPair)
    (species : Bosonize.A06.Orientation → σ) (w : Word M)
    (hh : 0 < h) (hN : Bosonize.A05.admissible h Ns)
    (K : ℕ) (hR2 : ∀ ν, 2 * K + |Ns ν| ≤ h)
    (hinj : Function.Injective species)
    (hPath : ∀ v ∈ survivingBranches hp.c (-hp.s) w,
      PathCovered h Ns species K v) :
    inner ℂ (Bosonize.A05.groundKet h Ns)
      (theta (σ := σ) h M species
        ((Bosonize.A08.bogoliubovMap M hp.c (-hp.s)
          (Bosonize.A08.wordElement M w)))
        (Bosonize.A05.groundKet h Ns)) =
      Bosonize.A08.omegaP M hp (Bosonize.A08.wordElement M w) := by
  classical
  rw [← inverse_expansion_contract]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    inner_sum, inner_smul_right]
  change _ = Bosonize.A08.omega0 M
    (Bosonize.A08.bogoliubovMap M hp.c (-hp.s) (Bosonize.A08.wordElement M w))
  rw [← inverse_expansion_contract, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hc : branchCoefficient hp.c (-hp.s) w v=0
  · simp [hc]
  · rw [covered_word_moment_contract h M Ns species v hh hN K hR2 hinj
      (hPath v (Finset.mem_filter.mpr ⟨hv,hc⟩))]

lemma branch_bounded {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M K : ℕ) (Ns : σ → ℤ) (species : Bosonize.A06.Orientation → σ)
    (hne : species .right ≠ species .left)
    (hR2 : ∀ ν, 2*K+|Ns ν| ≤ h)
    (xs : Word M) (E : σ → ℤ) (hE : nonnegativeEnergies species E)
    (hbound : energyTotal species E + xs.length * (M : ℤ) ≤ K) :
    BranchPath h M Ns species K xs E := by
  induction xs generalizing E with
  | nil => exact ⟨hE, by simpa using hbound⟩
  | cons g xs ih =>
    rcases g with ⟨b,o,i⟩
    have hm : (i.val+1 : ℤ) ≤ M := by exact_mod_cast i.isLt
    have htot : 0 ≤ energyTotal species E := add_nonneg hE.1 hE.2
    have hν : E (species o) ≤ energyTotal species E := by
      cases o <;> dsimp [energyTotal] <;> have hEr := hE.1 <;> have hEl := hE.2 <;> omega
    have hM : (M : ℤ) ≤ K := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hbound
      have hp : (0 : ℤ) ≤ xs.length * (M : ℤ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      omega
    have hb : energyTotal species E + (xs.length : ℤ) * M + M ≤ K := by
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using hbound
    have hEtot : energyTotal species E ≤ K := by
      have hp : (0 : ℤ) ≤ xs.length * (M : ℤ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      omega
    change nonnegativeEnergies species E ∧ _
    refine ⟨hE, ?_⟩
    cases b with
    | true =>
      change energyTotal species (energyUpdate species (true,(o,i)) E) ≤ K ∧ _
      have he : nonnegativeEnergies species (energyUpdate species (true,(o,i)) E) ∧
          energyTotal species (energyUpdate species (true,(o,i)) E) =
            energyTotal species E + (i.val+1) := by
        cases o <;> simp [energyTotal, nonnegativeEnergies, energyUpdate, weight,
          Function.update, hne, Ne.symm hne] at * <;> omega
      have hnew : energyTotal species (energyUpdate species (true,(o,i)) E) +
          xs.length * (M : ℤ) ≤ K := by rw [he.2]; omega
      exact ⟨by have hp : (0 : ℤ) ≤ xs.length * (M : ℤ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _); omega,
        ih _ he.1 hnew⟩
    | false =>
      change (i.val+1 : ℤ) + E (species o) + |Ns (species o)| ≤ h ∧ _
      refine ⟨by have hu := hR2 (species o); omega, ?_⟩
      change (if E (species o) < (i.val+1 : ℤ) then True else
        energyTotal species (energyUpdate species (false,(o,i)) E) ≤ K ∧
          BranchPath h M Ns species K xs (energyUpdate species (false,(o,i)) E))
      by_cases hk : E (species o) < (i.val+1 : ℤ)
      · rw [ite_eq_left hk]; trivial
      · rw [ite_eq_right hk]
        have he : nonnegativeEnergies species (energyUpdate species (false,(o,i)) E) ∧
            energyTotal species (energyUpdate species (false,(o,i)) E) =
              energyTotal species E - (i.val+1) := by
          cases o <;> simp [energyTotal, nonnegativeEnergies, energyUpdate, weight,
            Function.update, hne, Ne.symm hne] at * <;> omega
        have hnew : energyTotal species (energyUpdate species (false,(o,i)) E) +
            xs.length * (M : ℤ) ≤ K := by rw [he.2]; omega
        exact ⟨by have hp : (0 : ℤ) ≤ xs.length * (M : ℤ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _); omega,
          ih _ he.1 hnew⟩
theorem uniform_margin_path {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h d M : ℕ) (Ns : σ → ℤ) (species : Bosonize.A06.Orientation → σ)
    (hinj : Function.Injective species) (hU : UniformMargin h d M Ns)
    (w : Word M) (hw : w.length ≤ d) :
    PathCovered h Ns species (d*M) w := by
  have hne : species .right ≠ species .left := by
    intro he; have ho := hinj he; cases ho
  refine ⟨hne, branch_bounded h M (d*M) Ns species hne
      (uniform_margin_implies_r2 h d M (d*M) Ns hU (le_refl _)) w.reverse (fun _ => 0)
      (by simp [nonnegativeEnergies]) ?_⟩
  simp only [energyTotal, zero_add, List.length_reverse]
  exact_mod_cast Nat.mul_le_mul_right M hw
lemma inverse_branches_length {M : ℕ} (w v : Word M) (hv : v ∈ inverseBranches w) :
    v.length = w.length := by
  induction w generalizing v with
  | nil => simpa [inverseBranches] using hv
  | cons g w ih =>
    simp only [inverseBranches, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hv
    obtain ⟨t,ht,he⟩ := hv
    rcases he with rfl | rfl <;> simpa using congrArg Nat.succ (ih _ ht)
/-- Every word of the stated length obeys the derived finite margin. -/
theorem uniform_word_moment {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h d M : ℕ) (Ns : σ → ℤ) (species : Bosonize.A06.Orientation → σ)
    (hh : 0<h) (hN : Bosonize.A05.admissible h Ns)
    (hinj : Function.Injective species) (hU : UniformMargin h d M Ns)
    (w : Word M) (hw : w.length ≤ d) :
    inner ℂ (Bosonize.A05.groundKet h Ns)
      (theta h M species (Bosonize.A08.wordElement M w) (Bosonize.A05.groundKet h Ns)) =
      Bosonize.A08.omega0 M (Bosonize.A08.wordElement M w) := by
  exact covered_word_moment_contract h M Ns species w hh hN (d*M)
    (uniform_margin_implies_r2 h d M (d*M) Ns hU (le_refl _)) hinj
    (uniform_margin_path h d M Ns species hinj hU w hw)
/-- The same numerical bound covers every branch after inverse substitution. -/
theorem uniform_dressed_moment {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h d M : ℕ) (Ns : σ → ℤ) (hp : Bosonize.Ch18.HyperbolicPair)
    (species : Bosonize.A06.Orientation → σ)
    (hh : 0<h) (hN : Bosonize.A05.admissible h Ns)
    (hinj : Function.Injective species) (hU : UniformMargin h d M Ns)
    (w : Word M) (hw : w.length ≤ d) :
    inner ℂ (Bosonize.A05.groundKet h Ns)
      (theta h M species (Bosonize.A08.bogoliubovMap M hp.c (-hp.s)
        (Bosonize.A08.wordElement M w)) (Bosonize.A05.groundKet h Ns)) =
      Bosonize.A08.omegaP M hp (Bosonize.A08.wordElement M w) := by
  apply covered_dressed_moment_contract h M Ns hp species w hh hN (d*M)
    (uniform_margin_implies_r2 h d M (d*M) Ns hU (le_refl _)) hinj
  intro v hv
  apply uniform_margin_path h d M Ns species hinj hU v
  rw [inverse_branches_length w v (Finset.mem_filter.mp hv).1]
  exact hw
/-- Finite linear combinations require coverage word by word. -/
theorem covered_word_sum_moment {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (Ns : σ → ℤ) (species : Bosonize.A06.Orientation → σ)
    (hh : 0<h) (hN : Bosonize.A05.admissible h Ns)
    (K : ℕ) (hR2 : ∀ ν, 2*K+|Ns ν| ≤ h) (hinj : Function.Injective species)
    (ws : Finset (Word M)) (z : Word M → ℂ)
    (hpath : ∀ w ∈ ws, PathCovered h Ns species K w) :
    inner ℂ (Bosonize.A05.groundKet h Ns)
      (theta h M species (∑ w ∈ ws, z w • Bosonize.A08.wordElement M w)
        (Bosonize.A05.groundKet h Ns)) =
      Bosonize.A08.omega0 M (∑ w ∈ ws, z w • Bosonize.A08.wordElement M w) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    inner_sum, inner_smul_right, smul_eq_mul]
  exact Finset.sum_congr rfl (fun w hw => by
    rw [covered_word_moment_contract h M Ns species w hh hN K hR2 hinj (hpath w hw)])
theorem covered_dressed_sum_moment {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (Ns : σ → ℤ) (hp : Bosonize.Ch18.HyperbolicPair)
    (species : Bosonize.A06.Orientation → σ)
    (hh : 0<h) (hN : Bosonize.A05.admissible h Ns)
    (K : ℕ) (hR2 : ∀ ν, 2*K+|Ns ν| ≤ h) (hinj : Function.Injective species)
    (ws : Finset (Word M)) (z : Word M → ℂ)
    (hpath : ∀ w ∈ ws, ∀ v ∈ survivingBranches hp.c (-hp.s) w,
      PathCovered h Ns species K v) :
    inner ℂ (Bosonize.A05.groundKet h Ns)
      (theta h M species (Bosonize.A08.bogoliubovMap M hp.c (-hp.s)
        (∑ w ∈ ws, z w • Bosonize.A08.wordElement M w))
        (Bosonize.A05.groundKet h Ns)) =
      Bosonize.A08.omegaP M hp (∑ w ∈ ws, z w • Bosonize.A08.wordElement M w) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    inner_sum, inner_smul_right, smul_eq_mul]
  exact Finset.sum_congr rfl (fun w hw => by
    rw [covered_dressed_moment_contract h M Ns hp species w hh hN K hR2 hinj (hpath w hw)])
theorem polynomial_state_kernel {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M K : ℕ) (Ns : σ → ℤ) (species : Bosonize.A06.Orientation → σ)
    (hh : 0<h) (hN : Bosonize.A05.admissible h Ns)
    (hR2 : ∀ ν, 2*K+|Ns ν| ≤ h) (hinj : Function.Injective species)
    (p : Bosonize.A08.OscPoly M) (hp : PolynomialDomain K p)
    (hz : polynomialState h M Ns species p=0) : p=0 := by
  apply (Bosonize.A08.oscPairing_self_eq_zero M p).mp
  rw [← polynomial_state_gram_contract Ns species hh hinj hN hR2 p p hp hp, hz]
  exact inner_zero_left _
/-- Constants have their normalized finite sea expectation, also at M=0. -/
theorem constant_expectation {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h M : ℕ) (Ns : σ → ℤ) (species : Bosonize.A06.Orientation → σ) (c : ℂ) :
    inner ℂ (Bosonize.A05.groundKet h Ns)
      (theta h M species (c • (1 : Algebra M)) (Bosonize.A05.groundKet h Ns)) = c := by
  classical
  have hn : inner ℂ (Bosonize.A05.groundKet h Ns) (Bosonize.A05.groundKet h Ns) = 1 := by
    change inner ℂ (Bosonize.A02.ket (Bosonize.A05.groundConfiguration h Ns))
      (Bosonize.A02.ket (Bosonize.A05.groundConfiguration h Ns)) = 1
    simpa only [ite_true] using Bosonize.A02.ket_inner
      (Bosonize.A05.groundConfiguration h Ns) (Bosonize.A05.groundConfiguration h Ns)
  simp only [map_smul, map_one, LinearMap.smul_apply, Module.End.one_apply, inner_smul_right, hn, mul_one]


namespace Examples

noncomputable local instance orientationFintype : Fintype Bosonize.A06.Orientation :=
  ⟨⟨{.right, .left}, by decide⟩, fun o => by cases o <;> simp⟩

def orientationCode : Bosonize.A06.Orientation → Bool
  | .right => false
  | .left => true

theorem orientationCode_injective : Function.Injective orientationCode := by
  intro a b hab
  cases a <;> cases b <;> simp [orientationCode] at hab ⊢

noncomputable local instance orientationMax : Max Bosonize.A06.Orientation :=
  ⟨fun a b => match a, b with
    | .right, x => x
    | .left, _ => .left⟩

noncomputable local instance orientationMin : Min Bosonize.A06.Orientation :=
  ⟨fun a b => match a, b with
    | .right, _ => .right
    | .left, x => x⟩

noncomputable local instance orientationLinearOrder : LinearOrder Bosonize.A06.Orientation :=
  LinearOrder.lift orientationCode orientationCode_injective
    (by intro a b; cases a <;> cases b <;> rfl)
    (by intro a b; cases a <;> cases b <;> rfl)

noncomputable local instance orientationDecidableEq : DecidableEq Bosonize.A06.Orientation :=
  LinearOrder.toDecidableEq

set_option maxHeartbeats 1000000

def rightAnnihilator : Generator 1 := (false, (.right, 0))
def rightCreator : Generator 1 := (true, (.right, 0))
def leftAnnihilator : Generator 1 := (false, (.left, 0))
def leftCreator : Generator 1 := (true, (.left, 0))

/-- Empty-word/M=0 boundary case: the sea line is the entire zero-mode
polynomial image, and the path certificate has no current hypotheses. -/
example : PathCovered 2 (fun _ : Bosonize.A06.Orientation => (0 : ℤ)) id
    0 ([] : Word 0) := by
  simp [PathCovered, BranchPath, energyTotal, nonnegativeEnergies]

/-- Concrete admissible regulator: `h=4`, `L=8`, zero charges, mode cutoff
`M=1`, and word length two. The unsqueezed contraction `A₁ C₁` stays within
the exact mode-plus-suffix margin `1+1≤4`. -/
def contractionWord : Word 1 := [rightAnnihilator, rightCreator]

example : PathCovered 4 (fun _ : Bosonize.A06.Orientation => (0 : ℤ)) id
    2
    contractionWord := by
  simp [PathCovered, BranchPath, energyUpdate, energyTotal,
    nonnegativeEnergies, weight, contractionWord, rightCreator,
    rightAnnihilator, Function.update]

/-- The nonzero-squeeze quadratic expansion covers both live and immediately
killed branches at the same explicit regulator. -/
example : ∀ v ∈ inverseBranches contractionWord,
    PathCovered 4 (fun _ : Bosonize.A06.Orientation => (0 : ℤ)) id 2 v := by
  intro v hv
  simp [inverseBranches, contractionWord, rightCreator, rightAnnihilator,
    flipGenerator] at hv
  rcases hv with rfl | rfl | rfl | rfl
  all_goals simp [PathCovered, BranchPath, energyUpdate, energyTotal,
    nonnegativeEnergies, weight, Function.update,
    Bosonize.A07Interactions.oppositeOrientation]

/-- Mixed-species creation uses separate per-species energies, so neither
species can mask the other's path or charge margin. -/
def mixedCreationWord : Word 1 := [rightCreator, leftCreator]

example : PathCovered 4 (fun _ : Bosonize.A06.Orientation => (0 : ℤ)) id
    2
    mixedCreationWord := by
  simp [PathCovered, BranchPath, energyUpdate,
    energyTotal, nonnegativeEnergies, weight, mixedCreationWord,
    rightCreator, leftCreator, Function.update]

def fourthOrderWord : Word 1 :=
  [rightAnnihilator, rightCreator, rightAnnihilator, rightCreator]

/-- A genuinely longer, order-sensitive alternating word has an explicit
rightmost-first path certificate at the same finite regulator. -/
example : PathCovered 8 (fun _ : Bosonize.A06.Orientation => (0 : ℤ)) id
    4 fourthOrderWord := by
  simp [PathCovered, BranchPath, energyUpdate, energyTotal,
    nonnegativeEnergies, weight, rightCreator,
    rightAnnihilator, fourthOrderWord, Function.update]

/-- All sixteen inverse-substitution branches of the fourth-order word meet
the explicit live-or-killed path condition at `h=8`. -/
example : ∀ v ∈ inverseBranches fourthOrderWord,
    PathCovered 8 (fun _ : Bosonize.A06.Orientation => (0 : ℤ)) id 4 v := by
  intro v hv
  simp [inverseBranches, fourthOrderWord, rightCreator, rightAnnihilator,
    flipGenerator] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [PathCovered, BranchPath, energyUpdate, energyTotal,
    nonnegativeEnergies, weight, Function.update,
    Bosonize.A07Interactions.oppositeOrientation]

noncomputable def nonzeroSqueeze : Bosonize.Ch18.HyperbolicPair where
  c := 5/4
  s := 3/4
  hyperbolic_id := by norm_num

example : nonzeroSqueeze.s ≠ 0 := by norm_num [nonzeroSqueeze]

/-- A concrete unsqueezed contraction theorem instance at `h=4`, `M=1`. -/
example :
    inner ℂ (Bosonize.A05.groundKet 4
      (fun _ : Bosonize.A06.Orientation => (0 : ℤ)))
      (theta (σ := Bosonize.A06.Orientation) 4 1 id
        (Bosonize.A08.wordElement 1 contractionWord)
        (Bosonize.A05.groundKet 4
          (fun _ : Bosonize.A06.Orientation => (0 : ℤ)))) =
      Bosonize.A08.omega0 1 (Bosonize.A08.wordElement 1 contractionWord) := by
  have hN : Bosonize.A05.admissible 4
      (fun _ : Bosonize.A06.Orientation => (0 : ℤ)) := by
    intro ν
    exact ⟨by norm_num [Bosonize.Ch07.admissible], by norm_num [Bosonize.Ch07.admissible]⟩
  have hR2 : ∀ ν : Bosonize.A06.Orientation, 2 * 2 + |(0 : ℤ)| ≤ 4 := by
    intro ν
    norm_num
  have hPath : PathCovered 4
      (fun _ : Bosonize.A06.Orientation => (0 : ℤ)) id 2 contractionWord := by
    simp [PathCovered, contractionWord, rightCreator, rightAnnihilator,
      BranchPath, energyUpdate, energyTotal, nonnegativeEnergies, weight,
      Function.update]
  exact covered_word_moment_contract 4 1 _ id contractionWord (by norm_num)
    hN 2 hR2 Function.injective_id hPath

/-- A concrete nonzero-squeeze quadratic comparison. Its path condition covers
all coefficient-surviving inverse branches, including mixed orientations. -/
example :
    inner ℂ (Bosonize.A05.groundKet 4
      (fun _ : Bosonize.A06.Orientation => (0 : ℤ)))
      (theta (σ := Bosonize.A06.Orientation) 4 1 id
        (Bosonize.A08.bogoliubovMap 1 nonzeroSqueeze.c (-nonzeroSqueeze.s)
          (Bosonize.A08.wordElement 1 contractionWord))
        (Bosonize.A05.groundKet 4
          (fun _ : Bosonize.A06.Orientation => (0 : ℤ)))) =
      Bosonize.A08.omegaP 1 nonzeroSqueeze
        (Bosonize.A08.wordElement 1 contractionWord) := by
  have hN : Bosonize.A05.admissible 4
      (fun _ : Bosonize.A06.Orientation => (0 : ℤ)) := by
    intro ν
    exact ⟨by norm_num [Bosonize.Ch07.admissible], by norm_num [Bosonize.Ch07.admissible]⟩
  have hR2 : ∀ ν : Bosonize.A06.Orientation, 2 * 2 + |(0 : ℤ)| ≤ 4 := by
    intro ν
    norm_num
  have hPath : ∀ v ∈ survivingBranches nonzeroSqueeze.c (-nonzeroSqueeze.s)
      contractionWord, PathCovered 4
        (fun _ : Bosonize.A06.Orientation => (0 : ℤ)) id 2 v := by
    intro v hv
    have hv' : v ∈ inverseBranches contractionWord :=
      (Finset.mem_filter.mp hv).1
    have hall : ∀ v ∈ inverseBranches contractionWord, PathCovered 4
        (fun _ : Bosonize.A06.Orientation => (0 : ℤ)) id 2 v := by
      intro v hv
      simp [inverseBranches, contractionWord, rightCreator, rightAnnihilator,
        flipGenerator] at hv
      rcases hv with rfl | rfl | rfl | rfl
      all_goals simp [PathCovered, BranchPath, energyUpdate, energyTotal,
        nonnegativeEnergies, weight, Function.update,
        Bosonize.A07Interactions.oppositeOrientation]
    exact hall v hv'
  exact covered_dressed_moment_contract 4 1 _ nonzeroSqueeze id contractionWord
    (by norm_num) hN 2 hR2 Function.injective_id hPath

/-- The order-sensitive fourth-order word has a concrete finite comparison
at `h=8`; its word length and path budget remain explicit. -/
example :
    inner ℂ (Bosonize.A05.groundKet 8
      (fun _ : Bosonize.A06.Orientation => (0 : ℤ)))
      (theta (σ := Bosonize.A06.Orientation) 8 1 id
        (Bosonize.A08.wordElement 1 fourthOrderWord)
        (Bosonize.A05.groundKet 8
          (fun _ : Bosonize.A06.Orientation => (0 : ℤ)))) =
      Bosonize.A08.omega0 1 (Bosonize.A08.wordElement 1 fourthOrderWord) := by
  have hN : Bosonize.A05.admissible 8
      (fun _ : Bosonize.A06.Orientation => (0 : ℤ)) := by
    intro ν
    exact ⟨by norm_num [Bosonize.Ch07.admissible], by norm_num [Bosonize.Ch07.admissible]⟩
  have hR2 : ∀ ν : Bosonize.A06.Orientation, 2 * 4 + |(0 : ℤ)| ≤ 8 := by
    intro ν
    norm_num
  have hPath : PathCovered 8
      (fun _ : Bosonize.A06.Orientation => (0 : ℤ)) id 4 fourthOrderWord := by
    simp [PathCovered, fourthOrderWord, rightCreator, rightAnnihilator,
      BranchPath, energyUpdate, energyTotal, nonnegativeEnergies, weight,
      Function.update]
  exact covered_word_moment_contract 8 1 _ id fourthOrderWord (by norm_num)
    hN 4 hR2 Function.injective_id hPath

/-- Raw unsqueezed-sea contractions do not encode the squeezed functional:
for nonzero squeeze, the anomalous annihilator pair has a nonzero `omegaP`
expectation while its raw `omega0` expectation vanishes. -/
example :
    Bosonize.A08.omegaP 1 nonzeroSqueeze
      (Bosonize.A08.wordElement 1 [rightAnnihilator, leftAnnihilator]) ≠
    Bosonize.A08.omega0 1
      (Bosonize.A08.wordElement 1 [rightAnnihilator, leftAnnihilator]) := by
  norm_num [Bosonize.A08.omegaP, Bosonize.A08.omega0,
    Bosonize.A08.bogoliubovMap, Bosonize.A08.wordElement,
    Bosonize.A08.oscRep, Bosonize.A08.oscAnnihilation,
    Bosonize.A08.oscCreation, nonzeroSqueeze,
    rightAnnihilator, leftAnnihilator, rightCreator,
    Bosonize.A07Interactions.oppositeOrientation]
  simp [MvPolynomial.coeff_mul]
  norm_num [Bosonize.A08.oscWeight]

/-- The empty mode set still has every scalar expectation. -/
example (c : ℂ) :
    inner ℂ (Bosonize.A05.groundKet 2 (fun _ : Bosonize.A06.Orientation => (0 : ℤ)))
      (theta 2 0 id (c • (1 : Algebra 0))
        (Bosonize.A05.groundKet 2 (fun _ : Bosonize.A06.Orientation => (0 : ℤ)))) = c :=
  constant_expectation 2 0 _ id c

/-- All branches of a genuinely fourth-order squeezed comparison satisfy the
proved length wrapper at h=8, M=1, d=4. -/
example :
    inner ℂ (Bosonize.A05.groundKet 8 (fun _ : Bosonize.A06.Orientation => (0 : ℤ)))
      (theta 8 1 id (Bosonize.A08.bogoliubovMap 1 nonzeroSqueeze.c (-nonzeroSqueeze.s)
        (Bosonize.A08.wordElement 1 fourthOrderWord))
        (Bosonize.A05.groundKet 8 (fun _ : Bosonize.A06.Orientation => (0 : ℤ)))) =
      Bosonize.A08.omegaP 1 nonzeroSqueeze (Bosonize.A08.wordElement 1 fourthOrderWord) := by
  apply uniform_dressed_moment 8 4 1 _ nonzeroSqueeze id (by norm_num)
    (by intro ν; constructor <;> norm_num [Bosonize.Ch07.admissible]) Function.injective_id
    (by intro ν; norm_num) fourthOrderWord
  simp [fourthOrderWord]

/-- Mixed species have an actual current moment comparison at the same
quadratic regulator, in addition to their explicit path certificate above. -/
example :
    inner ℂ (Bosonize.A05.groundKet 4 (fun _ : Bosonize.A06.Orientation => (0 : ℤ)))
      (theta 4 1 id (Bosonize.A08.wordElement 1 mixedCreationWord)
        (Bosonize.A05.groundKet 4 (fun _ : Bosonize.A06.Orientation => (0 : ℤ)))) =
      Bosonize.A08.omega0 1 (Bosonize.A08.wordElement 1 mixedCreationWord) := by
  apply uniform_word_moment 4 2 1 _ id (by norm_num)
    (by intro ν; constructor <;> norm_num [Bosonize.Ch07.admissible]) Function.injective_id
    (by intro ν; norm_num) mixedCreationWord
  simp [mixedCreationWord]

end Examples

end Bosonize.V1S4
