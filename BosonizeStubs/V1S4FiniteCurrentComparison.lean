import Bosonize.Core.A05MultiSpecies
import Bosonize.Core.A08OscillatorStates

/-! V1-S4 Phase A candidate: exact finite current-word comparison.
The only placeholders below are theorem contracts in unaccepted staging.
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
  sorry

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
    {σ : Type*} [Fintype σ] [LinearOrder σ]
    (species : Bosonize.A06.Orientation → σ)
    (hinj : Function.Injective species)
    (r : Bosonize.A08.OscMode M →₀ ℕ) :
    Bosonize.A08.oscMonomialNorm r =
      ∏ ν : Bosonize.A06.Orientation,
        Bosonize.Ch11.hallFactor
          (((List.finRange M).flatMap fun i =>
            List.replicate (r (ν, i)) (i.val + 1) : List ℕ) : Multiset ℕ) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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

end Examples

end Bosonize.V1S4
