## Source map

- `notes/md/ch16_field_Hamiltonian.md`, Definitions 16.1–16.7, Lemmas 16.2–16.3, Theorems 16.5 and 16.8: the finite two-branch normal-ordered Hamiltonian, the weight, and the error. Equations (16.9)–(16.10) are explicitly *not* formalized.
- `notes/appendices/a06_chiral_fields_and_lattice_kernels.md`, “Correct square and normalization audit” and “Constructive realization in Lean”: the two mixed normal-order terms, factor `2*(2*h)`, orientation, genuine current adjoints, and previously verified finite-kernel interfaces. The appendix's proposed formula is a proof target, not proof evidence.
- `Bosonize.Core.A06ChiralFields`: `Orientation`, `Branches`, `speciesOf`, `chiralField`, `chiralDifferenceExpansion`, `chiral_forward_diff`, `joint_signed_current_commutator`, `marginAt`, `branchMargins`, and ground/no-alias witnesses.
- `Bosonize.Core.Ch15DualFields`: actual `phiField` and `thetaField`; `Bosonize.Core.A05MultiSpecies`: ambient `Operators`, `rho`, `rho_cross_commute`, `rho_adjoint`, `jointBudget`, `groundKet`, `ground_mem_budget`, `ground_ne_zero`, and `rho_lowering_budget_zero`.
- `Bosonize.Core.A01FourierCharacters`: `integerCharacter`, `canonicalRoot`, and character orthogonality; `Bosonize.Core.Ch10Heisenberg`: the **signed** commutator `[rho_p,rho_q] = -p` when `p+q=0`, restricted to budgets. The generated Core API digest and the Phase A verifier are the only available API/compiler references; the draft has not been elaborated here.

## Design and scope

The Hilbert carrier is the actual finite multispecies Fock space `A05.FockSpace σ h`, with *ambient* endomorphisms `A05.Operators σ h`; there is no insertion of intermediate budget projections. Its periodic spatial lattice is `ZMod (2*h)` and its independent branches are the **distinct species** of `A06.Branches σ`. The primitive root `ζ` has order `2*h`. The retained mode labels are `Fin M`, interpreted as `m = index.val + 1`; hence there are no zero denominators for represented labels. A Boolean denotes the branch and another denotes whether the signed current is a creator (`rho_+m`, `true`) or an annihilator (`rho_-m`, `false`). In this Core convention, `rho_-m` kills the ground ket and `[rho_-m,rho_m] = +m` on appropriate budgets.

An ordered quadratic **symbol** is a complex coefficient function on pairs of finite signed-current labels. `rawEvaluation` evaluates the original operator order. `normalEvaluation` instead swaps only a right-hand creator past a left-hand annihilator, representing the prescribed vacuum normal ordering *at symbol level*. This is not a map from already-evaluated operators to operators: equal represented operators need not have their symbols confused. It is linear in the quadratic symbol, but its value can differ from raw evaluation by a commutator. No unproved data definition or new axiom is used. The key contraction is `rho_m*rho_-m - rho_-m*rho_m = -m` on the input budget; this is the vacuum subtraction, not an assumed operator identity on the entire Fock space.

The exact finite differences are those of A06/CH15; coefficients contain the full orientation-dependent multipliers `(ζ^(±m)-1)` and `Complex.I/m`. The formal quadratic symbol for `phi` and `theta` squares is the sum of *their two separate squares*. Its chiral decomposition is a polynomial identity even for noncommuting endomorphisms; no cross-species commutativity is needed to cancel those terms. Evaluation and spatial DFT collapse are subsequent operations. The collapsed chiral square is `2*(2*h)` times a positive-mode ordered density product, giving `4*weightedEnergy` for the two dual-field squares. The algebraic weight is `epsilon(m) = (2*h)/m^2 * (ζ^m-1)*(ζ^(-m)-1)`; `g0 := epsilon(1)` is chosen *algebraically*, not the continuum constant `4*pi^2/(2*h)`.

Budget identities explicitly require `0<h`, `1≤M`, `2*M<2*h`, primitive `ζ`, and both `A06.marginAt h M K Ns` branch conditions. The stronger `marginWithExcursion` spells out `2*M+K+excursion+|Ns ν|≤h` on each selected species when the input is in the enlarged `K+excursion` budget. Normal-ordering contractions, density commutator substitutions, and excited witnesses must be applied to **right-suffix inputs** satisfying those bounds. These are *sufficient* margins, not global CCR claims.

## Lean draft

```lean
import Bosonize

-- BEGIN_MODULE BosonizeStubs/A07FiniteNormalOrdering.lean
namespace Bosonize.A07

open scoped BigOperators

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

-- branch: false = right, true = left;
-- creator: false = rho_(-m), true = rho_m.
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

lemma normal_evaluation_add (h M : ℕ) (branches : A06.Branches σ)
    (Q R : QuadraticSymbol M) :
    normalEvaluation h M branches (Q + R) =
      normalEvaluation h M branches Q + normalEvaluation h M branches R := by sorry

lemma normal_evaluation_smul (h M : ℕ) (branches : A06.Branches σ)
    (a : ℂ) (Q : QuadraticSymbol M) :
    normalEvaluation h M branches (a • Q) =
      a • normalEvaluation h M branches Q := by sorry

lemma normal_pair_contraction (h M : ℕ) (branches : A06.Branches σ)
    (p q : Letter M) :
    normalPair h M branches p q - rawPair h M branches p q =
      if p.2.2 = false ∧ q.2.2 = true then
        A02.commutator (current h M branches q) (current h M branches p)
      else 0 := by sorry

lemma contraction_on_joint_budget (h M K : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (p q : Letter M) (hp : p.2.2 = false) (hq : q.2.2 = true)
    (hbranch : p.1 = q.1)
    (hmargin : A06.marginAt h M K Ns
      (A06.speciesOf branches (orientation p.1)))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    (normalPair h M branches p q - rawPair h M branches p q) v =
      (if natMode p = natMode q then -(natMode p : ℂ) else 0) • v := by sorry

lemma chiral_gradient_representation (h M : ℕ) [NeZero (2 * h)]
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (η : A06.Orientation)
    (x : ZMod (2 * h)) :
    (∑ p : Letter M, (chiralCoefficient h M ζ η x p) •
      current h M branches p) =
      A06.opForwardDiff h (A06.chiralField h M ζ branches η) x := by sorry

lemma dual_square_chiral_decomposition (h M : ℕ) (ζ : ℂ)
    (x : ZMod (2 * h)) :
    dualSquareSymbol h M ζ x =
      (2 : ℂ) • (squareSymbol (chiralCoefficient h M ζ .right x) +
        squareSymbol (chiralCoefficient h M ζ .left x)) := by sorry

end Bosonize.A07
-- END_MODULE BosonizeStubs/A07FiniteNormalOrdering.lean

-- BEGIN_MODULE BosonizeStubs/Ch16FieldHamiltonian.lean
namespace Bosonize.Ch16

open scoped BigOperators

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

-- A sufficient right-suffix margin for an additional excursion.
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

lemma field_chiral_identity (h M : ℕ) (ζ : ℂ)
    (branches : A06.Branches σ) (x : ZMod (2 * h)) :
    localFieldEnergy h M ζ branches x =
      (2 : ℂ) • (chiralSquare h M ζ branches .right x +
        chiralSquare h M ζ branches .left x) := by sorry

lemma chiral_spatial_collapse_on_budget (h M K : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (η : A06.Orientation)
    (Ns : σ → ℤ)
    (hmargin : A06.marginAt h M K Ns (A06.speciesOf branches η))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    (∑ x : ZMod (2 * h), chiralSquare h M ζ branches η x) v =
      ((2 : ℂ) •
        (∑ m ∈ Finset.Icc 1 M,
          epsilon h ζ m •
            (A05.rho h (A06.speciesOf branches η) (m : ℤ) *
              A05.rho h (A06.speciesOf branches η) (-(m : ℤ))))) v := by sorry

theorem field_weighted_on_budget (h M K : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    fieldHamiltonian h M ζ branches v =
      ((4 : ℂ) • weightedEnergy h M ζ branches) v := by sorry

theorem field_weighted_after_excursion (h M K excursion : ℕ)
    [NeZero (2 * h)] (hh : 0 < h) (hM : 1 ≤ M)
    (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : marginWithExcursion h M K excursion Ns branches)
    (v : A05.FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns (K + excursion)) :
    fieldHamiltonian h M ζ branches v =
      ((4 : ℂ) • weightedEnergy h M ζ branches) v := by sorry

lemma error_weighted_on_budget (h M K : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hmargin : A06.branchMargins h M K Ns branches)
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    errorOperator h M ζ branches v =
      ((4 : ℂ) • weightedError h M ζ branches) v := by sorry

lemma ground_error_zero (h M K : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (hN : A05.admissible h Ns)
    (hmargin : A06.branchMargins h M K Ns branches) :
    errorOperator h M ζ branches (A05.groundKet h Ns) = 0 := by sorry

lemma excited_ket_mem_budget (h K m : ℕ) (hh : 0 < h)
    (hm : m ≤ K) (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (branches : A06.Branches σ) (η : A06.Orientation) :
    excitedKet h Ns branches η m ∈ A05.jointBudget h Ns K := by sorry

lemma excited_ket_nonzero (h M m : ℕ) (hh : 0 < h)
    (hm : 1 ≤ m) (hcut : m ≤ M)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (branches : A06.Branches σ) (η : A06.Orientation)
    (hmargin : A06.marginAt h M m Ns (A06.speciesOf branches η)) :
    excitedKet h Ns branches η m ≠ 0 := by sorry

theorem single_mode_error_eigenvector (h M K m : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (hm : 1 ≤ m) (hcut : m ≤ M) (hK : m ≤ K)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (η : A06.Orientation)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (hmargin : A06.branchMargins h M K Ns branches) :
    errorOperator h M ζ branches (excitedKet h Ns branches η m) =
      ((4 : ℂ) * (m : ℂ) * (epsilon h ζ m - referenceWeight h ζ)) •
        excitedKet h Ns branches η m := by sorry

theorem first_mode_error_zero (h M K : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hK : 1 ≤ K)
    (hNoAlias : 2 * M < 2 * h)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (η : A06.Orientation)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (hmargin : A06.branchMargins h M K Ns branches) :
    errorOperator h M ζ branches (excitedKet h Ns branches η 1) = 0 := by sorry

theorem error_nonzero_witness (h M K m : ℕ) [NeZero (2 * h)]
    (hh : 0 < h) (hM : 1 ≤ M) (hNoAlias : 2 * M < 2 * h)
    (hm : 1 ≤ m) (hcut : m ≤ M) (hK : m ≤ K)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (hweight : epsilon h ζ m ≠ referenceWeight h ζ)
    (branches : A06.Branches σ) (η : A06.Orientation)
    (Ns : σ → ℤ) (hN : A05.admissible h Ns)
    (hmargin : A06.branchMargins h M K Ns branches) :
    excitedKet h Ns branches η m ≠ 0 ∧
      errorOperator h M ζ branches (excitedKet h Ns branches η m) ≠ 0 := by sorry

theorem concrete_dispersion_gap :
    epsilon 8 (A01.canonicalRoot 16) 2 ≠
      referenceWeight 8 (A01.canonicalRoot 16) := by sorry

theorem concrete_excited_error_witness :
    A05.admissible 8 (fun _ : Fin 2 => 0) ∧
    A06.branchMargins 8 2 2 (fun _ : Fin 2 => 0) standardBranches ∧
    excitedKet 8 (fun _ : Fin 2 => 0) standardBranches .right 2 ≠ 0 ∧
    errorOperator 8 2 (A01.canonicalRoot 16) standardBranches
      (excitedKet 8 (fun _ : Fin 2 => 0) standardBranches .right 2) ≠ 0 := by sorry

end Bosonize.Ch16
-- END_MODULE BosonizeStubs/Ch16FieldHamiltonian.lean
```

## Companion notebook

**Finite carrier audit.** The `A07.Letter` label has `(branch, m, creator)` and `m ∈ {1,…,M}` by construction. `signedMode` yields `+m` for a creator, `-m` for an annihilator. `gradientCoefficient` is obtained by *expanding the existing A06 forward difference*, not by introducing a spectral derivative. The value of the square is the linear evaluation of the coefficient function on **ordered pairs**, so contractions are not hidden in an inconsistent post-evaluation rewrite. Verify `normal_pair_contraction` by cases on the two creator flags. For the same species, compare the paired mode indices and apply `A06.joint_signed_current_commutator` on the actual input subspace. Across species, use `A05.rho_cross_commute`.

**Cancellation and Fourier calculation.** At fixed `x`, write `a=Δφ_right`, `b=Δφ_left` at the symbol level. Expand `(a+b)^2+(a-b)^2=2(a²+b²)` as an ordered-word identity: the `ab` and `ba` coefficients cancel separately. For each chirality, the four sign combinations of momentum indices leave two opposite-sign pairings after summing the character over `ZMod (2*h)`. The others have frequency `±(m+n)` and vanish since `1≤m,n≤M`, `0<m+n≤2M<2h`. Opposite-sign terms enforce `m=n` and produce *two* identical `rho_m rho_-m` terms after normal ordering. Each spatial sum contributes `(2*h)`; their combined coefficient is `2*(2*h) (ζ^m-1)(ζ^-m-1)/m²`. Multiplication by the dual-square decomposition gives `4*epsilon(m)` on each of the two branches. Do not treat a formal symbol cancellation as a global current CCR identity.

**Ground, reference modes, and witness.** Because `rho_-m groundKet=0` for `m>0`, the weighted error annihilates the ground ket. With `g0=epsilon(1)`, the one-mode excited ket at `m=1` is in the kernel. For a general `m`, move the only rightmost lowering mode through `rho_m groundKet` with the signed budget CCR. The nonzero scalar `m` times the nonzero ground ket also proves `rho_m groundKet≠0`; no independent cyclicity or occupation axiom is assumed. The conclusion for `m≥2` requires the **separate** hypothesis `epsilon(m)≠g0`. For a concrete gap test, `h=8`, `M=2`, `K=2`, `ζ=canonicalRoot 16`, zero charges and distinct species `0,1` give `2M+K=6≤8`, `2M=4<16`, and `epsilon(2)≠epsilon(1)`. Establish the last inequality algebraically or from the *proved* Core canonical-dispersion formula; it is a proposed theorem, not numerical verification.

**Proof dependency order.** A07 linearity/contraction → A07 chiral coefficient identity and symbol cancellation → CH16 local identity → chiral DFT collapse (character orthogonality and no alias) → weighted field on budgets → weighted error → ground/one-mode kernel → excited eigenvalue → explicit nonzero ket and concrete dispersion gap. For composite words, use `marginWithExcursion` with the budget of each right suffix, not a projection between factors.

## Review obligations

1. **Source-to-carrier equivalence:** check that the chapter's external normal ordering of *gradients squared* is indeed the prescribed quadratic-symbol evaluation (and not raw operator squaring or a compression map). Confirm the `rho_-m` annihilator sign and test all four sign pairings directly. Prove actual chiral adjoints only by reference to `A06.chiral_adjoint`; no alternative adjoint is introduced.
2. **Non-vacuity:** establish admissibility of the concrete zero-charge sector, ground budget membership and nonzero ground ket from Core, membership/nonvanishing of `excitedKet`, and `epsilon(2)≠epsilon(1)`. Also check the stated margins on each *actual* right-suffix input before replacing commutators by scalars. A proof of an implication with inconsistent margins is not an acceptable witness.
3. **Elaboration and mathematical review:** run the provided `scripts/webllm/verify_phase_a.py` in the matching repository checkout, inspect every compiler diagnostic and generated axiom audit, and independently review theorem truth. The Lean statements here deliberately use `:= by sorry`; Phase A elaboration would establish only a coherent proposal, **not** mathematical proof, Phase B completion, or Core locking.
4. **Unresolved source limitations:** CH16's `L` is realized as `2*h` because this is the verified Core lattice. The source's field notation does not specify a canonical symbol-level normal-order map; the A07 choice is therefore a reviewable definition, not a fact already proved in CH15. No continuum normalization, analytic limits, Taylor remainder, or RG irrelevance statements are included. The `epsilon` definition accepts `m=0` syntactically but every physical theorem uses `m≥1` or `Fin M` and thus never divides by a zero-mode denominator.


## Local independent Phase A review — 2026-10-13

Independent reviewer `/root/characters` checked all six A07 and thirteen CH16
contracts against the current Core and reference notes. Verdict PASS. This is
mathematical/interface review, not proof completion. The saved artifact compiler
log elaborates 29 complete data declarations using standard axioms; its 19
theorem bodies remain unproved. The previous finish was interrupted during the
staging build, leaving the primary checkout unchanged.

The normal-ordering carrier is a quadratic coefficient symbol, not a map on
already represented operators. Signed currents, the -m contraction, two Fourier
cross pairings, normalization4, actual shared budget/suffix margins and the
nonzero-ground excited witness contracts are retained. The Phase B preparation
is advisory and its proof bodies require installed-compiler verification.
No analytic, continuum, RG or arbitrary-root sine theorem is claimed.
