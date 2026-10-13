import Bosonize

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
      normalEvaluation h M branches Q + normalEvaluation h M branches R := by
  classical
  simp only [normalEvaluation, Pi.add_apply, add_smul, Finset.sum_add_distrib]

lemma normal_evaluation_smul (h M : ℕ) (branches : A06.Branches σ)
    (a : ℂ) (Q : QuadraticSymbol M) :
    normalEvaluation h M branches (a • Q) =
      a • normalEvaluation h M branches Q := by
  classical
  simp only [normalEvaluation, Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum]

lemma normal_pair_contraction (h M : ℕ) (branches : A06.Branches σ)
    (p q : Letter M) :
    normalPair h M branches p q - rawPair h M branches p q =
      if p.2.2 = false ∧ q.2.2 = true then
        A02.commutator (current h M branches q) (current h M branches p)
      else 0 := by
  classical
  by_cases hs : p.2.2 = false ∧ q.2.2 = true
  · simp [normalPair, hs, rawPair, A02.commutator]
  · simp [normalPair, hs]

lemma contraction_on_joint_budget (h M K : ℕ) (hh : 0 < h)
    (branches : A06.Branches σ) (Ns : σ → ℤ)
    (p q : Letter M) (hp : p.2.2 = false) (hq : q.2.2 = true)
    (hbranch : p.1 = q.1)
    (hmargin : A06.marginAt h M K Ns
      (A06.speciesOf branches (orientation p.1)))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    (normalPair h M branches p q - rawPair h M branches p q) v =
      (if natMode p = natMode q then -(natMode p : ℂ) else 0) • v := by
  classical
  rw [normal_pair_contraction]
  simp only [hp, hq, and_self, ite_true]
  unfold current signedMode
  simp only [hp, hq, Bool.false_eq_true, ite_false, ite_true, ← hbranch]
  rw [A06.joint_signed_current_commutator h K hh Ns
    (A06.speciesOf branches (orientation p.1)) (natMode q : ℤ) (-(natMode p : ℤ))]
  · unfold Ch10.schwingerCoefficient
    by_cases he : natMode p = natMode q
    · simp [he]
    · have hz : (natMode q : ℤ) + -(natMode p : ℤ) ≠ 0 := by omega
      simp only [hz, he, ite_false]
  · have hpM : natMode p ≤ M := by unfold natMode; omega
    have hqM : natMode q ≤ M := by unfold natMode; omega
    unfold A06.marginAt at hmargin
    rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    omega
  · exact hv

lemma chiral_gradient_representation (h M : ℕ) [NeZero (2 * h)]
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * h))
    (branches : A06.Branches σ) (η : A06.Orientation)
    (x : ZMod (2 * h)) :
    (∑ p : Letter M, (chiralCoefficient h M ζ η x p) •
      current h M branches p) =
      A06.opForwardDiff h (A06.chiralField h M ζ branches η) x  := by
  classical
  have hsum (f : ℕ → A05.Operators σ h) :
      (∑ i : Fin M, f (i.val + 1)) = ∑ m ∈ Finset.Icc 1 M, f m := by
    apply Finset.sum_bij (fun i _ => i.val + 1)
    · intro i hi
      simp only [Finset.mem_Icc]
      omega
    · intro i hi j hj he
      apply Fin.ext
      omega
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      refine ⟨⟨m - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp
      omega
    · intro i hi
      rfl
  rw [A06.chiral_forward_diff h M ζ hζ branches η x]
  unfold Letter
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  unfold chiralCoefficient
  cases η <;>
    simp only [orientation, Bool.false_eq_true, ite_false, ite_true,
      reduceCtorEq, zero_smul, Finset.sum_const_zero, add_zero, zero_add]
  all_goals
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    unfold gradientCoefficient current phaseSign signedMode natMode
    simp only [orientation, Bool.false_eq_true, ite_false, ite_true,
      A06.orientationSign, Int.cast_one, Int.cast_neg,
      one_mul, neg_mul, neg_neg]
    unfold A06.chiralDifferenceExpansion
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [smul_sub, smul_smul, A06.orientationSign,
      one_mul, neg_mul, neg_neg]
    module

lemma dual_square_chiral_decomposition (h M : ℕ) (ζ : ℂ)
    (x : ZMod (2 * h)) :
    dualSquareSymbol h M ζ x =
      (2 : ℂ) • (squareSymbol (chiralCoefficient h M ζ .right x) +
        squareSymbol (chiralCoefficient h M ζ .left x)) := by
  funext pq
  rcases pq with ⟨⟨bp, ip, cp⟩, ⟨bq, iq, cq⟩⟩
  cases bp <;> cases bq <;>
    simp [dualSquareSymbol, squareSymbol, phiCoefficient, thetaCoefficient,
      chiralCoefficient, orientation, A06.orientationSign] <;> ring

end Bosonize.A07
