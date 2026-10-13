import Bosonize
import BosonizeStubs.A07FiniteNormalOrdering

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
