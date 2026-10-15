import Bosonize.Core.Ch18Bogoliubov
import BosonizeStubs.A08OscillatorStates

namespace Bosonize.Ch19

open scoped BigOperators

noncomputable def densityKernel (h M : ℕ) (ζ : ℂ) (c2 s2 : ℝ) (d : ℤ) : ℂ :=
  (((2 * h : ℕ) : ℂ)⁻¹) ^ 2 * ∑ m ∈ Finset.Icc 1 M, (m : ℂ) *
    ((s2 : ℂ) * Bosonize.A01.integerCharacter ζ (-(m : ℤ)) d +
     (c2 : ℂ) * Bosonize.A01.integerCharacter ζ (m : ℤ) d)

noncomputable def oscDensityR (h M : ℕ) (ζ : ℂ) (x : ZMod (2 * h)) : Bosonize.A08.OscAlgebra M :=
  (((2 * h : ℕ) : ℂ)⁻¹) • ∑ i : Fin M,
    (Bosonize.A06.latticeCharacter h ζ (-((i.val + 1 : ℕ) : ℤ)) x • Bosonize.A08.creatorGen M .right i +
     Bosonize.A06.latticeCharacter h ζ ((i.val + 1 : ℕ) : ℤ) x • Bosonize.A08.annihilatorGen M .right i)

noncomputable def orderedDensityCorrelation (h M : ℕ) (ζ : ℂ) (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) : ℂ :=
  Bosonize.A08.omegaP M hp (oscDensityR h M ζ x * oscDensityR h M ζ y)

def freePair : Bosonize.Ch18.HyperbolicPair :=
  ⟨1, 0, by norm_num⟩

theorem omegaP_creator_annihilator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.annihilatorGen M .right j) =
      if i = j then ((i.val + 1 : ℕ) : ℂ) * (hp.s : ℂ) ^ 2 else 0 := by sorry

theorem omegaP_annihilator_creator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.annihilatorGen M .right i * Bosonize.A08.creatorGen M .right j) =
      if i = j then ((i.val + 1 : ℕ) : ℂ) * (hp.c : ℂ) ^ 2 else 0 := by sorry

theorem omegaP_creator_creator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.creatorGen M .right j) = 0 := by sorry

theorem omegaP_annihilator_annihilator_right (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.annihilatorGen M .right i * Bosonize.A08.annihilatorGen M .right j) = 0 := by sorry

theorem omegaP_cross_creator_creator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.creatorGen M .left j) =
      if i = j then -(((i.val + 1 : ℕ) : ℂ) * (hp.c : ℂ) * (hp.s : ℂ)) else 0 := by sorry

theorem omegaP_cross_annihilator_annihilator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.annihilatorGen M .right i * Bosonize.A08.annihilatorGen M .left j) =
      if i = j then -(((i.val + 1 : ℕ) : ℂ) * (hp.c : ℂ) * (hp.s : ℂ)) else 0 := by sorry

theorem omegaP_cross_creator_annihilator (M : ℕ) (hp : Bosonize.Ch18.HyperbolicPair) (i j : Fin M) :
    Bosonize.A08.omegaP M hp (Bosonize.A08.creatorGen M .right i * Bosonize.A08.annihilatorGen M .left j) = 0 := by sorry

theorem ordered_density_kernel (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x y =
      densityKernel h M ζ (hp.c ^ 2) (hp.s ^ 2) ((x.val : ℤ) - (y.val : ℤ)) := by sorry

theorem ordered_density_kernel_lattice (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 * h)) (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x y =
      (((2 * h : ℕ) : ℂ)⁻¹) ^ 2 * ∑ m ∈ Finset.Icc 1 M, (m : ℂ) *
        ((hp.s : ℂ) ^ 2 * Bosonize.A06.latticeCharacter h ζ (-(m : ℤ)) (x - y) +
         (hp.c : ℂ) ^ 2 * Bosonize.A06.latticeCharacter h ζ (m : ℤ) (x - y)) := by sorry

theorem density_commutator_expectation (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x y - orderedDensityCorrelation h M ζ hp y x =
      densityKernel h M ζ 1 (-1) ((x.val : ℤ) - (y.val : ℤ)) := by sorry

theorem symmetrized_density_kernel (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x y : ZMod (2 * h)) :
    (orderedDensityCorrelation h M ζ hp x y + orderedDensityCorrelation h M ζ hp y x) / 2 =
      densityKernel h M ζ
        ((Bosonize.Ch18.luttingerG hp + (Bosonize.Ch18.luttingerG hp)⁻¹) / 4)
        ((Bosonize.Ch18.luttingerG hp + (Bosonize.Ch18.luttingerG hp)⁻¹) / 4)
        ((x.val : ℤ) - (y.val : ℤ)) := by sorry

theorem s_sq_eq_luttinger (hp : Bosonize.Ch18.HyperbolicPair) :
    hp.s ^ 2 = (Bosonize.Ch18.luttingerG hp + (Bosonize.Ch18.luttingerG hp)⁻¹ - 2) / 4 := by sorry

theorem c_sq_eq_luttinger (hp : Bosonize.Ch18.HyperbolicPair) :
    hp.c ^ 2 = (Bosonize.Ch18.luttingerG hp + (Bosonize.Ch18.luttingerG hp)⁻¹ + 2) / 4 := by sorry

theorem density_kernel_diagonal (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x x =
      ((((hp.c ^ 2 + hp.s ^ 2) * ((M * (M + 1) : ℝ) / 2) / ((2 * h : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) := by sorry

theorem density_kernel_diagonal_pos (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (x : ZMod (2 * h))
    (hh : 0 < h) (hM : 1 ≤ M) :
    0 < (orderedDensityCorrelation h M ζ hp x x).re := by sorry

theorem ordered_density_free (h M : ℕ) [NeZero (2 * h)] (ζ : ℂ) (hζ : ζ ≠ 0)
    (hp : Bosonize.Ch18.HyperbolicPair) (hs : hp.s = 0) (x y : ZMod (2 * h)) :
    orderedDensityCorrelation h M ζ hp x y =
      densityKernel h M ζ 1 0 ((x.val : ℤ) - (y.val : ℤ)) := by sorry

section Fock

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

noncomputable def fockDensityR (h M : ℕ) (ζ : ℂ) (branches : Bosonize.A06.Branches σ) (x : ZMod (2 * h)) :
    Bosonize.A05.Operators σ h :=
  (((2 * h : ℕ) : ℂ)⁻¹) • ∑ m ∈ Finset.Icc 1 M,
    (Bosonize.A06.latticeCharacter h ζ (-(m : ℤ)) x • Bosonize.A05.rho h branches.rightSpecies (m : ℤ) +
     Bosonize.A06.latticeCharacter h ζ (m : ℤ) x • Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)))

theorem ground_lowering_raising (h M : ℕ) (hh : 0 < h) (m n : ℕ)
    (hm : 1 ≤ m) (hmM : m ≤ M) (hnM : n ≤ M)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M 0 Ns branches.rightSpecies) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) *
         Bosonize.A05.rho h branches.rightSpecies (n : ℤ)) =
      if m = n then (m : ℂ) else 0 := by sorry

theorem ground_raising_lowering (h : ℕ) (hh : 0 < h) (m n : ℕ) (hn : 1 ≤ n)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (m : ℤ) *
         Bosonize.A05.rho h branches.rightSpecies (-(n : ℤ))) = 0 := by sorry

theorem ground_raising_raising (h : ℕ) (hh : 0 < h) (m n : ℕ) (hm : 1 ≤ m)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (m : ℤ) *
         Bosonize.A05.rho h branches.rightSpecies (n : ℤ)) = 0 := by sorry

theorem ground_lowering_lowering (h : ℕ) (hh : 0 < h) (m n : ℕ) (hn : 1 ≤ n)
    (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A05.rho h branches.rightSpecies (-(m : ℤ)) *
         Bosonize.A05.rho h branches.rightSpecies (-(n : ℤ))) = 0 := by sorry

theorem excited_ket_norm_sq (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M)
    (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M 0 Ns (Bosonize.A06.speciesOf branches η)) :
    ‖Bosonize.Ch16.excitedKet h Ns branches η m‖ ^ 2 = (m : ℝ) := by sorry

theorem ground_dressed_number (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hp : Bosonize.Ch18.HyperbolicPair)
    (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.branchMargins h M 0 Ns branches) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η *
         Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η) =
      (m : ℂ) * (hp.s : ℂ) ^ 2 := by sorry

theorem ground_dressed_reverse (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hp : Bosonize.Ch18.HyperbolicPair)
    (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.branchMargins h M 0 Ns branches) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η *
         Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η) =
      (m : ℂ) * (hp.c : ℂ) ^ 2 := by sorry

theorem ground_not_dressed_vacuum (h M m : ℕ) (hh : 0 < h) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hp : Bosonize.Ch18.HyperbolicPair) (hs : hp.s ≠ 0)
    (branches : Bosonize.A06.Branches σ) (η : Bosonize.A06.Orientation) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.branchMargins h M 0 Ns branches) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (Bosonize.A07Interactions.bogoliubovCreator h m hp.c hp.s branches η *
         Bosonize.A07Interactions.bogoliubovAnnihilator h m hp.c hp.s branches η) ≠ 0 := by sorry

theorem fock_ground_density_kernel (h M : ℕ) [NeZero (2 * h)] (hh : 0 < h)
    (ζ : ℂ) (hζ : ζ ≠ 0) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M 0 Ns branches.rightSpecies)
    (x y : ZMod (2 * h)) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (fockDensityR h M ζ branches x * fockDensityR h M ζ branches y) =
      densityKernel h M ζ 1 0 ((x.val : ℤ) - (y.val : ℤ)) := by sorry

/-- The Fock ground expectation matches the abstract free state correlation value.
This is a scalar equality at s = 0 only; it is not an identification of states
or representations. -/
theorem fock_ground_matches_free_state (h M : ℕ) [NeZero (2 * h)] (hh : 0 < h)
    (ζ : ℂ) (hζ : ζ ≠ 0) (branches : Bosonize.A06.Branches σ) (Ns : σ → ℤ)
    (hN : Bosonize.A05.admissible h Ns)
    (hmargin : Bosonize.A06.marginAt h M 0 Ns branches.rightSpecies)
    (x y : ZMod (2 * h)) :
    Bosonize.A08.vectorState h (Bosonize.A05.groundKet h Ns)
        (fockDensityR h M ζ branches x * fockDensityR h M ζ branches y) =
      orderedDensityCorrelation h M ζ freePair x y := by sorry

end Fock

theorem concrete_correlation_witness :
    Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair
        (Bosonize.A08.creatorGen 2 .right (1 : Fin 2) *
         Bosonize.A08.annihilatorGen 2 .right (1 : Fin 2)) = (9 : ℂ) / 8 ∧
      Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair
        (Bosonize.A08.annihilatorGen 2 .right (1 : Fin 2) *
         Bosonize.A08.creatorGen 2 .right (1 : Fin 2)) = (25 : ℂ) / 8 ∧
      Bosonize.A08.omegaP 2 Bosonize.Ch18.concretePair
        (Bosonize.A08.creatorGen 2 .right (1 : Fin 2) *
         Bosonize.A08.creatorGen 2 .left (1 : Fin 2)) = -(15 : ℂ) / 8 ∧
      orderedDensityCorrelation 8 2 (Bosonize.A01.canonicalRoot (2 * 8))
        Bosonize.Ch18.concretePair 0 0 = (51 : ℂ) / 2048 ∧
      Bosonize.A06.branchMargins 8 2 0 Bosonize.Ch18.concreteNs Bosonize.Ch18.concreteBranches ∧
      Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
        (Bosonize.A05.rho 8 0 (-2) * Bosonize.A05.rho 8 0 2) = 2 ∧
      Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
        (Bosonize.A07Interactions.bogoliubovCreator 8 2
          Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
          Bosonize.Ch18.concreteBranches .right *
         Bosonize.A07Interactions.bogoliubovAnnihilator 8 2
          Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
          Bosonize.Ch18.concreteBranches .right) = (9 : ℂ) / 8 ∧
      Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
        (Bosonize.A07Interactions.bogoliubovCreator 8 2
          Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
          Bosonize.Ch18.concreteBranches .right *
         Bosonize.A07Interactions.bogoliubovAnnihilator 8 2
          Bosonize.Ch18.concretePair.c Bosonize.Ch18.concretePair.s
          Bosonize.Ch18.concreteBranches .right) ≠ 0 ∧
      Bosonize.A08.vectorState 8 (Bosonize.A05.groundKet 8 Bosonize.Ch18.concreteNs)
        (fockDensityR 8 2 (Bosonize.A01.canonicalRoot (2 * 8)) Bosonize.Ch18.concreteBranches 0 *
         fockDensityR 8 2 (Bosonize.A01.canonicalRoot (2 * 8)) Bosonize.Ch18.concreteBranches 0) =
        (3 : ℂ) / 256 := by sorry

end Bosonize.Ch19
