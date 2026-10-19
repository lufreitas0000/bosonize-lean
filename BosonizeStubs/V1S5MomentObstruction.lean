import Bosonize.Core.V1S1OrderedWick
import Bosonize.Core.A05MultiSpecies
import BosonizeStubs.V1S5FiniteGroundState

/-! S5 staging: raw-current dictionary, ambient powers and final compression.
The rightmost lowering acts first. No reverse-order vanishing is asserted. -/
@[expose] public section
namespace Bosonize.V1S5
open scoped BigOperators

theorem repeated_lowering_zero {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h K m q : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ)
    (hbound : K < q * m) (v : A05.FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) :
    (A05.rho h ν (-(m : ℤ)) ^ q) v = 0 := by sorry

theorem finite_normal_moment_zero {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h K m q : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ)
    (hbound : K < q * m) (v : A05.FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) :
    inner ℂ v ((A05.rho h ν (m : ℤ) ^ q *
      A05.rho h ν (-(m : ℤ)) ^ q) v) = 0 := by sorry

theorem compressed_lowering_zero {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h K m q : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ)
    (hbound : K < q * m) :
    compression (E := Budget h Ns K) (inclusion h Ns K)
      (A05.rho h ν (-(m : ℤ))) ^ q = 0 := by sorry

theorem compressed_normal_moment_zero {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h K m q : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ)
    (hbound : K < q * m) (v : Budget h Ns K) :
    vectorState (E := Budget h Ns K) v
      ((compression (E := Budget h Ns K) (inclusion h Ns K)
        (A05.rho h ν (m : ℤ))) ^ q *
       (compression (E := Budget h Ns K) (inclusion h Ns K)
        (A05.rho h ν (-(m : ℤ)))) ^ q) = 0 := by sorry

theorem oscillator_normal_moment (M : ℕ) (hp : Ch18.HyperbolicPair)
    (ν : A06.Orientation) (i : Fin M) (q : ℕ) :
    A08.omegaP M hp (A08.creatorGen M ν i ^ q * A08.annihilatorGen M ν i ^ q) =
      (q.factorial : ℂ) * (((i.val + 1 : ℕ) : ℂ) * (hp.s : ℂ) ^ 2) ^ q := by sorry

theorem raw_dictionary_obstruction {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h K M q : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (species : A06.Orientation → σ) (ν : A06.Orientation) (i : Fin M)
    (hp : Ch18.HyperbolicPair) (hs : hp.s ≠ 0) (hbound : K < q * (i.val + 1))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    inner ℂ v ((A05.rho h (species ν) ((i.val + 1 : ℕ) : ℤ) ^ q *
      A05.rho h (species ν) (-((i.val + 1 : ℕ) : ℤ)) ^ q) v) ≠
      A08.omegaP M hp (A08.creatorGen M ν i ^ q * A08.annihilatorGen M ν i ^ q) := by sorry

theorem raw_obstruction_witness :
    A05.groundKet 8 (fun _ : Fin 2 => (0 : ℤ)) ∈
      A05.jointBudget 8 (fun _ : Fin 2 => (0 : ℤ)) 2 ∧
    A05.groundKet 8 (fun _ : Fin 2 => (0 : ℤ)) ≠ 0 ∧
    inner ℂ (A05.groundKet 8 (fun _ : Fin 2 => (0 : ℤ)))
      ((A05.rho 8 (0 : Fin 2) 1 ^ 3 * A05.rho 8 (0 : Fin 2) (-1) ^ 3)
        (A05.groundKet 8 (fun _ : Fin 2 => (0 : ℤ)))) ≠
      A08.omegaP 1 Ch18.concretePair
        (A08.creatorGen 1 .right 0 ^ 3 * A08.annihilatorGen 1 .right 0 ^ 3) := by sorry

theorem ground_state_raw_obstruction {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h K M q : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (branches : A06.Branches σ) (vF g4 g2 mu : ℝ)
    (g : GroundVector (E := Budget h Ns K)
      (budgetHamiltonian h M K Ns vF g4 g2 mu branches))
    (ν : A06.Orientation) (i : Fin M) (hp : Ch18.HyperbolicPair)
    (hs : hp.s ≠ 0) (hbound : K < q * (i.val + 1)) :
    extendedState (E := Budget h Ns K) (inclusion h Ns K) g.ket
      (A05.rho h (A06.speciesOf branches ν) ((i.val + 1 : ℕ) : ℤ) ^ q *
       A05.rho h (A06.speciesOf branches ν) (-((i.val + 1 : ℕ) : ℤ)) ^ q) ≠
      A08.omegaP M hp (A08.creatorGen M ν i ^ q * A08.annihilatorGen M ν i ^ q) := by sorry

end Bosonize.V1S5
