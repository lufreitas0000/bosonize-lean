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
    (A05.rho h ν (-(m : ℤ)) ^ q) v = 0 := by
  induction q generalizing K v with
  | zero => simp at hbound
  | succ q ih =>
    rw [pow_succ, Module.End.mul_apply]
    by_cases hm : K < m
    · rw [A05.rho_lowering_budget_zero h hh ν m K hm Ns v hv, map_zero]
    · have hmk : m ≤ K := by omega
      have hout : A05.rho h ν (-(m : ℤ)) v ∈ A05.jointBudget h Ns (K - m) := by
        have hb := A05.rho_budget_map h ν (-(m : ℤ)) Ns K v hv
        simpa only [A05.jointBudget, Nat.cast_sub hmk, sub_eq_add_neg] using hb
      apply ih (K - m) _ _ hout
      rw [Nat.succ_mul] at hbound
      omega

theorem finite_normal_moment_zero {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h K m q : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ)
    (hbound : K < q * m) (v : A05.FockSpace σ h)
    (hv : v ∈ A05.jointBudget h Ns K) :
    inner ℂ v ((A05.rho h ν (m : ℤ) ^ q *
      A05.rho h ν (-(m : ℤ)) ^ q) v) = 0 := by
  rw [Module.End.mul_apply, repeated_lowering_zero h K m q hh Ns ν hbound v hv]
  simp

theorem compressed_lowering_zero {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h K m q : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ)
    (hbound : K < q * m) :
    compression (E := Budget h Ns K) (inclusion h Ns K)
      (A05.rho h ν (-(m : ℤ))) ^ q = 0 := by
  let A := A05.rho h ν (-(m : ℤ))
  let i := inclusion h Ns K
  let T := compression (E := Budget h Ns K) i A
  have hmem (v : Budget h Ns K) : A (i v) ∈ A05.jointBudget h Ns K := by
    have hv := A05.rho_budget_map h ν (-(m : ℤ)) Ns K (i v) v.property
    apply A03.coordinate_space_mono _ _ ?_ hv
    intro S hS
    exact ⟨hS.1, le_trans hS.2 (by omega)⟩
  have hT (v : Budget h Ns K) : i (T v) = A (i v) := by
    change ((inclusion h Ns K).comp
      (LinearMap.adjoint (𝕜 := ℂ) (E := Budget h Ns K)
        (F := A05.FockSpace σ h) (inclusion h Ns K))) (A (i v)) = _
    rw [inclusion_projection]
    exact (A03.projection_fixed_iff _ _).mpr (hmem v)
  have hp (n : ℕ) (v : Budget h Ns K) : i ((T ^ n) v) = (A ^ n) (i v) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Module.End.mul_apply, hT, ih,
        pow_succ', Module.End.mul_apply]
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change i ((T ^ q) v) = 0
  rw [hp]
  exact repeated_lowering_zero h K m q hh Ns ν hbound (i v) v.property

theorem compressed_normal_moment_zero {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h K m q : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (ν : σ)
    (hbound : K < q * m) (v : Budget h Ns K) :
    vectorState (E := Budget h Ns K) v
      ((compression (E := Budget h Ns K) (inclusion h Ns K)
        (A05.rho h ν (m : ℤ))) ^ q *
       (compression (E := Budget h Ns K) (inclusion h Ns K)
        (A05.rho h ν (-(m : ℤ)))) ^ q) = 0 := by
  rw [compressed_lowering_zero h K m q hh Ns ν hbound, mul_zero]
  simp [vectorState]

theorem oscillator_normal_moment (M : ℕ) (hp : Ch18.HyperbolicPair)
    (ν : A06.Orientation) (i : Fin M) (q : ℕ) :
    A08.omegaP M hp (A08.creatorGen M ν i ^ q * A08.annihilatorGen M ν i ^ q) =
      (q.factorial : ℂ) * (((i.val + 1 : ℕ) : ℂ) * (hp.s : ℂ) ^ 2) ^ q := by
  classical
  let p : A08.OscMode M := (A07Interactions.oppositeOrientation ν, i)
  let T := A08.oscRep M (A08.bogoliubovMap M hp.c (-hp.s) (A08.annihilatorGen M ν i))
  have hne : (ν,i) ≠ p := by
    cases ν <;> simp [p, A07Interactions.oppositeOrientation]
  have hstep (n : ℕ) : T (MvPolynomial.X p ^ n) =
      (-hp.s : ℂ) • MvPolynomial.X p ^ (n+1) := by
    dsimp [T]
    rw [A08.annihilatorGen, A08.bogoliubovMap, FreeAlgebra.lift_ι_apply,
      map_add, map_smul, map_smul]
    simp only [A08.oscRep, FreeAlgebra.lift_ι_apply, Complex.ofReal_neg]
    change (hp.c : ℂ) • (A08.oscAnnihilation M (ν,i) (MvPolynomial.X p ^ n)) +
      (-hp.s : ℂ) • (A08.oscCreation M p (MvPolynomial.X p ^ n)) = _
    simp [A08.oscAnnihilation, A08.oscCreation, hne,
      pow_succ, mul_comm]

  have hpow (n : ℕ) : (T ^ n) 1 = (-hp.s : ℂ) ^ n • MvPolynomial.X p ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hstep, smul_smul]
      rw [pow_succ (-hp.s : ℂ)]
  have hd := A08.bogoliubovMap_word_adjoint M hp.c (-hp.s)
    (List.replicate q (false, (ν,i))) 1 ((T ^ q) 1)
  have hpair : A08.omegaP M hp
      (A08.creatorGen M ν i ^ q * A08.annihilatorGen M ν i ^ q) =
      A08.oscPairing M ((T ^ q) 1) ((T ^ q) 1) := by
    change A08.omega0 M (A08.bogoliubovMap M hp.c (-hp.s) _) = _
    rw [A08.omega0_eq_pairing]
    simpa only [A08.wordDagger, List.map_replicate, List.reverse_replicate,
      A08.wordElement, List.prod_replicate, Bool.not_false, map_mul, map_pow,
      Module.End.mul_apply, A08.creatorGen, A08.annihilatorGen, T] using hd
  rw [hpair, hpow]
  have hX : MvPolynomial.X p ^ q = MvPolynomial.monomial (Finsupp.single p q) (1 : ℂ) := by
    simp [MvPolynomial.X_pow_eq_monomial]
  rw [hX]
  rw [MvPolynomial.smul_monomial]
  simp only [smul_eq_mul, mul_one]
  have hmono (a : ℂ) (r : A08.OscMode M →₀ ℕ) :
      A08.oscPairing M (MvPolynomial.monomial r a) (MvPolynomial.monomial r a) =
        star a * (A08.oscMonomialNorm r : ℂ) * a := by
    by_cases ha : a = 0
    · simp [ha, A08.oscPairing]
    · simp [A08.oscPairing, MvPolynomial.lcoeff_apply, ha]
  rw [hmono]
  have hs : star (-hp.s : ℂ) = (-hp.s : ℂ) := by simp
  simp only [A08.oscMonomialNorm, Finsupp.prod_single_index, pow_zero,
    Nat.factorial_zero, mul_one, Nat.cast_mul, Nat.cast_pow,
    star_pow, hs, A08.oscWeight, p]
  have he : (-hp.s : ℂ) ^ q * (-hp.s : ℂ) ^ q = ((hp.s : ℂ) ^ 2) ^ q := by
    rw [← mul_pow]
    congr 1
    ring
  rw [mul_pow]
  linear_combination (((i.val + 1 : ℕ) : ℂ) ^ q * (q.factorial : ℂ)) * he

theorem raw_dictionary_obstruction {σ : Type*} [Fintype σ] [LinearOrder σ]
    (h K M q : ℕ) (hh : 0 < h) (Ns : σ → ℤ)
    (species : A06.Orientation → σ) (ν : A06.Orientation) (i : Fin M)
    (hp : Ch18.HyperbolicPair) (hs : hp.s ≠ 0) (hbound : K < q * (i.val + 1))
    (v : A05.FockSpace σ h) (hv : v ∈ A05.jointBudget h Ns K) :
    inner ℂ v ((A05.rho h (species ν) ((i.val + 1 : ℕ) : ℤ) ^ q *
      A05.rho h (species ν) (-((i.val + 1 : ℕ) : ℤ)) ^ q) v) ≠
      A08.omegaP M hp (A08.creatorGen M ν i ^ q * A08.annihilatorGen M ν i ^ q) := by
  rw [finite_normal_moment_zero h K (i.val + 1) q hh Ns (species ν) hbound v hv,
    oscillator_normal_moment]
  apply Ne.symm
  apply mul_ne_zero
  · exact_mod_cast q.factorial_ne_zero
  · apply pow_ne_zero
    apply mul_ne_zero
    · exact_mod_cast (show i.val + 1 ≠ 0 by omega)
    · exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hs)

set_option maxRecDepth 2000 in
theorem raw_obstruction_witness :
    A05.groundKet 8 (fun _ : Fin 2 => (0 : ℤ)) ∈
      A05.jointBudget 8 (fun _ : Fin 2 => (0 : ℤ)) 2 ∧
    A05.groundKet 8 (fun _ : Fin 2 => (0 : ℤ)) ≠ 0 ∧
    inner ℂ (A05.groundKet 8 (fun _ : Fin 2 => (0 : ℤ)))
      ((A05.rho 8 (0 : Fin 2) 1 ^ 3 * A05.rho 8 (0 : Fin 2) (-1) ^ 3)
        (A05.groundKet 8 (fun _ : Fin 2 => (0 : ℤ)))) ≠
      A08.omegaP 1 Ch18.concretePair
        (A08.creatorGen 1 .right 0 ^ 3 * A08.annihilatorGen 1 .right 0 ^ 3) := by
  have hN : A05.admissible 8 (fun _ : Fin 2 => (0 : ℤ)) := by
    intro ν
    norm_num [Ch07.admissible]
  have hv := A05.ground_mem_budget 8 (by norm_num) _ hN 2
  refine ⟨hv, A05.ground_ne_zero _ _, ?_⟩
  have hz := finite_normal_moment_zero (σ := Fin 2) 8 2 1 3 (by norm_num)
    (fun _ : Fin 2 => (0 : ℤ)) (0 : Fin 2) (by norm_num)
    (A05.groundKet 8 (fun _ : Fin 2 => (0 : ℤ))) hv
  simp only [Nat.cast_one] at hz
  rw [hz]
  rw [oscillator_normal_moment]
  norm_num [Ch18.concretePair, Ch18.HyperbolicPair.ofParams,
    Ch18.concreteParams]


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
      A08.omegaP M hp (A08.creatorGen M ν i ^ q * A08.annihilatorGen M ν i ^ q) := by
  rw [extended_state_vector]
  exact raw_dictionary_obstruction h K M q hh Ns (A06.speciesOf branches) ν i hp hs hbound
    (inclusion h Ns K g.ket) g.ket.property

end Bosonize.V1S5
