import Bosonize

/-!
# Chapter 21: Spinful Fermions, Spin-Charge Separation, and Umklapp Obstructions

Constructive formalization of the 4-branch (`Fin 4`: `L↑, L↓, R↑, R↓`)
spinful Tomonaga-Luttinger model on `Bosonize`:
- `B1`: Spin-charge parity sublattice, ambient global edge-difference identities (`prop:ch21-global-edge`)
  and mixed cross-chirality commutation, raw charge/spin current Schwinger commutators (`2m`),
  spin-charge Kac-Moody commutation, and charge-sector orthogonality.
- `B3`: Two-channel spin-singlet pairing (`Ch20.orderSC`) orthogonal sector split,
  reuse of `Ch20.projected_sc_residual`, and the combined orthogonal-sum codomain
  `W = V_{t,B} ⊕ V_{t,A}` projection theorem (`thm:ch21-pair-projected`, Eq. (21.7)).
- `B2`: Real-space Umklapp operator `umklappOp`, exact charge/spin/chiral shifts `(+1,+1,-1,-1)`,
  self-adjointness, commutator charge shifts, and fixed-charge sector diagonal vanishing.
- `B4`: Concrete zero-charge witness state `umklappZeroChargeWitness`, exact CAR
  matrix-element evaluation `umklapp_zero_charge_witness_coeff` (`-g_U / (2h)^2`),
  derived `h = 2` (`-g_U / 16`) & `h = 1` (`-g_U / 4`) evaluations, constructive
  non-invariance of any zero-charge budget, and concrete `h = 2` witnesses for
  `ex:ch21-pair-sign` (`±1/4`), `ex:ch21-pair-residual` (`-i/4`), and
  `ex:ch21-u-inward-only` (Pauli-blocked inward-only `g_U / 16` without box leakage).
-/

namespace Bosonize.Ch21

open scoped BigOperators ComplexConjugate

noncomputable local instance localModeLinearOrderCh21 (h : ℕ) :
    LinearOrder (A05.Mode (Fin 4) h) := A05.speciesOrder h
noncomputable local instance localModeLTCh21 (h : ℕ) :
    LT (A05.Mode (Fin 4) h) := (A05.speciesOrder h).toLT
noncomputable local instance localModeLECh21 (h : ℕ) :
    LE (A05.Mode (Fin 4) h) := (A05.speciesOrder h).toLE
noncomputable local instance localModeDecidableEqCh21 (h : ℕ) :
    DecidableEq (A05.Mode (Fin 4) h) := A05.localModeDecidableEq h

/-! ## 1. Canonical Four-Branch Carrier & Parity Sublattice (`A1`, `B1`) -/

/-- Canonical 4-branch index order: `0 = L↑`, `1 = L↓`, `2 = R↑`, `3 = R↓`. -/
abbrev SpinBranch := Fin 4

def brLUp : SpinBranch := 0
def brLDown : SpinBranch := 1
def brRUp : SpinBranch := 2
def brRDown : SpinBranch := 3

lemma brLUp_ne_brLDown : brLUp ≠ brLDown := by decide
lemma brLUp_ne_brRUp : brLUp ≠ brRUp := by decide
lemma brLUp_ne_brRDown : brLUp ≠ brRDown := by decide
lemma brLDown_ne_brRUp : brLDown ≠ brRUp := by decide
lemma brLDown_ne_brRDown : brLDown ≠ brRDown := by decide
lemma brRUp_ne_brRDown : brRUp ≠ brRDown := by decide

/-- Four macroscopic spin-charge integer labels `(Q_c, Q_s, J_c, J_s)`. -/
structure SpinChargeTuple where
  qc : ℤ
  qs : ℤ
  jc : ℤ
  js : ℤ
  deriving DecidableEq, Repr

/-- Map per-branch relative charges `(N_L↑, N_L↓, N_R↑, N_R↓)` to `(Q_c, Q_s, J_c, J_s)`. -/
def branchesToSpinCharge (Ns : SpinBranch → ℤ) : SpinChargeTuple where
  qc := Ns brLUp + Ns brLDown + Ns brRUp + Ns brRDown
  qs := (Ns brLUp + Ns brRUp) - (Ns brLDown + Ns brRDown)
  jc := (Ns brRUp + Ns brRDown) - (Ns brLUp + Ns brLDown)
  js := (Ns brRUp - Ns brRDown) - (Ns brLUp - Ns brLDown)

/-- Exact mod-4 parity sublattice characterizing integer `(N_L↑, N_L↓, N_R↑, N_R↓)`. -/
def SpinChargeSublattice (q : SpinChargeTuple) : Prop :=
  (q.qc + q.qs - q.jc - q.js) % 4 = 0 ∧
  (q.qc - q.qs - q.jc + q.js) % 4 = 0 ∧
  (q.qc + q.qs + q.jc + q.js) % 4 = 0 ∧
  (q.qc - q.qs + q.jc - q.js) % 4 = 0

/-- Inverse branch charges reconstructed on `SpinChargeSublattice`. -/
def spinChargeToBranches (q : SpinChargeTuple) : SpinBranch → ℤ
  | ⟨0, _⟩ => (q.qc + q.qs - q.jc - q.js) / 4
  | ⟨1, _⟩ => (q.qc - q.qs - q.jc + q.js) / 4
  | ⟨2, _⟩ => (q.qc + q.qs + q.jc + q.js) / 4
  | ⟨3, _⟩ => (q.qc - q.qs + q.jc - q.js) / 4

lemma branchesToSpinCharge_mem_sublattice (Ns : SpinBranch → ℤ) :
    SpinChargeSublattice (branchesToSpinCharge Ns) := by
  simp only [SpinChargeSublattice, branchesToSpinCharge]
  omega

lemma spinCharge_left_inv (Ns : SpinBranch → ℤ) (ν : SpinBranch) :
    spinChargeToBranches (branchesToSpinCharge Ns) ν = Ns ν := by
  fin_cases ν <;> simp [spinChargeToBranches, branchesToSpinCharge, brLUp, brLDown, brRUp, brRDown] <;>
    omega

lemma spinCharge_right_inv (q : SpinChargeTuple) (hq : SpinChargeSublattice q) :
    branchesToSpinCharge (spinChargeToBranches q) = q := by
  rcases q with ⟨qc, qs, jc, js⟩
  rcases hq with ⟨h0, h1, h2, h3⟩
  simp only [branchesToSpinCharge, spinChargeToBranches, brLUp, brLDown, brRUp, brRDown]
  congr 1 <;> dsimp at h0 h1 h2 h3 <;> omega

/-- Per-chirality `(N_↑, N_↓) ↔ (Q_c, Q_s)` parity sublattice `Q_c + Q_s ≡ 0 [mod 2]`. -/
def ChiralSpinChargeParity (qc qs : ℤ) : Prop := (qc + qs) % 2 = 0

lemma chiral_spinCharge_recover (nUp nDown : ℤ) :
    let qc := nUp + nDown
    let qs := nUp - nDown
    ChiralSpinChargeParity qc qs ∧ (qc + qs) / 2 = nUp ∧ (qc - qs) / 2 = nDown := by
  dsimp [ChiralSpinChargeParity]
  omega

/-! ## 2. Sector Orthogonality & Spin-Charge Observables (`B1`) -/

/-- Exact charge-sector coordinate subspace `{S | ∀ ν, relativeCharge S ν = Ns ν}`. -/
noncomputable def chargeSector (h : ℕ) (Ns : SpinBranch → ℤ) :
    Submodule ℂ (A05.FockSpace SpinBranch h) :=
  @A03.coordinateSpace (A05.Mode SpinBranch h) _ instDecidableEqProd
    {S | ∀ ν, Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) = Ns ν}

lemma jointBudget_le_chargeSector (h : ℕ) (Ns : SpinBranch → ℤ) (K : ℕ) :
    A05.jointBudget h Ns K ≤ chargeSector h Ns := by
  unfold A05.jointBudget Ch07.speciesBudget chargeSector
  exact @A03.coordinate_space_mono (A05.Mode SpinBranch h) _ instDecidableEqProd
    _ _ (fun _ hS => hS.1)

/-- Any two distinct species-charge vectors define orthogonal charge sectors. -/
lemma distinct_charge_sectors_orthogonal (h : ℕ)
    (Ns₁ Ns₂ : SpinBranch → ℤ) (hne : Ns₁ ≠ Ns₂)
    (u : A05.FockSpace SpinBranch h) (hu : u ∈ chargeSector h Ns₁)
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ chargeSector h Ns₂) :
    inner ℂ u v = 0 := by
  exact @A03.coordinate_space_disjoint (A05.Mode SpinBranch h) _ instDecidableEqProd _ _
    (by
      rw [Set.disjoint_left]
      intro S hS₁ hS₂
      apply hne
      funext ν
      exact (hS₁ ν).symm.trans (hS₂ ν))
    u hu v hv

/-- Any two distinct species-charge vectors define orthogonal joint Fock budgets. -/
lemma distinct_charge_budgets_orthogonal (h : ℕ)
    (Ns₁ Ns₂ : SpinBranch → ℤ) (hne : Ns₁ ≠ Ns₂) (K₁ K₂ : ℕ)
    (u : A05.FockSpace SpinBranch h) (hu : u ∈ A05.jointBudget h Ns₁ K₁)
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ A05.jointBudget h Ns₂ K₂) :
    inner ℂ u v = 0 :=
  distinct_charge_sectors_orthogonal h Ns₁ Ns₂ hne u
    (jointBudget_le_chargeSector h Ns₁ K₁ hu) v (jointBudget_le_chargeSector h Ns₂ K₂ hv)

lemma charge_observable_self_adjoint (h : ℕ) (ν : SpinBranch) :
    LinearMap.adjoint (A05.chargeObservable h ν) = A05.chargeObservable h ν := by
  unfold A05.chargeObservable
  rw [A03.diagonal_adjoint]
  congr 1
  funext S
  simp

private lemma ket_chargeObservable (h : ℕ) (ν : SpinBranch)
    (S : A02.Occupation (A05.Mode SpinBranch h)) :
    A05.chargeObservable h ν (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) =
      (Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) : ℂ) •
        @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S := by
  unfold A05.chargeObservable
  exact @A03.diagonal_ket (A05.Mode SpinBranch h) _ instDecidableEqProd _ S

/-- Characterization of `chargeSector h Ns` as joint eigenspace of `A05.chargeObservable h ν`. -/
lemma mem_chargeSector_iff_eigen (h : ℕ) (Ns : SpinBranch → ℤ)
    (v : A05.FockSpace SpinBranch h) :
    v ∈ chargeSector h Ns ↔ ∀ ν, A05.chargeObservable h ν v = (Ns ν : ℂ) • v := by
  constructor
  · intro hv ν
    rw [chargeSector] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨S, hS, rfl⟩ := hx
      change A05.chargeObservable h ν
          (@A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S) =
        (Ns ν : ℂ) • @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S
      rw [ket_chargeObservable, hS ν]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
    | smul a x _ hx => rw [map_smul, hx, smul_comm]
  · intro hv
    rw [chargeSector, @A03.coordinate_space_support (A05.Mode SpinBranch h) _ instDecidableEqProd]
    intro S hS
    simp only [Set.mem_ofPred_eq, not_forall] at hS
    obtain ⟨ν, hν⟩ := hS
    let kS : A05.FockSpace SpinBranch h :=
      @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S
    have hinner1 : inner ℂ kS (A05.chargeObservable h ν v) =
        (Ns ν : ℂ) * inner ℂ kS v := by
      rw [hv ν, inner_smul_right]
    have hinner2 : inner ℂ kS (A05.chargeObservable h ν v) =
        (Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) : ℂ) * inner ℂ kS v := by
      have hadj : inner ℂ kS (A05.chargeObservable h ν v) =
          inner ℂ (A05.chargeObservable h ν kS) v := by
        calc
          inner ℂ kS (A05.chargeObservable h ν v)
              = inner ℂ (LinearMap.adjoint (A05.chargeObservable h ν) kS) v := by
                rw [LinearMap.adjoint_inner_left]
          _ = inner ℂ (A05.chargeObservable h ν kS) v := by
                rw [charge_observable_self_adjoint]
      rw [hadj]
      dsimp only [kS]
      rw [ket_chargeObservable h ν S, inner_smul_left]
      simp
    have hdiff : ((Ns ν : ℂ) - (Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) : ℂ)) *
        inner ℂ kS v = 0 := by
      rw [sub_mul, ← hinner1, ← hinner2, sub_self]
    have hneC : (Ns ν : ℂ) - (Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) : ℂ) ≠ 0 := by
      intro h0
      apply hν
      have hcast : (Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) : ℂ) = (Ns ν : ℂ) :=
        (sub_eq_zero.mp h0).symm
      exact Int.cast_injective hcast
    have hket0 : inner ℂ kS v = 0 := (mul_eq_zero.mp hdiff).resolve_left hneC
    have hcoord : inner ℂ kS v = @A02.coordinates (A05.Mode SpinBranch h) _ instDecidableEqProd v S := by
      dsimp only [kS]
      rw [@A02.fock_inner (A05.Mode SpinBranch h) _ instDecidableEqProd]
      simp [A02.ket_apply, A02.coordinates]
    exact hcoord.symm.trans hket0

/-- Any operator satisfying exact charge-commutator shifts maps `chargeSector Ns` to `Ns + q`. -/
lemma charge_commutator_maps_sector (h : ℕ) (A : A05.Operators SpinBranch h)
    (q : SpinBranch → ℤ)
    (hcomm : ∀ ν, A02.commutator (A05.chargeObservable h ν) A = (q ν : ℂ) • A)
    (Ns : SpinBranch → ℤ) (v : A05.FockSpace SpinBranch h) (hv : v ∈ chargeSector h Ns) :
    A v ∈ chargeSector h (fun ν => Ns ν + q ν) := by
  rw [mem_chargeSector_iff_eigen]
  intro ν
  have h1 := congrArg (fun T : A05.Operators SpinBranch h => T v) (hcomm ν)
  simp only [A02.commutator, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h1
  have hv_eig := (mem_chargeSector_iff_eigen h Ns v).mp hv ν
  rw [hv_eig, map_smul] at h1
  have hgoal : A05.chargeObservable h ν (A v) = (Ns ν : ℂ) • A v + (q ν : ℂ) • A v :=
    sub_eq_iff_eq_add'.mp h1
  rw [hgoal, Int.cast_add, add_smul]

/-- Total electric charge observable `Q_c = N_{L↑} + N_{L↓} + N_{R↑} + N_{R↓}`. -/
noncomputable def totalChargeObservable (h : ℕ) : A05.Operators SpinBranch h :=
  A05.chargeObservable h brLUp + A05.chargeObservable h brLDown +
    A05.chargeObservable h brRUp + A05.chargeObservable h brRDown

/-- Total spin observable `Q_s = (N_{L↑} + N_{R↑}) - (N_{L↓} + N_{R↓})`. -/
noncomputable def totalSpinObservable (h : ℕ) : A05.Operators SpinBranch h :=
  (A05.chargeObservable h brLUp + A05.chargeObservable h brRUp) -
    (A05.chargeObservable h brLDown + A05.chargeObservable h brRDown)

lemma totalChargeObservable_self_adjoint (h : ℕ) :
    LinearMap.adjoint (totalChargeObservable h) = totalChargeObservable h := by
  simp only [totalChargeObservable, map_add, charge_observable_self_adjoint]

lemma totalSpinObservable_self_adjoint (h : ℕ) :
    LinearMap.adjoint (totalSpinObservable h) = totalSpinObservable h := by
  simp only [totalSpinObservable, map_sub, map_add, charge_observable_self_adjoint]

lemma totalChargeObservable_budget (h : ℕ) (Ns : SpinBranch → ℤ) (K : ℕ)
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ A05.jointBudget h Ns K) :
    totalChargeObservable h v = ((branchesToSpinCharge Ns).qc : ℂ) • v := by
  have h0 := A05.charge_budget h brLUp Ns K v hv
  have h1 := A05.charge_budget h brLDown Ns K v hv
  have h2 := A05.charge_budget h brRUp Ns K v hv
  have h3 := A05.charge_budget h brRDown Ns K v hv
  simp only [totalChargeObservable, LinearMap.add_apply, h0, h1, h2, h3, branchesToSpinCharge,
    Int.cast_add]
  module

lemma totalSpinObservable_budget (h : ℕ) (Ns : SpinBranch → ℤ) (K : ℕ)
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ A05.jointBudget h Ns K) :
    totalSpinObservable h v = ((branchesToSpinCharge Ns).qs : ℂ) • v := by
  have h0 := A05.charge_budget h brLUp Ns K v hv
  have h1 := A05.charge_budget h brLDown Ns K v hv
  have h2 := A05.charge_budget h brRUp Ns K v hv
  have h3 := A05.charge_budget h brRDown Ns K v hv
  simp only [totalSpinObservable, LinearMap.sub_apply, LinearMap.add_apply, h0, h1, h2, h3,
    branchesToSpinCharge, Int.cast_sub, Int.cast_add]
  module

/-! ## 3. Raw Chiral Charge/Spin Currents (`2m` Schwinger Terms & Separation) (`B1`) -/

noncomputable def rhoChargeL (h : ℕ) (m : ℤ) : A05.Operators SpinBranch h :=
  A05.rho h brLUp m + A05.rho h brLDown m

noncomputable def rhoSpinL (h : ℕ) (m : ℤ) : A05.Operators SpinBranch h :=
  A05.rho h brLUp m - A05.rho h brLDown m

noncomputable def rhoChargeR (h : ℕ) (m : ℤ) : A05.Operators SpinBranch h :=
  A05.rho h brRUp m + A05.rho h brRDown m

noncomputable def rhoSpinR (h : ℕ) (m : ℤ) : A05.Operators SpinBranch h :=
  A05.rho h brRUp m - A05.rho h brRDown m

lemma rhoChargeL_adjoint (h : ℕ) (m : ℤ) :
    LinearMap.adjoint (rhoChargeL h m) = rhoChargeL h (-m) := by
  simp only [rhoChargeL, map_add, A05.rho_adjoint]

lemma rhoSpinL_adjoint (h : ℕ) (m : ℤ) :
    LinearMap.adjoint (rhoSpinL h m) = rhoSpinL h (-m) := by
  simp only [rhoSpinL, map_sub, A05.rho_adjoint]

lemma rhoChargeR_adjoint (h : ℕ) (m : ℤ) :
    LinearMap.adjoint (rhoChargeR h m) = rhoChargeR h (-m) := by
  simp only [rhoChargeR, map_add, A05.rho_adjoint]

lemma rhoSpinR_adjoint (h : ℕ) (m : ℤ) :
    LinearMap.adjoint (rhoSpinR h m) = rhoSpinR h (-m) := by
  simp only [rhoSpinR, map_sub, A05.rho_adjoint]

private lemma comm_add_left {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B C : Module.End ℂ V) :
    A02.commutator (A + B) C = A02.commutator A C + A02.commutator B C := by
  simp only [A02.commutator]; noncomm_ring

private lemma comm_sub_left {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B C : Module.End ℂ V) :
    A02.commutator (A - B) C = A02.commutator A C - A02.commutator B C := by
  simp only [A02.commutator]; noncomm_ring

private lemma comm_add_right {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B C : Module.End ℂ V) :
    A02.commutator A (B + C) = A02.commutator A B + A02.commutator A C := by
  simp only [A02.commutator]; noncomm_ring

private lemma comm_sub_right {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B C : Module.End ℂ V) :
    A02.commutator A (B - C) = A02.commutator A B - A02.commutator A C := by
  simp only [A02.commutator]; noncomm_ring

/-- Ambient finite-band current-commutator edge operator `E_{ν}(m, n) = [ρ_{ν,m}, ρ_{ν,n}]`. -/
noncomputable def edgeOp (h : ℕ) (ν : SpinBranch) (m n : ℤ) : A05.Operators SpinBranch h :=
  A02.commutator (A05.rho h ν m) (A05.rho h ν n)

/-- Global (unbudgeted) commutator expansion for same-chirality spin pairs `a ≠ b`. -/
private lemma pair_current_global_edge (h : ℕ) (a b : SpinBranch) (hab : a ≠ b) (m n : ℤ) :
    (A02.commutator (A05.rho h a m + A05.rho h b m) (A05.rho h a n - A05.rho h b n) =
        edgeOp h a m n - edgeOp h b m n) ∧
    (A02.commutator (A05.rho h a m + A05.rho h b m) (A05.rho h a n + A05.rho h b n) =
        edgeOp h a m n + edgeOp h b m n) ∧
    (A02.commutator (A05.rho h a m - A05.rho h b m) (A05.rho h a n - A05.rho h b n) =
        edgeOp h a m n + edgeOp h b m n) := by
  have cab := A05.rho_cross_commute h a b hab m n
  have cba := A05.rho_cross_commute h b a hab.symm m n
  refine ⟨?_, ?_, ?_⟩
  · rw [comm_add_left, comm_sub_right, comm_sub_right, cab, cba]
    simp only [edgeOp]
    abel
  · rw [comm_add_left, comm_add_right, comm_add_right, cab, cba]
    simp only [add_zero, zero_add, edgeOp]
  · rw [comm_sub_left, comm_sub_right, comm_sub_right, cab, cba]
    simp only [sub_zero, zero_sub, sub_neg_eq_add, edgeOp]

lemma rhoChargeL_rhoSpinL_global_edge (h : ℕ) (m n : ℤ) :
    A02.commutator (rhoChargeL h m) (rhoSpinL h n) =
      edgeOp h brLUp m n - edgeOp h brLDown m n :=
  (pair_current_global_edge h brLUp brLDown brLUp_ne_brLDown m n).1

lemma rhoChargeL_global_edge (h : ℕ) (m n : ℤ) :
    A02.commutator (rhoChargeL h m) (rhoChargeL h n) =
      edgeOp h brLUp m n + edgeOp h brLDown m n :=
  (pair_current_global_edge h brLUp brLDown brLUp_ne_brLDown m n).2.1

lemma rhoSpinL_global_edge (h : ℕ) (m n : ℤ) :
    A02.commutator (rhoSpinL h m) (rhoSpinL h n) =
      edgeOp h brLUp m n + edgeOp h brLDown m n :=
  (pair_current_global_edge h brLUp brLDown brLUp_ne_brLDown m n).2.2

lemma rhoChargeL_eq_rhoSpinL_global_edge (h : ℕ) (m n : ℤ) :
    A02.commutator (rhoChargeL h m) (rhoChargeL h n) =
      A02.commutator (rhoSpinL h m) (rhoSpinL h n) := by
  rw [rhoChargeL_global_edge, rhoSpinL_global_edge]

lemma rhoChargeR_rhoSpinR_global_edge (h : ℕ) (m n : ℤ) :
    A02.commutator (rhoChargeR h m) (rhoSpinR h n) =
      edgeOp h brRUp m n - edgeOp h brRDown m n :=
  (pair_current_global_edge h brRUp brRDown brRUp_ne_brRDown m n).1

lemma rhoChargeR_global_edge (h : ℕ) (m n : ℤ) :
    A02.commutator (rhoChargeR h m) (rhoChargeR h n) =
      edgeOp h brRUp m n + edgeOp h brRDown m n :=
  (pair_current_global_edge h brRUp brRDown brRUp_ne_brRDown m n).2.1

lemma rhoSpinR_global_edge (h : ℕ) (m n : ℤ) :
    A02.commutator (rhoSpinR h m) (rhoSpinR h n) =
      edgeOp h brRUp m n + edgeOp h brRDown m n :=
  (pair_current_global_edge h brRUp brRDown brRUp_ne_brRDown m n).2.2

lemma rhoChargeR_eq_rhoSpinR_global_edge (h : ℕ) (m n : ℤ) :
    A02.commutator (rhoChargeR h m) (rhoChargeR h n) =
      A02.commutator (rhoSpinR h m) (rhoSpinR h n) := by
  rw [rhoChargeR_global_edge, rhoSpinR_global_edge]

/-- Helper expanding `[ρ_a ± ρ_b, ρ_a ±' ρ_b]` for distinct species `a ≠ b`. -/
private lemma pair_current_commutator_expand (h K : ℕ) (hh : 0 < h)
    (Ns : SpinBranch → ℤ) (a b : SpinBranch) (hab : a ≠ b) (m n : ℤ)
    (ha : |m| + |n| + (K : ℤ) + |Ns a| ≤ (h : ℤ))
    (hb : |m| + |n| + (K : ℤ) + |Ns b| ≤ (h : ℤ))
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ A05.jointBudget h Ns K) :
    (A02.commutator (A05.rho h a m + A05.rho h b m) (A05.rho h a n + A05.rho h b n) v =
        ((2 : ℂ) * Ch10.schwingerCoefficient m n) • v) ∧
    (A02.commutator (A05.rho h a m - A05.rho h b m) (A05.rho h a n - A05.rho h b n) v =
        ((2 : ℂ) * Ch10.schwingerCoefficient m n) • v) ∧
    (A02.commutator (A05.rho h a m + A05.rho h b m) (A05.rho h a n - A05.rho h b n) v = 0) := by
  have caa := A06.joint_signed_current_commutator h K hh Ns a m n ha v hv
  have cbb := A06.joint_signed_current_commutator h K hh Ns b m n hb v hv
  have cab := A05.rho_cross_commute h a b hab m n
  have cba := A05.rho_cross_commute h b a hab.symm m n
  refine ⟨?_, ?_, ?_⟩
  · rw [comm_add_left, comm_add_right, comm_add_right, cab, cba]
    simp only [add_zero, zero_add, LinearMap.add_apply, caa, cbb, two_mul, add_smul]
  · rw [comm_sub_left, comm_sub_right, comm_sub_right, cab, cba]
    simp only [sub_zero, zero_sub, sub_neg_eq_add, LinearMap.add_apply, caa, cbb, two_mul, add_smul]
  · rw [comm_add_left, comm_sub_right, comm_sub_right, cab, cba]
    simp only [sub_zero, zero_sub, LinearMap.add_apply, LinearMap.neg_apply, caa, cbb, add_neg_cancel]

lemma rhoChargeL_commutator (h K : ℕ) (hh : 0 < h) (Ns : SpinBranch → ℤ) (m n : ℤ)
    (hUp : |m| + |n| + (K : ℤ) + |Ns brLUp| ≤ (h : ℤ))
    (hDown : |m| + |n| + (K : ℤ) + |Ns brLDown| ≤ (h : ℤ))
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (rhoChargeL h m) (rhoChargeL h n) v =
      ((2 : ℂ) * Ch10.schwingerCoefficient m n) • v :=
  (pair_current_commutator_expand h K hh Ns brLUp brLDown brLUp_ne_brLDown m n hUp hDown v hv).1

lemma rhoSpinL_commutator (h K : ℕ) (hh : 0 < h) (Ns : SpinBranch → ℤ) (m n : ℤ)
    (hUp : |m| + |n| + (K : ℤ) + |Ns brLUp| ≤ (h : ℤ))
    (hDown : |m| + |n| + (K : ℤ) + |Ns brLDown| ≤ (h : ℤ))
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (rhoSpinL h m) (rhoSpinL h n) v =
      ((2 : ℂ) * Ch10.schwingerCoefficient m n) • v :=
  (pair_current_commutator_expand h K hh Ns brLUp brLDown brLUp_ne_brLDown m n hUp hDown v hv).2.1

lemma rhoChargeL_rhoSpinL_commutator (h K : ℕ) (hh : 0 < h) (Ns : SpinBranch → ℤ) (m n : ℤ)
    (hUp : |m| + |n| + (K : ℤ) + |Ns brLUp| ≤ (h : ℤ))
    (hDown : |m| + |n| + (K : ℤ) + |Ns brLDown| ≤ (h : ℤ))
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (rhoChargeL h m) (rhoSpinL h n) v = 0 :=
  (pair_current_commutator_expand h K hh Ns brLUp brLDown brLUp_ne_brLDown m n hUp hDown v hv).2.2

lemma rhoChargeR_commutator (h K : ℕ) (hh : 0 < h) (Ns : SpinBranch → ℤ) (m n : ℤ)
    (hUp : |m| + |n| + (K : ℤ) + |Ns brRUp| ≤ (h : ℤ))
    (hDown : |m| + |n| + (K : ℤ) + |Ns brRDown| ≤ (h : ℤ))
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (rhoChargeR h m) (rhoChargeR h n) v =
      ((2 : ℂ) * Ch10.schwingerCoefficient m n) • v :=
  (pair_current_commutator_expand h K hh Ns brRUp brRDown brRUp_ne_brRDown m n hUp hDown v hv).1

lemma rhoSpinR_commutator (h K : ℕ) (hh : 0 < h) (Ns : SpinBranch → ℤ) (m n : ℤ)
    (hUp : |m| + |n| + (K : ℤ) + |Ns brRUp| ≤ (h : ℤ))
    (hDown : |m| + |n| + (K : ℤ) + |Ns brRDown| ≤ (h : ℤ))
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (rhoSpinR h m) (rhoSpinR h n) v =
      ((2 : ℂ) * Ch10.schwingerCoefficient m n) • v :=
  (pair_current_commutator_expand h K hh Ns brRUp brRDown brRUp_ne_brRDown m n hUp hDown v hv).2.1

lemma rhoChargeR_rhoSpinR_commutator (h K : ℕ) (hh : 0 < h) (Ns : SpinBranch → ℤ) (m n : ℤ)
    (hUp : |m| + |n| + (K : ℤ) + |Ns brRUp| ≤ (h : ℤ))
    (hDown : |m| + |n| + (K : ℤ) + |Ns brRDown| ≤ (h : ℤ))
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ A05.jointBudget h Ns K) :
    A02.commutator (rhoChargeR h m) (rhoSpinR h n) v = 0 :=
  (pair_current_commutator_expand h K hh Ns brRUp brRDown brRUp_ne_brRDown m n hUp hDown v hv).2.2

lemma rhoChargeR_rhoChargeL_commute (h : ℕ) (m n : ℤ) :
    A02.commutator (rhoChargeR h m) (rhoChargeL h n) = 0 := by
  rw [rhoChargeR, rhoChargeL, comm_add_left, comm_add_right, comm_add_right]
  rw [A05.rho_cross_commute h brRUp brLUp brLUp_ne_brRUp.symm,
    A05.rho_cross_commute h brRUp brLDown brLDown_ne_brRUp.symm,
    A05.rho_cross_commute h brRDown brLUp brLUp_ne_brRDown.symm,
    A05.rho_cross_commute h brRDown brLDown brLDown_ne_brRDown.symm]
  simp

lemma rhoSpinR_rhoSpinL_commute (h : ℕ) (m n : ℤ) :
    A02.commutator (rhoSpinR h m) (rhoSpinL h n) = 0 := by
  rw [rhoSpinR, rhoSpinL, comm_sub_left, comm_sub_right, comm_sub_right]
  rw [A05.rho_cross_commute h brRUp brLUp brLUp_ne_brRUp.symm,
    A05.rho_cross_commute h brRUp brLDown brLDown_ne_brRUp.symm,
    A05.rho_cross_commute h brRDown brLUp brLUp_ne_brRDown.symm,
    A05.rho_cross_commute h brRDown brLDown brLDown_ne_brRDown.symm]
  simp

lemma rhoChargeR_rhoSpinL_commute (h : ℕ) (m n : ℤ) :
    A02.commutator (rhoChargeR h m) (rhoSpinL h n) = 0 := by
  rw [rhoChargeR, rhoSpinL, comm_add_left, comm_sub_right, comm_sub_right]
  rw [A05.rho_cross_commute h brRUp brLUp brLUp_ne_brRUp.symm,
    A05.rho_cross_commute h brRUp brLDown brLDown_ne_brRUp.symm,
    A05.rho_cross_commute h brRDown brLUp brLUp_ne_brRDown.symm,
    A05.rho_cross_commute h brRDown brLDown brLDown_ne_brRDown.symm]
  simp

lemma rhoSpinR_rhoChargeL_commute (h : ℕ) (m n : ℤ) :
    A02.commutator (rhoSpinR h m) (rhoChargeL h n) = 0 := by
  rw [rhoSpinR, rhoChargeL, comm_sub_left, comm_add_right, comm_add_right]
  rw [A05.rho_cross_commute h brRUp brLUp brLUp_ne_brRUp.symm,
    A05.rho_cross_commute h brRUp brLDown brLDown_ne_brRUp.symm,
    A05.rho_cross_commute h brRDown brLUp brLUp_ne_brRDown.symm,
    A05.rho_cross_commute h brRDown brLDown brLDown_ne_brRDown.symm]
  simp

/-! ## 4. Two-Channel Spin-Singlet Pairing (`A3`, `B3`) -/

/-- Spin-singlet Channel A (`R↓`, `L↑`). -/
def singletBranchesA : A06.Branches SpinBranch :=
  ⟨brRDown, brLUp, brLUp_ne_brRDown.symm⟩

/-- Spin-singlet Channel B (`R↑`, `L↓`). -/
def singletBranchesB : A06.Branches SpinBranch :=
  ⟨brRUp, brLDown, brLDown_ne_brRUp.symm⟩

noncomputable def singletOrderSC (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (x : ℤ) :
    A05.Operators SpinBranch h :=
  Ch20.orderSC h b singletBranchesB x - Ch20.orderSC h b singletBranchesA x

lemma singlet_targets_distinct (Ns : SpinBranch → ℤ) :
    Ch20.scTarget singletBranchesA Ns ≠ Ch20.scTarget singletBranchesB Ns := by
  intro heq
  have hval := congrFun heq brLUp
  simp only [Ch20.scTarget_apply, Ch20.scShift, singletBranchesA, singletBranchesB,
    brLUp, brLDown, brRUp, brRDown] at hval
  norm_num at hval

lemma singlet_channel_targets_orthogonal (h : ℕ) (Ns : SpinBranch → ℤ) (K₁ K₂ : ℕ)
    (u : A05.FockSpace SpinBranch h)
    (hu : u ∈ A05.jointBudget h (Ch20.scTarget singletBranchesA Ns) K₁)
    (v : A05.FockSpace SpinBranch h)
    (hv : v ∈ A05.jointBudget h (Ch20.scTarget singletBranchesB Ns) K₂) :
    inner ℂ u v = 0 :=
  distinct_charge_budgets_orthogonal h _ _ (singlet_targets_distinct Ns) K₁ K₂ u hu v hv

lemma singlet_preserves_spin_and_shifts_charge (Ns : SpinBranch → ℤ) :
    (branchesToSpinCharge (Ch20.scTarget singletBranchesA Ns)).qc = (branchesToSpinCharge Ns).qc - 2 ∧
    (branchesToSpinCharge (Ch20.scTarget singletBranchesA Ns)).qs = (branchesToSpinCharge Ns).qs ∧
    (branchesToSpinCharge (Ch20.scTarget singletBranchesB Ns)).qc = (branchesToSpinCharge Ns).qc - 2 ∧
    (branchesToSpinCharge (Ch20.scTarget singletBranchesB Ns)).qs = (branchesToSpinCharge Ns).qs := by
  simp only [branchesToSpinCharge, Ch20.scTarget_apply, Ch20.scShift,
    singletBranchesA, singletBranchesB, brLUp, brLDown, brRUp, brRDown]
  norm_num
  omega

/-- Channel A projected SC residual identity inherited directly from `Ch20.projected_sc_residual`. -/
lemma singletA_projected_residual (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (x : ℤ) (Ns : SpinBranch → ℤ)
    (Ks Km Kt : ℕ) :
    Ch14.projectedMap h Ns (Ch20.scTarget singletBranchesA Ns) Ks Kt (Ch20.orderSC h b singletBranchesA x) =
      Ch14.projectedMap h (Ch13.lowerCharge Ns singletBranchesA.leftSpecies)
        (Ch20.scTarget singletBranchesA Ns) Km Kt
          (Ch20.fieldOf h b singletBranchesA.rightSpecies x) ∘ₗ
        Ch14.projectedMap h Ns (Ch13.lowerCharge Ns singletBranchesA.leftSpecies) Ks Km
          (Ch20.fieldOf h b singletBranchesA.leftSpecies x) +
      Ch14.projectedMap h Ns (Ch20.scTarget singletBranchesA Ns) Ks Kt
        (Ch20.scResidualOp h b singletBranchesA x Ns Km) :=
  Ch20.projected_sc_residual h b singletBranchesA x Ns Ks Km Kt

/-- Channel B projected SC residual identity inherited directly from `Ch20.projected_sc_residual`. -/
lemma singletB_projected_residual (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (x : ℤ) (Ns : SpinBranch → ℤ)
    (Ks Km Kt : ℕ) :
    Ch14.projectedMap h Ns (Ch20.scTarget singletBranchesB Ns) Ks Kt (Ch20.orderSC h b singletBranchesB x) =
      Ch14.projectedMap h (Ch13.lowerCharge Ns singletBranchesB.leftSpecies)
        (Ch20.scTarget singletBranchesB Ns) Km Kt
          (Ch20.fieldOf h b singletBranchesB.rightSpecies x) ∘ₗ
        Ch14.projectedMap h Ns (Ch13.lowerCharge Ns singletBranchesB.leftSpecies) Ks Km
          (Ch20.fieldOf h b singletBranchesB.leftSpecies x) +
      Ch14.projectedMap h Ns (Ch20.scTarget singletBranchesB Ns) Ks Kt
        (Ch20.scResidualOp h b singletBranchesB x Ns Km) :=
  Ch20.projected_sc_residual h b singletBranchesB x Ns Ks Km Kt

/-- Combined coordinate set `U_{t,B} ∪ U_{t,A}` for the two orthogonal singlet target budgets. -/
def singletTargetUnionSet (h : ℕ) (Ns : SpinBranch → ℤ) (KtB KtA : ℕ) :
    Set (A05.Occupation SpinBranch h) :=
  Ch14.budgetSet h (Ch20.scTarget singletBranchesB Ns) KtB ∪
    Ch14.budgetSet h (Ch20.scTarget singletBranchesA Ns) KtA

/-- Combined orthogonal-sum codomain `W = V_{t,B} ⊔ V_{t,A}` (`V_{t,1} ⊕ V_{t,2}` in §21.2). -/
noncomputable def singletTargetSum (h : ℕ) (Ns : SpinBranch → ℤ) (KtB KtA : ℕ) :
    Submodule ℂ (A05.FockSpace SpinBranch h) :=
  A05.jointBudget h (Ch20.scTarget singletBranchesB Ns) KtB ⊔
    A05.jointBudget h (Ch20.scTarget singletBranchesA Ns) KtA

lemma singletTargetSum_disjoint (h : ℕ) (Ns : SpinBranch → ℤ) (KtB KtA : ℕ) :
    Disjoint (A05.jointBudget h (Ch20.scTarget singletBranchesB Ns) KtB)
      (A05.jointBudget h (Ch20.scTarget singletBranchesA Ns) KtA) := by
  rw [Submodule.disjoint_def]
  intro v hvB hvA
  have h0 : inner ℂ v v = 0 :=
    singlet_channel_targets_orthogonal h Ns KtA KtB v hvA v hvB
  exact inner_self_eq_zero.mp h0

/-- Canonical isometric inclusion `j₁ : V_{t,B} ↪ W` of singlet channel 1 (`R↑, L↓`). -/
noncomputable def singletTargetInclB (h : ℕ) (Ns : SpinBranch → ℤ) (KtB KtA : ℕ) :
    A05.jointBudget h (Ch20.scTarget singletBranchesB Ns) KtB →ₗ[ℂ]
      singletTargetSum h Ns KtB KtA :=
  Submodule.inclusion le_sup_left

/-- Canonical isometric inclusion `j₂ : V_{t,A} ↪ W` of singlet channel 2 (`R↓, L↑`). -/
noncomputable def singletTargetInclA (h : ℕ) (Ns : SpinBranch → ℤ) (KtB KtA : ℕ) :
    A05.jointBudget h (Ch20.scTarget singletBranchesA Ns) KtA →ₗ[ℂ]
      singletTargetSum h Ns KtB KtA :=
  Submodule.inclusion le_sup_right

/-- Ambient orthogonal projector `P_W = P_{t,B} + P_{t,A}` onto `W = V_{t,B} ⊕ V_{t,A}`. -/
noncomputable def singletTargetProjection (h : ℕ) (Ns : SpinBranch → ℤ) (KtB KtA : ℕ) :
    A05.Operators SpinBranch h :=
  Ch14.projection h (Ch20.scTarget singletBranchesB Ns) KtB +
    Ch14.projection h (Ch20.scTarget singletBranchesA Ns) KtA

private lemma ch14_projection_eq_prod (h : ℕ) (Ns : SpinBranch → ℤ) (K : ℕ) :
    Ch14.projection h Ns K =
      @A03.coordinateProjection (A05.Mode SpinBranch h) _ instDecidableEqProd
        (Ch14.budgetSet h Ns K) := by
  apply @A02.end_ext_basis (A05.Mode SpinBranch h) _ instDecidableEqProd
  intro S
  have hket : @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S =
      @A02.ket (A05.Mode SpinBranch h) _ (Ch14.localModeDecidableEq h) S := by
    have hdec : (instDecidableEqProd : DecidableEq (A05.Mode SpinBranch h)) =
        Ch14.localModeDecidableEq h := Subsingleton.elim _ _
    exact congrArg (fun d => @A02.ket (A05.Mode SpinBranch h) _ d S) hdec
  unfold Ch14.projection
  rw [@A03.projection_ket (A05.Mode SpinBranch h) _ instDecidableEqProd, hket,
    @A03.projection_ket (A05.Mode SpinBranch h) _ (Ch14.localModeDecidableEq h)]

lemma singletTargetProjection_eq_coord (h : ℕ) (Ns : SpinBranch → ℤ) (KtB KtA : ℕ) :
    singletTargetProjection h Ns KtB KtA =
      @A03.coordinateProjection (A05.Mode SpinBranch h) _ instDecidableEqProd
        (singletTargetUnionSet h Ns KtB KtA) := by
  unfold singletTargetProjection singletTargetUnionSet
  rw [ch14_projection_eq_prod, ch14_projection_eq_prod]
  apply @A02.end_ext_basis (A05.Mode SpinBranch h) _ instDecidableEqProd
  intro S
  simp only [LinearMap.add_apply,
    @A03.projection_ket (A05.Mode SpinBranch h) _ instDecidableEqProd, Set.mem_union]
  by_cases hB : S ∈ Ch14.budgetSet h (Ch20.scTarget singletBranchesB Ns) KtB
  · have hnA : S ∉ Ch14.budgetSet h (Ch20.scTarget singletBranchesA Ns) KtA := by
      intro hA
      apply singlet_targets_distinct Ns
      funext ν
      exact (hA.1 ν).symm.trans (hB.1 ν)
    simp [hB, hnA]
  · by_cases hA : S ∈ Ch14.budgetSet h (Ch20.scTarget singletBranchesA Ns) KtA
    · simp [hB, hA]
    · simp [hB, hA]

lemma singletTargetProjection_idempotent (h : ℕ) (Ns : SpinBranch → ℤ) (KtB KtA : ℕ) :
    singletTargetProjection h Ns KtB KtA * singletTargetProjection h Ns KtB KtA =
      singletTargetProjection h Ns KtB KtA := by
  rw [singletTargetProjection_eq_coord]
  exact @A03.projection_idempotent (A05.Mode SpinBranch h) _ instDecidableEqProd _

lemma singletTargetProjection_adjoint (h : ℕ) (Ns : SpinBranch → ℤ) (KtB KtA : ℕ) :
    LinearMap.adjoint (singletTargetProjection h Ns KtB KtA) =
      singletTargetProjection h Ns KtB KtA := by
  rw [singletTargetProjection_eq_coord]
  exact @A03.projection_adjoint (A05.Mode SpinBranch h) _ instDecidableEqProd _

lemma singletTargetProjection_range (h : ℕ) (Ns : SpinBranch → ℤ) (KtB KtA : ℕ) :
    LinearMap.range (singletTargetProjection h Ns KtB KtA) = singletTargetSum h Ns KtB KtA := by
  rw [singletTargetProjection_eq_coord,
    @A03.projection_range (A05.Mode SpinBranch h) _ instDecidableEqProd,
    singletTargetUnionSet,
    @A03.coordinate_space_union (A05.Mode SpinBranch h) _ instDecidableEqProd]
  rfl

/-- Typed projection `p_W A i_s : V_s →ₗ[ℂ] W` onto the combined singlet target codomain. -/
noncomputable def singletProjectedMap (h : ℕ) (Ns : SpinBranch → ℤ) (Ks KtB KtA : ℕ)
    (A : A05.Operators SpinBranch h) :
    A05.jointBudget h Ns Ks →ₗ[ℂ] singletTargetSum h Ns KtB KtA :=
  (singletTargetProjection h Ns KtB KtA * A).domRestrict (A05.jointBudget h Ns Ks) |>.codRestrict
    (singletTargetSum h Ns KtB KtA) (fun v => by
      rw [← singletTargetProjection_range h Ns KtB KtA]
      exact ⟨A v.val, rfl⟩)

private lemma orderSC_maps_sector (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h))
    (branches : A06.Branches SpinBranch) (x : ℤ)
    (Ns : SpinBranch → ℤ) (v : A05.FockSpace SpinBranch h) (hv : v ∈ chargeSector h Ns) :
    Ch20.orderSC h b branches x v ∈ chargeSector h (Ch20.scTarget branches Ns) := by
  have htarget : Ch20.scTarget branches Ns = fun ν => Ns ν + Ch20.scShift branches ν := by
    funext ν
    exact Ch20.scTarget_apply branches Ns ν
  rw [htarget]
  exact charge_commutator_maps_sector h (Ch20.orderSC h b branches x) (Ch20.scShift branches)
    (fun ν => Ch20.orderSC_charge_commutator h b branches x ν) Ns v hv

private lemma ch14_projection_vanish_of_distinct_sector (h : ℕ)
    (Ns₁ Ns₂ : SpinBranch → ℤ) (hne : Ns₁ ≠ Ns₂) (K : ℕ)
    (w : A05.FockSpace SpinBranch h) (hw : w ∈ chargeSector h Ns₁) :
    Ch14.projection h Ns₂ K w = 0 := by
  rw [ch14_projection_eq_prod]
  rw [chargeSector] at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    rw [@A03.projection_ket (A05.Mode SpinBranch h) _ instDecidableEqProd]
    have hnot : S ∉ Ch14.budgetSet h Ns₂ K := by
      intro hmem
      apply hne
      funext ν
      exact (hS ν).symm.trans (hmem.1 ν)
    simp [hnot]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

/-- Exact two-channel projected singlet identity (`thm:ch21-pair-projected`, Eq. (21.7))
on the combined orthogonal-sum codomain `W = V_{t,B} ⊕ V_{t,A}` with independent cutoffs
`Ks, KmB, KmA, KtB, KtA`. -/
theorem singletOrderSC_projected_sum (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (x : ℤ)
    (Ns : SpinBranch → ℤ) (Ks KmB KmA KtB KtA : ℕ) :
    singletProjectedMap h Ns Ks KtB KtA (singletOrderSC h b x) =
      singletTargetInclB h Ns KtB KtA ∘ₗ
        (Ch14.projectedMap h (Ch13.lowerCharge Ns singletBranchesB.leftSpecies)
            (Ch20.scTarget singletBranchesB Ns) KmB KtB
              (Ch20.fieldOf h b singletBranchesB.rightSpecies x) ∘ₗ
          Ch14.projectedMap h Ns (Ch13.lowerCharge Ns singletBranchesB.leftSpecies) Ks KmB
            (Ch20.fieldOf h b singletBranchesB.leftSpecies x) +
          Ch14.projectedMap h Ns (Ch20.scTarget singletBranchesB Ns) Ks KtB
            (Ch20.scResidualOp h b singletBranchesB x Ns KmB)) -
      singletTargetInclA h Ns KtB KtA ∘ₗ
        (Ch14.projectedMap h (Ch13.lowerCharge Ns singletBranchesA.leftSpecies)
            (Ch20.scTarget singletBranchesA Ns) KmA KtA
              (Ch20.fieldOf h b singletBranchesA.rightSpecies x) ∘ₗ
          Ch14.projectedMap h Ns (Ch13.lowerCharge Ns singletBranchesA.leftSpecies) Ks KmA
            (Ch20.fieldOf h b singletBranchesA.leftSpecies x) +
          Ch14.projectedMap h Ns (Ch20.scTarget singletBranchesA Ns) Ks KtA
            (Ch20.scResidualOp h b singletBranchesA x Ns KmA)) := by
  rw [← singletB_projected_residual h b x Ns Ks KmB KtB,
    ← singletA_projected_residual h b x Ns Ks KmA KtA]
  ext v : 1
  apply Subtype.ext
  have hvSec : v.val ∈ chargeSector h Ns := jointBudget_le_chargeSector h Ns Ks v.property
  have hBsec : Ch20.orderSC h b singletBranchesB x v.val ∈
      chargeSector h (Ch20.scTarget singletBranchesB Ns) :=
    orderSC_maps_sector h b singletBranchesB x Ns v.val hvSec
  have hAsec : Ch20.orderSC h b singletBranchesA x v.val ∈
      chargeSector h (Ch20.scTarget singletBranchesA Ns) :=
    orderSC_maps_sector h b singletBranchesA x Ns v.val hvSec
  have hBA0 : Ch14.projection h (Ch20.scTarget singletBranchesA Ns) KtA
      (Ch20.orderSC h b singletBranchesB x v.val) = 0 :=
    ch14_projection_vanish_of_distinct_sector h _ _ (singlet_targets_distinct Ns).symm KtA _ hBsec
  have hAB0 : Ch14.projection h (Ch20.scTarget singletBranchesB Ns) KtB
      (Ch20.orderSC h b singletBranchesA x v.val) = 0 :=
    ch14_projection_vanish_of_distinct_sector h _ _ (singlet_targets_distinct Ns) KtB _ hAsec
  change singletTargetProjection h Ns KtB KtA (singletOrderSC h b x v.val) =
    Ch14.projection h (Ch20.scTarget singletBranchesB Ns) KtB
      (Ch20.orderSC h b singletBranchesB x v.val) -
    Ch14.projection h (Ch20.scTarget singletBranchesA Ns) KtA
      (Ch20.orderSC h b singletBranchesA x v.val)
  simp only [singletTargetProjection, singletOrderSC, LinearMap.add_apply, LinearMap.sub_apply,
    map_sub, hBA0, hAB0]
  abel

/-! ## 5. Real-Space Umklapp Operator & Charge Sector Theorems (`A2`, `B2`) -/

/-- Umklapp charge transfer vector `(+1, +1, -1, -1)` on `(L↑, L↓, R↑, R↓)`. -/
def umklappDelta (ν : SpinBranch) : ℤ :=
  if ν = brLUp ∨ ν = brLDown then 1 else -1

def umklappForwardTarget (Ns : SpinBranch → ℤ) (ν : SpinBranch) : ℤ :=
  Ns ν + umklappDelta ν

def umklappBackwardTarget (Ns : SpinBranch → ℤ) (ν : SpinBranch) : ℤ :=
  Ns ν - umklappDelta ν

lemma umklapp_targets_distinct (Ns : SpinBranch → ℤ) :
    umklappForwardTarget Ns ≠ Ns ∧
    umklappBackwardTarget Ns ≠ Ns ∧
    umklappForwardTarget Ns ≠ umklappBackwardTarget Ns := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; have h0 := congrFun h brLUp
    simp [umklappForwardTarget, umklappDelta, brLUp] at h0
  · intro h; have h0 := congrFun h brLUp
    simp [umklappBackwardTarget, umklappDelta, brLUp] at h0
  · intro h; have h0 := congrFun h brLUp
    simp [umklappForwardTarget, umklappBackwardTarget, umklappDelta, brLUp] at h0
    omega

lemma umklapp_quantum_number_shifts (Ns : SpinBranch → ℤ) :
    let q := branchesToSpinCharge Ns
    let qf := branchesToSpinCharge (umklappForwardTarget Ns)
    let qb := branchesToSpinCharge (umklappBackwardTarget Ns)
    qf.qc = q.qc ∧ qf.qs = q.qs ∧ qf.jc = q.jc - 4 ∧ qf.js = q.js ∧
    qb.qc = q.qc ∧ qb.qs = q.qs ∧ qb.jc = q.jc + 4 ∧ qb.js = q.js := by
  dsimp [branchesToSpinCharge, umklappForwardTarget, umklappBackwardTarget, umklappDelta,
    brLUp, brLDown, brRUp, brRDown]
  omega

/-- Real-space fermionic site annihilation and creation shorthands. -/
noncomputable def siteField (h : ℕ) (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h))
    (ν : SpinBranch) (x : ℤ) : A05.Operators SpinBranch h :=
  A05.liftedAnnihilation h b ν x

noncomputable def siteAdjoint (h : ℕ) (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h))
    (ν : SpinBranch) (x : ℤ) : A05.Operators SpinBranch h :=
  LinearMap.adjoint (A05.liftedAnnihilation h b ν x)

/-- Forward Umklapp local term `c†_{L↑}(x) c†_{L↓}(x) c_{R↓}(x) c_{R↑}(x)`. -/
noncomputable def umklappForwardSite (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (x : ℤ) :
    A05.Operators SpinBranch h :=
  siteAdjoint h b brLUp x * siteAdjoint h b brLDown x *
    siteField h b brRDown x * siteField h b brRUp x

/-- Backward Umklapp local term `c†_{R↑}(x) c†_{R↓}(x) c_{L↓}(x) c_{L↑}(x)`. -/
noncomputable def umklappBackwardSite (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (x : ℤ) :
    A05.Operators SpinBranch h :=
  siteAdjoint h b brRUp x * siteAdjoint h b brRDown x *
    siteField h b brLDown x * siteField h b brLUp x

private lemma end_adjoint_mul (h : ℕ) (A B : A05.Operators SpinBranch h) :
    LinearMap.adjoint (A * B) = LinearMap.adjoint B * LinearMap.adjoint A :=
  LinearMap.adjoint_comp A B

lemma umklappBackwardSite_eq_adjoint (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (x : ℤ) :
    umklappBackwardSite h b x = LinearMap.adjoint (umklappForwardSite h b x) := by
  simp only [umklappForwardSite, umklappBackwardSite, siteAdjoint, siteField, end_adjoint_mul,
    LinearMap.adjoint_adjoint, mul_assoc]

lemma umklappForwardSite_eq_adjoint_backward (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (x : ℤ) :
    umklappForwardSite h b x = LinearMap.adjoint (umklappBackwardSite h b x) := by
  rw [umklappBackwardSite_eq_adjoint, LinearMap.adjoint_adjoint]

/-- Full periodic-summed real-space Umklapp Hamiltonian `H_U(g_U)`. -/
noncomputable def umklappOp (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (gU : ℝ) :
    A05.Operators SpinBranch h :=
  ((gU : ℂ) / (2 * (h : ℂ))) •
    ∑ x : Fin (2 * h), (umklappForwardSite h b (x.val : ℤ) + umklappBackwardSite h b (x.val : ℤ))

noncomputable def periodicUmklappOp (h : ℕ) (gU : ℝ) : A05.Operators SpinBranch h :=
  umklappOp h (fun _ => Ch06Ext.periodicTwist (2 * h)) gU

lemma umklappOp_self_adjoint (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (gU : ℝ) :
    LinearMap.adjoint (umklappOp h b gU) = umklappOp h b gU := by
  unfold umklappOp
  rw [map_smulₛₗ, starRingEnd_apply]
  have hscalar : star ((gU : ℂ) / (2 * (h : ℂ))) = (gU : ℂ) / (2 * (h : ℂ)) := by simp
  rw [hscalar, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [map_add, ← umklappBackwardSite_eq_adjoint, ← umklappForwardSite_eq_adjoint_backward, add_comm]

private lemma annihilation_charge_commutator (h : ℕ) (ν η : SpinBranch)
    (k : Ch01.Band (2 * h)) :
    A02.commutator (A05.chargeObservable h ν) (A05.annihilation h η k) =
      -(if ν = η then (1 : ℂ) else 0) • A05.annihilation h η k := by
  apply @A02.end_ext_basis (A05.Mode SpinBranch h) _ instDecidableEqProd
  intro S
  simp only [A02.commutator, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply]
  unfold A05.annihilation
  let kS := @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S
  change (A05.chargeObservable h ν) (Ch04.annihilation (η, k) kS) -
      Ch04.annihilation (η, k) ((A05.chargeObservable h ν) kS) =
    (-(if ν = η then (1 : ℂ) else 0)) • Ch04.annihilation (η, k) kS
  have hqS : A05.chargeObservable h ν kS =
      (Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) : ℂ) • kS :=
    ket_chargeObservable h ν S
  rw [hqS, map_smul]
  have hch : Ch04.annihilation (η, k) kS =
      if (η, k) ∈ S then
        Ch04.fermionSign (η, k) S • @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd (S.erase (η, k))
      else 0 := by
    unfold Ch04.annihilation
    exact A02.extend_basis_ket _ S
  rw [hch]
  by_cases hmem : (η, k) ∈ S
  · simp only [hmem, ↓reduceIte]
    have hqEr := ket_chargeObservable h ν (S.erase (η, k))
    rw [map_smul, hqEr]
    have hdiff : Ch07.relativeCharge h (Ch07.speciesConfiguration h (S.erase (η, k)) ν) =
        Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν) - (if ν = η then 1 else 0) := by
      by_cases hνη : ν = η
      · subst η
        have hspec : Ch07.speciesConfiguration h (S.erase (ν, k)) ν =
            (Ch07.speciesConfiguration h S ν).erase k := by
          ext j; simp [Ch07.speciesConfiguration, Finset.mem_erase]
        have hkmem : k ∈ Ch07.speciesConfiguration h S ν :=
          Finset.mem_image.mpr ⟨(ν, k), Finset.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
        rw [hspec, Ch07.charge_erase h _ k hkmem]; simp
      · have hspec : Ch07.speciesConfiguration h (S.erase (η, k)) ν =
            Ch07.speciesConfiguration h S ν := by
          ext j; simp [Ch07.speciesConfiguration, Finset.mem_erase, hνη]
        rw [hspec]; simp [hνη]
    rw [hdiff]
    by_cases hνη : ν = η
    · simp only [hνη, ↓reduceIte, Int.cast_sub, Int.cast_one, smul_smul]
      module
    · simp only [hνη, ↓reduceIte, sub_zero, neg_zero, smul_smul]
      module
  · simp [hmem]

private lemma siteField_charge_commutator (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (ν η : SpinBranch) (x : ℤ) :
    A02.commutator (A05.chargeObservable h ν) (siteField h b η x) =
      -(if ν = η then (1 : ℂ) else 0) • siteField h b η x := by
  unfold siteField A05.liftedAnnihilation
  simp only [A02.commutator, smul_mul_assoc, mul_smul_comm]
  rw [Finset.mul_sum, Finset.sum_mul, ← smul_sub, ← Finset.sum_sub_distrib]
  simp_rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
  change (A01.normalization (2 * h) : ℂ) •
      ∑ k : Ch01.Band (2 * h), Ch06Ext.twistedCharacter (2 * h) (b η) k x •
        A02.commutator (A05.chargeObservable h ν) (A05.annihilation h η k) = _
  simp_rw [annihilation_charge_commutator]
  simp [Finset.smul_sum, smul_smul]

private lemma adjoint_commutator_self_left (h : ℕ)
    (Q A : A05.Operators SpinBranch h) (hQ : LinearMap.adjoint Q = Q) :
    LinearMap.adjoint (A02.commutator Q A) = -A02.commutator Q (LinearMap.adjoint A) := by
  unfold A02.commutator
  rw [map_sub, end_adjoint_mul, end_adjoint_mul, hQ]
  noncomm_ring

private lemma siteAdjoint_charge_commutator (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (ν η : SpinBranch) (x : ℤ) :
    A02.commutator (A05.chargeObservable h ν) (siteAdjoint h b η x) =
      (if ν = η then (1 : ℂ) else 0) • siteAdjoint h b η x := by
  have h1 := congrArg LinearMap.adjoint (siteField_charge_commutator h b ν η x)
  rw [adjoint_commutator_self_left h _ _ (charge_observable_self_adjoint h ν)] at h1
  rw [map_smulₛₗ, starRingEnd_apply] at h1
  have hstar : star (-(if ν = η then (1 : ℂ) else 0)) = -(if ν = η then (1 : ℂ) else 0) := by
    split_ifs <;> simp
  rw [hstar] at h1
  change -A02.commutator (A05.chargeObservable h ν) (siteAdjoint h b η x) =
    -(if ν = η then (1 : ℂ) else 0) • siteAdjoint h b η x at h1
  calc
    A02.commutator (A05.chargeObservable h ν) (siteAdjoint h b η x)
        = -(-A02.commutator (A05.chargeObservable h ν) (siteAdjoint h b η x)) := by abel
    _ = -(-(if ν = η then (1 : ℂ) else 0) • siteAdjoint h b η x) := by rw [h1]
    _ = _ := by module

private lemma comm_mul_four {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Q A B C D : Module.End ℂ V) :
    A02.commutator Q (A * B * C * D) =
      A02.commutator Q A * B * C * D +
      A * A02.commutator Q B * C * D +
      A * B * A02.commutator Q C * D +
      A * B * C * A02.commutator Q D := by
  simp only [A02.commutator]
  noncomm_ring

lemma umklappForwardSite_charge_commutator (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (ν : SpinBranch) (x : ℤ) :
    A02.commutator (A05.chargeObservable h ν) (umklappForwardSite h b x) =
      (umklappDelta ν : ℂ) • umklappForwardSite h b x := by
  unfold umklappForwardSite
  rw [comm_mul_four]
  rw [siteAdjoint_charge_commutator, siteAdjoint_charge_commutator,
    siteField_charge_commutator, siteField_charge_commutator]
  fin_cases ν <;>
    simp [umklappDelta, brLUp, brLDown, brRUp, brRDown]

lemma umklappBackwardSite_charge_commutator (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (ν : SpinBranch) (x : ℤ) :
    A02.commutator (A05.chargeObservable h ν) (umklappBackwardSite h b x) =
      ((-umklappDelta ν : ℤ) : ℂ) • umklappBackwardSite h b x := by
  have h1 := congrArg LinearMap.adjoint (umklappForwardSite_charge_commutator h b ν x)
  rw [adjoint_commutator_self_left h _ _ (charge_observable_self_adjoint h ν)] at h1
  rw [← umklappBackwardSite_eq_adjoint, map_smulₛₗ, starRingEnd_apply] at h1
  have hstar : star (umklappDelta ν : ℂ) = (umklappDelta ν : ℂ) := by simp
  rw [hstar, ← umklappBackwardSite_eq_adjoint] at h1
  calc
    A02.commutator (A05.chargeObservable h ν) (umklappBackwardSite h b x)
        = -(-A02.commutator (A05.chargeObservable h ν) (umklappBackwardSite h b x)) := by abel
    _ = -((umklappDelta ν : ℂ) • umklappBackwardSite h b x) := by rw [h1]
    _ = _ := by simp [Int.cast_neg, neg_smul]

lemma umklappForwardSite_maps_sector (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (x : ℤ)
    (Ns : SpinBranch → ℤ) (v : A05.FockSpace SpinBranch h) (hv : v ∈ chargeSector h Ns) :
    umklappForwardSite h b x v ∈ chargeSector h (umklappForwardTarget Ns) := by
  change umklappForwardSite h b x v ∈ chargeSector h (fun ν => Ns ν + umklappDelta ν)
  exact charge_commutator_maps_sector h (umklappForwardSite h b x) umklappDelta
    (fun ν => umklappForwardSite_charge_commutator h b ν x) Ns v hv

lemma umklappBackwardSite_maps_sector (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (x : ℤ)
    (Ns : SpinBranch → ℤ) (v : A05.FockSpace SpinBranch h) (hv : v ∈ chargeSector h Ns) :
    umklappBackwardSite h b x v ∈ chargeSector h (umklappBackwardTarget Ns) := by
  change umklappBackwardSite h b x v ∈ chargeSector h (fun ν => Ns ν + (-umklappDelta ν))
  exact charge_commutator_maps_sector h (umklappBackwardSite h b x) (fun ν => -umklappDelta ν)
    (fun ν => umklappBackwardSite_charge_commutator h b ν x) Ns v hv

/-- Fixed-charge diagonal matrix elements of `umklappOp` vanish identically on every sector. -/
theorem umklappOp_charge_diagonal_zero (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h)) (gU : ℝ)
    (Ns : SpinBranch → ℤ) (K₁ K₂ : ℕ)
    (u : A05.FockSpace SpinBranch h) (hu : u ∈ A05.jointBudget h Ns K₁)
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ A05.jointBudget h Ns K₂) :
    inner ℂ u (umklappOp h b gU v) = 0 := by
  have huSec := jointBudget_le_chargeSector h Ns K₁ hu
  have hvSec := jointBudget_le_chargeSector h Ns K₂ hv
  have hmem : umklappOp h b gU v ∈
      chargeSector h (umklappForwardTarget Ns) ⊔ chargeSector h (umklappBackwardTarget Ns) := by
    unfold umklappOp
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro x _
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (umklappForwardSite_maps_sector h b _ Ns v hvSec))
      (Submodule.mem_sup_right (umklappBackwardSite_maps_sector h b _ Ns v hvSec))
  obtain ⟨yf, hyf, yb, hyb, heq⟩ := Submodule.mem_sup.mp hmem
  rw [← heq, inner_add_right]
  have hf0 := distinct_charge_sectors_orthogonal h Ns (umklappForwardTarget Ns)
    (umklapp_targets_distinct Ns).1.symm u huSec yf hyf
  have hb0 := distinct_charge_sectors_orthogonal h Ns (umklappBackwardTarget Ns)
    (umklapp_targets_distinct Ns).2.1.symm u huSec yb hyb
  simp [hf0, hb0]

/-! ## 6. Zero-Charge Witness & Constructive Non-Invariance (`A4`, `B4`) -/

/-- Upper witness momentum `k = 1` inside `Ch01.Band (2 * h)` for `h > 0`. -/
def witnessUpperMode (h : ℕ) (hh : 0 < h) : Ch01.Band (2 * h) :=
  ⟨1, by simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]; omega⟩

/-- Lower band-bottom witness momentum `k = 1 - h` inside `Ch01.Band (2 * h)` for `h > 0`. -/
def witnessLowerMode (h : ℕ) (hh : 0 < h) : Ch01.Band (2 * h) :=
  ⟨1 - (h : ℤ), by simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]; omega⟩

lemma witnessUpperMode_not_mem_ground_zero (h : ℕ) (hh : 0 < h) :
    witnessUpperMode h hh ∉ Ch07.groundConfiguration h 0 := by
  simp [Ch07.groundConfiguration, witnessUpperMode]

lemma witnessLowerMode_mem_ground_zero (h : ℕ) (hh : 0 < h) :
    witnessLowerMode h hh ∈ Ch07.groundConfiguration h 0 := by
  simp only [Ch07.groundConfiguration, Finset.mem_filter, Finset.mem_univ, true_and,
    witnessLowerMode]
  omega

/-- Target species occupations: `ground 1` for `L↑, L↓` and `(ground 0).erase (1 - h)` for `R↑, R↓`. -/
noncomputable def umklappTargetSpeciesConfig (h : ℕ) (hh : 0 < h) (ν : SpinBranch) :
    Ch07.Occupation h :=
  if ν = brLUp ∨ ν = brLDown then
    Ch07.groundConfiguration h 1
  else
    (Ch07.groundConfiguration h 0).erase (witnessLowerMode h hh)

noncomputable def umklappTargetConfig (h : ℕ) (hh : 0 < h) : A05.Occupation SpinBranch h :=
  A05.jointConfiguration h (umklappTargetSpeciesConfig h hh)

/-- Explicit witness ket `|Ψ_target⟩` populated by forward Umklapp from `|Ω₀⟩`. -/
noncomputable def umklappZeroChargeWitness (h : ℕ) (hh : 0 < h) :
    A05.FockSpace SpinBranch h :=
  @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd (umklappTargetConfig h hh)

lemma umklappTargetSpeciesConfig_charge (h : ℕ) (hh : 0 < h) (ν : SpinBranch) :
    Ch07.relativeCharge h (umklappTargetSpeciesConfig h hh ν) =
      umklappForwardTarget (fun _ => 0) ν := by
  have h0adm : Ch07.admissible h 0 := by unfold Ch07.admissible; omega
  have h1adm : Ch07.admissible h 1 := by unfold Ch07.admissible; omega
  by_cases hL : ν = brLUp ∨ ν = brLDown
  · simp only [umklappTargetSpeciesConfig, hL, ↓reduceIte, umklappForwardTarget, umklappDelta,
      zero_add]
    exact Ch07.ground_configuration_charge h hh 1 h1adm
  · simp only [umklappTargetSpeciesConfig, hL, ↓reduceIte, umklappForwardTarget, umklappDelta,
      zero_add]
    rw [Ch07.charge_erase h _ _ (witnessLowerMode_mem_ground_zero h hh),
      Ch07.ground_configuration_charge h hh 0 h0adm]
    ring

lemma umklappZeroChargeWitness_mem_target_sector (h : ℕ) (hh : 0 < h) :
    umklappZeroChargeWitness h hh ∈ chargeSector h (umklappForwardTarget (fun _ => 0)) := by
  rw [umklappZeroChargeWitness, chargeSector,
    @A03.ket_mem_coordinate_space (A05.Mode SpinBranch h) _ instDecidableEqProd]
  intro ν
  have hspec : Ch07.speciesConfiguration h (umklappTargetConfig h hh) ν =
      umklappTargetSpeciesConfig h hh ν := by
    ext k
    simp only [Ch07.speciesConfiguration, umklappTargetConfig, A05.jointConfiguration,
      Finset.mem_image, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨η, j⟩, ⟨⟨η', j', hj', hpair⟩, he⟩, hjk⟩
      dsimp at he hjk
      subst he hjk
      cases hpair
      exact hj'
    · intro hk
      exact ⟨(ν, k), ⟨⟨ν, k, hk, rfl⟩, rfl⟩, rfl⟩
  rw [hspec]
  exact umklappTargetSpeciesConfig_charge h hh ν

lemma umklappZeroChargeWitness_orthogonal_zero_budget (h : ℕ) (hh : 0 < h) (K : ℕ)
    (v : A05.FockSpace SpinBranch h) (hv : v ∈ A05.jointBudget h (fun _ => 0) K) :
    inner ℂ (umklappZeroChargeWitness h hh) v = 0 :=
  distinct_charge_sectors_orthogonal h (umklappForwardTarget (fun _ => 0)) (fun _ => 0)
    (umklapp_targets_distinct (fun _ => 0)).1
    (umklappZeroChargeWitness h hh) (umklappZeroChargeWitness_mem_target_sector h hh)
    v (jointBudget_le_chargeSector h (fun _ => 0) K hv)

private lemma ket_instDecidableEqProd_eq (h : ℕ) (S : A05.Occupation SpinBranch h) :
    @A02.ket (A05.Mode SpinBranch h) _ instDecidableEqProd S = A02.ket S := by
  have hdec : (instDecidableEqProd : DecidableEq (A05.Mode SpinBranch h)) =
      A05.localModeDecidableEq h := Subsingleton.elim _ _
  exact congrArg (fun d => @A02.ket (A05.Mode SpinBranch h) _ d S) hdec

private lemma siteField_ket (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h))
    (S : A05.Occupation SpinBranch h) (ν : SpinBranch) (x : ℤ) :
    siteField h b ν x (A02.ket S) =
      (A01.normalization (2 * h) : ℂ) •
        ∑ k : Ch01.Band (2 * h),
          if (ν, k) ∈ S then
            (Ch06Ext.twistedCharacter (2 * h) (b ν) k x *
              Ch04.fermionSign (ν, k) S) • A02.ket (S.erase (ν, k))
          else 0 := by
  simp only [siteField, A05.liftedAnnihilation, LinearMap.smul_apply,
    LinearMap.sum_apply, A05.annihilation, Ch04.annihilation_ket]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · simp only [smul_smul]
  · simp

private lemma map_if_zero_ch21 {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    [Module ℂ V] [Module ℂ W] (f : V →ₗ[ℂ] W) (p : Prop) [Decidable p] (v : V) :
    f (if p then v else 0) = if p then f v else 0 := by
  split_ifs <;> simp

private lemma twoSiteField_ket (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h))
    (S : A05.Occupation SpinBranch h) (ν₁ ν₂ : SpinBranch) (x : ℤ) :
    siteField h b ν₂ x (siteField h b ν₁ x (A02.ket S)) =
      ((A01.normalization (2 * h) : ℂ) ^ 2) •
        ∑ k₁ : Ch01.Band (2 * h), ∑ k₂ : Ch01.Band (2 * h),
          if (ν₁, k₁) ∈ S ∧ (ν₂, k₂) ∈ S.erase (ν₁, k₁) then
            (Ch06Ext.twistedCharacter (2 * h) (b ν₂) k₂ x *
              Ch04.fermionSign (ν₂, k₂) (S.erase (ν₁, k₁)) *
              (Ch06Ext.twistedCharacter (2 * h) (b ν₁) k₁ x *
                Ch04.fermionSign (ν₁, k₁) S)) •
              A02.ket ((S.erase (ν₁, k₁)).erase (ν₂, k₂))
          else 0 := by
  rw [siteField_ket]
  simp only [map_smul, map_sum]
  simp_rw [map_if_zero_ch21, map_smul, siteField_ket]
  rw [show (A01.normalization (2 * h) : ℂ) ^ 2 =
      (A01.normalization (2 * h) : ℂ) * (A01.normalization (2 * h) : ℂ) by ring, ← smul_smul]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k₁ _
  by_cases hk₁ : (ν₁, k₁) ∈ S
  · rw [ite_eq_left hk₁, smul_comm _ (A01.normalization (2 * h) : ℂ)]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k₂ _
    by_cases hk₂ : (ν₂, k₂) ∈ S.erase (ν₁, k₁)
    · rw [ite_eq_left hk₂, ite_eq_left ⟨hk₁, hk₂⟩, smul_smul]
      congr 1
      ring
    · simp [hk₁, hk₂]
  · simp [hk₁]

private lemma inner_ite_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (p q : Prop) [Decidable p] [Decidable q] (u v : E) :
    inner ℂ (if p then u else 0) (if q then v else 0) =
      if p ∧ q then inner ℂ u v else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

private lemma sum_single_quad {ι : Type*} [Fintype ι]
    (a b c d : ι) (f : ι → ι → ι → ι → ℂ)
    (g : ι → ι → ι → ι → Prop) [∀ i j k l, Decidable (g i j k l)]
    (huniq : ∀ i j k l, g i j k l → i = a ∧ j = b ∧ k = c ∧ l = d)
    (habcd : g a b c d) :
    (∑ i, ∑ j, ∑ k, ∑ l, if g i j k l then f i j k l else 0) = f a b c d := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single c]
      · rw [Finset.sum_eq_single d]
        · simp [habcd]
        · intro l _ hl
          have hnot : ¬ g a b c l := fun h => hl (huniq a b c l h).2.2.2
          simp [hnot]
        · simp
      · intro k _ hk
        have hzero : ∀ l, ¬ g a b k l := fun l h => hk (huniq a b k l h).2.2.1
        simp [hzero]
      · simp
    · intro j _ hj
      have hzero : ∀ k l, ¬ g a j k l := fun k l h => hj (huniq a j k l h).2.1
      simp [hzero]
    · simp
  · intro i _ hi
    have hzero : ∀ j k l, ¬ g i j k l := fun j k l h => hi (huniq i j k l h).1
    simp [hzero]
  · simp

private lemma speciesConfiguration_erase_ch21 (h : ℕ)
    (S : A05.Occupation SpinBranch h) (ν η : SpinBranch) (k : Ch01.Band (2 * h)) :
    Ch07.speciesConfiguration h (S.erase (ν, k)) η =
      if η = ν then (Ch07.speciesConfiguration h S η).erase k
      else Ch07.speciesConfiguration h S η := by
  ext j
  by_cases hη : η = ν
  · subst η
    simp [Ch07.speciesConfiguration, Finset.mem_erase]
  · simp [Ch07.speciesConfiguration, Finset.mem_erase, hη]

/-- Exact `B4` CAR matrix element `⟨Ψ_target | H_U(g_U) | Ω₀⟩ = -g_U / (2h)^2`. -/
theorem umklapp_zero_charge_witness_coeff (h : ℕ) (hh : 0 < h) (gU : ℝ) :
    inner ℂ (umklappZeroChargeWitness h hh)
      (periodicUmklappOp h gU (A05.groundKet h (fun _ => 0))) =
        -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2)) := by
  let _ : NeZero (2 * h) := ⟨by omega⟩
  let b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h) := fun _ => Ch06Ext.periodicTwist (2 * h)
  let S₀ : A05.Occupation SpinBranch h := A05.groundConfiguration h (fun _ => 0)
  let St : A05.Occupation SpinBranch h := umklappTargetConfig h hh
  let k₁₀ : Ch01.Band (2 * h) := witnessUpperMode h hh
  let k_lo : Ch01.Band (2 * h) := witnessLowerMode h hh
  have hadm0 : A05.admissible h (fun _ : SpinBranch => (0 : ℤ)) := fun _ => by
    unfold Ch07.admissible; dsimp; omega
  have hground_sec : A05.groundKet h (fun _ => 0) ∈ chargeSector h (fun _ => 0) :=
    jointBudget_le_chargeSector h (fun _ => 0) 0 (A05.ground_mem_budget h hh (fun _ => 0) hadm0 0)
  have hback_zero : ∀ x : ℤ,
      inner ℂ (umklappZeroChargeWitness h hh)
        (umklappBackwardSite h b x (A05.groundKet h (fun _ => 0))) = 0 := by
    intro x
    exact distinct_charge_sectors_orthogonal h
      (umklappForwardTarget (fun _ => 0)) (umklappBackwardTarget (fun _ => 0))
      (umklapp_targets_distinct (fun _ => 0)).2.2
      (umklappZeroChargeWitness h hh) (umklappZeroChargeWitness_mem_target_sector h hh)
      _ (umklappBackwardSite_maps_sector h b x (fun _ => 0) _ hground_sec)
  have hmem1_0 : k₁₀ ∈ Ch07.groundConfiguration h 1 := by
    simp [Ch07.groundConfiguration, k₁₀, witnessUpperMode]
  have hnmem0_1 : k₁₀ ∉ Ch07.groundConfiguration h 0 :=
    witnessUpperMode_not_mem_ground_zero h hh
  have hmem0_lo : k_lo ∈ Ch07.groundConfiguration h 0 :=
    witnessLowerMode_mem_ground_zero h hh
  have herase1 : (Ch07.groundConfiguration h 1).erase k₁₀ = Ch07.groundConfiguration h 0 := by
    ext l
    simp only [Finset.mem_erase, Ch07.groundConfiguration, Finset.mem_filter, Finset.mem_univ,
      true_and, ne_eq, Subtype.ext_iff, k₁₀, witnessUpperMode]
    omega
  have hS0_mem (ν : SpinBranch) (k : Ch01.Band (2 * h)) :
      (ν, k) ∈ S₀ ↔ k ∈ Ch07.groundConfiguration h 0 := by
    simp [S₀, A05.groundConfiguration, A05.jointConfiguration]
  have hSt_mem (ν : SpinBranch) (k : Ch01.Band (2 * h)) :
      (ν, k) ∈ St ↔ k ∈ umklappTargetSpeciesConfig h hh ν := by
    simp [St, umklappTargetConfig, A05.jointConfiguration]
  have hS0_spec (ν : SpinBranch) :
      Ch07.speciesConfiguration h S₀ ν = Ch07.groundConfiguration h 0 :=
    A05.species_joint_configuration h (fun _ => Ch07.groundConfiguration h 0) ν
  have hSt_spec (ν : SpinBranch) :
      Ch07.speciesConfiguration h St ν = umklappTargetSpeciesConfig h hh ν :=
    A05.species_joint_configuration h (umklappTargetSpeciesConfig h hh) ν
  have hcard0 : (Ch07.groundConfiguration h 0).card = h := by
    have hz := Ch07.ground_configuration_card h hh 0 (by unfold Ch07.admissible; omega)
    omega
  have hprec_lo (S : Ch07.Occupation h) : Ch04.precedingCount k_lo S = 0 := by
    unfold Ch04.precedingCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro l _
    have hl := l.property
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hl
    change ¬ (l.val < k_lo.val)
    dsimp [k_lo, witnessLowerMode]
    omega
  have hprec_10 : Ch04.precedingCount k₁₀ (Ch07.groundConfiguration h 1) = h := by
    have hfilt : (Ch07.groundConfiguration h 1).filter (· < k₁₀) =
        Ch07.groundConfiguration h 0 := by
      ext l
      simp only [Finset.mem_filter, Ch07.groundConfiguration, Finset.mem_univ, true_and]
      change (l.val ≤ 1 ∧ l.val < k₁₀.val) ↔ l.val ≤ 0
      dsimp [k₁₀, witnessUpperMode]
      omega
    unfold Ch04.precedingCount
    rw [hfilt]
    exact hcard0
  let g (k₀ k₁ k₂ k₃ : Ch01.Band (2 * h)) : Prop :=
    ((brLUp, k₀) ∈ St ∧ (brLDown, k₁) ∈ St.erase (brLUp, k₀)) ∧
      ((brRUp, k₂) ∈ S₀ ∧ (brRDown, k₃) ∈ S₀.erase (brRUp, k₂)) ∧
      ((St.erase (brLUp, k₀)).erase (brLDown, k₁) =
        (S₀.erase (brRUp, k₂)).erase (brRDown, k₃))
  have hsupp : g k₁₀ k₁₀ k_lo k_lo := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [hSt_mem]
      simpa [umklappTargetSpeciesConfig, Or.inl rfl] using hmem1_0
    · rw [Finset.mem_erase, hSt_mem]
      refine ⟨by intro he; exact brLUp_ne_brLDown (congrArg Prod.fst he).symm, ?_⟩
      simpa [umklappTargetSpeciesConfig, Or.inr rfl] using hmem1_0
    · rw [hS0_mem]
      exact hmem0_lo
    · rw [Finset.mem_erase, hS0_mem]
      refine ⟨by intro he; exact brRUp_ne_brRDown (congrArg Prod.fst he).symm, hmem0_lo⟩
    · ext ⟨ν, k⟩
      simp only [Finset.mem_erase, ne_eq, Prod.mk.injEq, hSt_mem, hS0_mem]
      fin_cases ν
      · simp [umklappTargetSpeciesConfig, brLUp, brLDown, brRUp, brRDown]
        have heq1 : k = k₁₀ ↔ k.val = 1 := by
          simp [Subtype.ext_iff, k₁₀, witnessUpperMode]
        simp only [Ch07.groundConfiguration, Finset.mem_filter, Finset.mem_univ, true_and, heq1]
        omega
      · simp [umklappTargetSpeciesConfig, brLUp, brLDown, brRUp, brRDown]
        have heq1 : k = k₁₀ ↔ k.val = 1 := by
          simp [Subtype.ext_iff, k₁₀, witnessUpperMode]
        simp only [Ch07.groundConfiguration, Finset.mem_filter, Finset.mem_univ, true_and, heq1]
        omega
      · simp [umklappTargetSpeciesConfig, brLUp, brLDown, brRUp, brRDown]
        tauto
      · simp [umklappTargetSpeciesConfig, brLUp, brLDown, brRUp, brRDown]
        tauto
  have huniq : ∀ k₀ k₁ k₂ k₃, g k₀ k₁ k₂ k₃ →
      k₀ = k₁₀ ∧ k₁ = k₁₀ ∧ k₂ = k_lo ∧ k₃ = k_lo := by
    intro k₀ k₁ k₂ k₃ hg
    rcases hg with ⟨⟨_, _⟩, ⟨hk₂, hk₃⟩, heq⟩
    have h0 : k₀ = k₁₀ := by
      by_contra hne
      have hmemL : (brLUp, k₁₀) ∈ (St.erase (brLUp, k₀)).erase (brLDown, k₁) := by
        rw [Finset.mem_erase, Finset.mem_erase, hSt_mem]
        refine ⟨fun h => brLUp_ne_brLDown (congrArg Prod.fst h),
          fun h => hne (congrArg Prod.snd h).symm, ?_⟩
        simpa [umklappTargetSpeciesConfig, brLUp, brLDown] using hmem1_0
      rw [heq] at hmemL
      simp only [Finset.mem_erase, hS0_mem] at hmemL
      exact hnmem0_1 hmemL.2.2
    have h1 : k₁ = k₁₀ := by
      by_contra hne
      have hmemL : (brLDown, k₁₀) ∈ (St.erase (brLUp, k₀)).erase (brLDown, k₁) := by
        rw [Finset.mem_erase, Finset.mem_erase, hSt_mem]
        refine ⟨fun h => hne (congrArg Prod.snd h).symm,
          fun h => brLUp_ne_brLDown.symm (congrArg Prod.fst h), ?_⟩
        simpa [umklappTargetSpeciesConfig, brLUp, brLDown] using hmem1_0
      rw [heq] at hmemL
      simp only [Finset.mem_erase, hS0_mem] at hmemL
      exact hnmem0_1 hmemL.2.2
    have h2 : k₂ = k_lo := by
      have hk₂' : k₂ ∈ Ch07.groundConfiguration h 0 := (hS0_mem brRUp k₂).mp hk₂
      by_contra hne
      have hmemL : (brRUp, k₂) ∈ (St.erase (brLUp, k₀)).erase (brLDown, k₁) := by
        rw [Finset.mem_erase, Finset.mem_erase, hSt_mem]
        refine ⟨fun h => brLDown_ne_brRUp.symm (congrArg Prod.fst h),
          fun h => brLUp_ne_brRUp.symm (congrArg Prod.fst h), ?_⟩
        simpa [umklappTargetSpeciesConfig, brLUp, brLDown, brRUp] using ⟨hne, hk₂'⟩
      rw [heq] at hmemL
      simp [Finset.mem_erase] at hmemL
    have h3 : k₃ = k_lo := by
      have hk₃' : k₃ ∈ Ch07.groundConfiguration h 0 :=
        (hS0_mem brRDown k₃).mp (Finset.mem_of_mem_erase hk₃)
      by_contra hne
      have hmemL : (brRDown, k₃) ∈ (St.erase (brLUp, k₀)).erase (brLDown, k₁) := by
        rw [Finset.mem_erase, Finset.mem_erase, hSt_mem]
        refine ⟨fun h => brLDown_ne_brRDown.symm (congrArg Prod.fst h),
          fun h => brLUp_ne_brRDown.symm (congrArg Prod.fst h), ?_⟩
        simpa [umklappTargetSpeciesConfig, brLUp, brLDown, brRDown] using ⟨hne, hk₃'⟩
      rw [heq] at hmemL
      simp [Finset.mem_erase] at hmemL
    exact ⟨h0, h1, h2, h3⟩
  have hsign_prod :
      star (Ch04.fermionSign (brLDown, k₁₀) (St.erase (brLUp, k₁₀)) *
          Ch04.fermionSign (brLUp, k₁₀) St) *
        (Ch04.fermionSign (brRDown, k_lo) (S₀.erase (brRUp, k_lo)) *
          Ch04.fermionSign (brRUp, k_lo) S₀) = (-1 : ℂ) := by
    have hp1 : Ch04.precedingCount (brRUp, k_lo) S₀ = 2 * h := by
      rw [A05.preceding_count_split, hprec_lo]
      have hfilt : (Finset.univ.filter (· < brRUp) : Finset SpinBranch) = {brLUp, brLDown} := by
        decide
      rw [hfilt, Finset.sum_insert (by decide), Finset.sum_singleton,
        hS0_spec brLUp, hS0_spec brLDown, hcard0]
      omega
    have hp2 : Ch04.precedingCount (brRDown, k_lo) (S₀.erase (brRUp, k_lo)) = 3 * h - 1 := by
      rw [A05.preceding_count_split, hprec_lo]
      have hfilt : (Finset.univ.filter (· < brRDown) : Finset SpinBranch) =
          {brLUp, brLDown, brRUp} := by decide
      rw [hfilt, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton,
        speciesConfiguration_erase_ch21, speciesConfiguration_erase_ch21,
        speciesConfiguration_erase_ch21,
        ite_eq_right brLUp_ne_brRUp, ite_eq_right brLDown_ne_brRUp, ite_eq_left rfl,
        hS0_spec brLUp, hS0_spec brLDown, hS0_spec brRUp,
        hcard0, Finset.card_erase_of_mem hmem0_lo, hcard0]
      omega
    have hp3 : Ch04.precedingCount (brLUp, k₁₀) St = h := by
      rw [A05.preceding_count_split]
      have hfilt : (Finset.univ.filter (· < brLUp) : Finset SpinBranch) = ∅ := by decide
      rw [hfilt, Finset.sum_empty, zero_add, hSt_spec brLUp]
      simpa [umklappTargetSpeciesConfig] using hprec_10
    have hp4 : Ch04.precedingCount (brLDown, k₁₀) (St.erase (brLUp, k₁₀)) = 2 * h := by
      rw [A05.preceding_count_split]
      have hfilt : (Finset.univ.filter (· < brLDown) : Finset SpinBranch) = {brLUp} := by decide
      rw [hfilt, Finset.sum_singleton,
        speciesConfiguration_erase_ch21, speciesConfiguration_erase_ch21,
        ite_eq_left rfl, ite_eq_right brLUp_ne_brLDown.symm,
        hSt_spec brLUp, hSt_spec brLDown]
      have hup : umklappTargetSpeciesConfig h hh brLUp = Ch07.groundConfiguration h 1 := by
        simp [umklappTargetSpeciesConfig]
      have hdn : umklappTargetSpeciesConfig h hh brLDown = Ch07.groundConfiguration h 1 := by
        simp [umklappTargetSpeciesConfig]
      rw [hup, hdn, herase1, hcard0, hprec_10]
      omega
    unfold Ch04.fermionSign
    rw [hp1, hp2, hp3, hp4]
    simp only [star_mul, star_pow, star_neg, star_one]
    rw [← pow_add, ← pow_add, ← pow_add]
    have hexp : h + 2 * h + (3 * h - 1 + 2 * h) = 2 * (4 * h - 1) + 1 := by omega
    rw [hexp, pow_add, pow_mul]
    norm_num
  have hfwd : ∀ x : ℤ,
      inner ℂ (umklappZeroChargeWitness h hh)
        (umklappForwardSite h b x (A05.groundKet h (fun _ => 0))) =
          -(((2 * (h : ℂ)) ^ 2)⁻¹) := by
    intro x
    rw [umklappZeroChargeWitness, ket_instDecidableEqProd_eq]
    change inner ℂ (A02.ket St) (umklappForwardSite h b x (A02.ket S₀)) = _
    have hadj : inner ℂ (A02.ket St) (umklappForwardSite h b x (A02.ket S₀)) =
        inner ℂ (siteField h b brLDown x (siteField h b brLUp x (A02.ket St)))
          (siteField h b brRDown x (siteField h b brRUp x (A02.ket S₀))) := by
      simp only [umklappForwardSite, Module.End.mul_apply, siteAdjoint, siteField,
        LinearMap.adjoint_inner_right]
    rw [hadj, twoSiteField_ket, twoSiteField_ket]
    rw [inner_smul_left, inner_smul_right]
    rw [starRingEnd_apply, star_pow, A01.normalization_conj (2 * h)]
    have hnorm4 : (A01.normalization (2 * h) : ℂ) ^ 2 * (A01.normalization (2 * h) : ℂ) ^ 2 =
        ((2 * (h : ℂ)) ^ 2)⁻¹ := by
      have hsq : ((2 * h : ℕ) : ℂ) * (A01.normalization (2 * h) : ℂ) ^ 2 = 1 :=
        A01.normalization_square_complex (2 * h)
      have hh0 : (2 * (h : ℂ)) ≠ 0 := by
        exact mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hh))
      have hnorm2 : (A01.normalization (2 * h) : ℂ) ^ 2 = (2 * (h : ℂ))⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        simpa [Nat.cast_mul, Nat.cast_ofNat] using hsq
      rw [hnorm2]
      field_simp [hh0]
    rw [← mul_assoc, hnorm4]
    simp_rw [sum_inner, inner_sum, inner_ite_zero, inner_smul_left, inner_smul_right,
      A02.ket_inner]
    have hre : (∑ k₀ : Ch01.Band (2 * h), ∑ k₁ : Ch01.Band (2 * h),
        ∑ k₂ : Ch01.Band (2 * h), ∑ k₃ : Ch01.Band (2 * h),
          if ((brLUp, k₀) ∈ St ∧ (brLDown, k₁) ∈ St.erase (brLUp, k₀)) ∧
              ((brRUp, k₂) ∈ S₀ ∧ (brRDown, k₃) ∈ S₀.erase (brRUp, k₂)) then
            starRingEnd ℂ
              (Ch06Ext.twistedCharacter (2 * h) (b brLDown) k₁ x *
                Ch04.fermionSign (brLDown, k₁) (St.erase (brLUp, k₀)) *
                (Ch06Ext.twistedCharacter (2 * h) (b brLUp) k₀ x *
                  Ch04.fermionSign (brLUp, k₀) St)) *
              ((Ch06Ext.twistedCharacter (2 * h) (b brRDown) k₃ x *
                  Ch04.fermionSign (brRDown, k₃) (S₀.erase (brRUp, k₂)) *
                  (Ch06Ext.twistedCharacter (2 * h) (b brRUp) k₂ x *
                    Ch04.fermionSign (brRUp, k₂) S₀)) *
                if (St.erase (brLUp, k₀)).erase (brLDown, k₁) =
                    (S₀.erase (brRUp, k₂)).erase (brRDown, k₃) then 1 else 0)
          else 0) =
        ∑ k₀ : Ch01.Band (2 * h), ∑ k₁ : Ch01.Band (2 * h),
          ∑ k₂ : Ch01.Band (2 * h), ∑ k₃ : Ch01.Band (2 * h),
            if g k₀ k₁ k₂ k₃ then
              starRingEnd ℂ
                (Ch06Ext.twistedCharacter (2 * h) (b brLDown) k₁ x *
                  Ch04.fermionSign (brLDown, k₁) (St.erase (brLUp, k₀)) *
                  (Ch06Ext.twistedCharacter (2 * h) (b brLUp) k₀ x *
                    Ch04.fermionSign (brLUp, k₀) St)) *
                (Ch06Ext.twistedCharacter (2 * h) (b brRDown) k₃ x *
                  Ch04.fermionSign (brRDown, k₃) (S₀.erase (brRUp, k₂)) *
                  (Ch06Ext.twistedCharacter (2 * h) (b brRUp) k₂ x *
                    Ch04.fermionSign (brRUp, k₂) S₀))
            else 0 := by
      refine Finset.sum_congr rfl (fun k₀ _ => Finset.sum_congr rfl (fun k₁ _ =>
        Finset.sum_congr rfl (fun k₂ _ => Finset.sum_congr rfl (fun k₃ _ => ?_))))
      dsimp only [g]
      by_cases ha : (brLUp, k₀) ∈ St ∧ (brLDown, k₁) ∈ St.erase (brLUp, k₀)
      · by_cases hb : (brRUp, k₂) ∈ S₀ ∧ (brRDown, k₃) ∈ S₀.erase (brRUp, k₂)
        · by_cases hc : (St.erase (brLUp, k₀)).erase (brLDown, k₁) =
              (S₀.erase (brRUp, k₂)).erase (brRDown, k₃)
          · rw [ite_eq_left ⟨ha, hb⟩, ite_eq_left hc, mul_one, ite_eq_left ⟨ha, hb, hc⟩]
          · rw [ite_eq_left ⟨ha, hb⟩, ite_eq_right hc, mul_zero, mul_zero,
              ite_eq_right (fun h => hc h.2.2)]
        · rw [ite_eq_right (fun h => hb h.2), ite_eq_right (fun h => hb h.2.1)]
      · rw [ite_eq_right (fun h => ha h.1), ite_eq_right (fun h => ha h.1)]
    rw [hre, sum_single_quad k₁₀ k₁₀ k_lo k_lo _ g huniq hsupp]
    have hchar_prod :
        starRingEnd ℂ (Ch06Ext.twistedCharacter (2 * h) (b brLDown) k₁₀ x) *
          starRingEnd ℂ (Ch06Ext.twistedCharacter (2 * h) (b brLUp) k₁₀ x) *
          (Ch06Ext.twistedCharacter (2 * h) (b brRDown) k_lo x *
            Ch06Ext.twistedCharacter (2 * h) (b brRUp) k_lo x) = 1 := by
      have htw (ν : SpinBranch) (k : Ch01.Band (2 * h)) :
          Ch06Ext.twistedCharacter (2 * h) (b ν) k x =
            A01.integerCharacter (A01.canonicalRoot (2 * h)) k.val x := by
        simp [b, Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, Ch06Ext.periodicTwist]
      simp_rw [htw, starRingEnd_apply,
        A01.complex_character_conj (2 * h) _ (A01.canonical_root_primitive (2 * h))]
      have hroot := A01.canonical_root_primitive (2 * h)
      have hnz : A01.canonicalRoot (2 * h) ≠ 0 := A01.root_ne_zero (2 * h) _ hroot
      have hpow1 : A01.canonicalRoot (2 * h) ^ ((2 * h : ℕ) : ℤ) = 1 := by
        rw [zpow_natCast]
        exact hroot.pow_eq_one
      simp only [A01.integerCharacter, k₁₀, k_lo, witnessUpperMode, witnessLowerMode]
      rw [← zpow_add₀ hnz, ← zpow_add₀ hnz, ← zpow_add₀ hnz]
      have hexp : (-1) * x + (-1) * x + ((1 - (h : ℤ)) * x + (1 - (h : ℤ)) * x) =
          ((2 * h : ℕ) : ℤ) * (-x) := by
        push_cast
        ring
      rw [hexp, zpow_mul, hpow1, one_zpow]
    have hsplit :
        starRingEnd ℂ
            (Ch06Ext.twistedCharacter (2 * h) (b brLDown) k₁₀ x *
              Ch04.fermionSign (brLDown, k₁₀) (St.erase (brLUp, k₁₀)) *
              (Ch06Ext.twistedCharacter (2 * h) (b brLUp) k₁₀ x *
                Ch04.fermionSign (brLUp, k₁₀) St)) *
            (Ch06Ext.twistedCharacter (2 * h) (b brRDown) k_lo x *
              Ch04.fermionSign (brRDown, k_lo) (S₀.erase (brRUp, k_lo)) *
              (Ch06Ext.twistedCharacter (2 * h) (b brRUp) k_lo x *
                Ch04.fermionSign (brRUp, k_lo) S₀)) =
          (starRingEnd ℂ (Ch06Ext.twistedCharacter (2 * h) (b brLDown) k₁₀ x) *
            starRingEnd ℂ (Ch06Ext.twistedCharacter (2 * h) (b brLUp) k₁₀ x) *
            (Ch06Ext.twistedCharacter (2 * h) (b brRDown) k_lo x *
              Ch06Ext.twistedCharacter (2 * h) (b brRUp) k_lo x)) *
          (star (Ch04.fermionSign (brLDown, k₁₀) (St.erase (brLUp, k₁₀)) *
              Ch04.fermionSign (brLUp, k₁₀) St) *
            (Ch04.fermionSign (brRDown, k_lo) (S₀.erase (brRUp, k_lo)) *
              Ch04.fermionSign (brRUp, k_lo) S₀)) := by
      simp only [map_mul, starRingEnd_apply, star_mul]
      ring
    rw [hsplit, hchar_prod, one_mul, hsign_prod]
    ring
  unfold periodicUmklappOp umklappOp
  rw [LinearMap.smul_apply, LinearMap.sum_apply, inner_smul_right, inner_sum]
  simp only [LinearMap.add_apply, inner_add_right]
  simp_rw [show (fun _ : SpinBranch => Ch06Ext.periodicTwist (2 * h)) = b from rfl,
    hback_zero, add_zero, hfwd]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hh0 : (2 * (h : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hh))
  push_cast
  field_simp [hh0]

theorem umklapp_witness_h2_coeff (gU : ℝ) :
    inner ℂ (umklappZeroChargeWitness 2 (by decide))
      (periodicUmklappOp 2 gU (A05.groundKet 2 (fun _ => 0))) = -((gU : ℂ) / 16) := by
  rw [umklapp_zero_charge_witness_coeff 2 (by decide) gU]
  norm_num

theorem umklapp_witness_h1_coeff (gU : ℝ) :
    inner ℂ (umklappZeroChargeWitness 1 (by decide))
      (periodicUmklappOp 1 gU (A05.groundKet 1 (fun _ => 0))) = -((gU : ℂ) / 4) := by
  rw [umklapp_zero_charge_witness_coeff 1 (by decide) gU]
  norm_num

/-- Non-invariance of every zero-charge budget under periodic Umklapp for `g_U ≠ 0`. -/
theorem umklapp_zero_budget_not_invariant (h : ℕ) (hh : 0 < h) (K : ℕ) (gU : ℝ)
    (hg : gU ≠ 0) :
    periodicUmklappOp h gU (A05.groundKet h (fun _ => 0)) ∉
      A05.jointBudget h (fun _ => 0) K := by
  intro hmem
  have hzero := umklappZeroChargeWitness_orthogonal_zero_budget h hh K _ hmem
  rw [umklapp_zero_charge_witness_coeff h hh gU] at hzero
  have hne : -((gU : ℂ) / ((2 * (h : ℂ)) ^ 2)) ≠ 0 := by
    have hgC : (gU : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
    have hhC : (h : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hh)
    have hden : ((2 * (h : ℂ)) ^ 2) ≠ 0 := pow_ne_zero 2 (mul_ne_zero two_ne_zero hhC)
    exact neg_ne_zero.mpr (div_ne_zero hgC hden)
  exact hne hzero

/-! ## 7. Concrete `h = 2` Finite-CAR Witnesses (`ex:ch21-pair-sign`, `ex:ch21-pair-residual`, `ex:ch21-u-inward-only`) -/

/-- Canonical momentum modes `{-1, 0, 1, 2}` in the four-site band `Ch01.Band (2 * 2)`. -/
def band4M1 : Ch01.Band (2 * 2) := ⟨-1, by simp [Ch01.inBandPredicate]⟩
def band4Zero : Ch01.Band (2 * 2) := ⟨0, by simp [Ch01.inBandPredicate]⟩
def band4One : Ch01.Band (2 * 2) := ⟨1, by simp [Ch01.inBandPredicate]⟩
def band4Two : Ch01.Band (2 * 2) := ⟨2, by simp [Ch01.inBandPredicate]⟩

lemma zeroCharge_admissible (h : ℕ) : A05.admissible h (fun _ : SpinBranch => (0 : ℤ)) :=
  fun _ => by unfold Ch07.admissible; dsimp; omega

lemma canonicalRoot_four_eq_I : A01.canonicalRoot 4 = Complex.I := by
  unfold A01.canonicalRoot
  have harg : 2 * (Real.pi : ℂ) * Complex.I / ((4 : ℕ) : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

private lemma norm4_sq : (A01.normalization (2 * 2) : ℂ) ^ 2 = (4 : ℂ)⁻¹ := by
  have hsq : ((2 * 2 : ℕ) : ℂ) * (A01.normalization (2 * 2) : ℂ) ^ 2 = 1 :=
    A01.normalization_square_complex (2 * 2)
  apply eq_inv_of_mul_eq_one_right
  simpa using hsq

private lemma erase_eq_erase_imp_eq {α : Type*} [DecidableEq α]
    {s : Finset α} {a b : α} (ha : a ∈ s)
    (heq : s.erase a = s.erase b) : a = b := by
  by_contra hne
  have hmem : a ∈ s.erase b := Finset.mem_erase.mpr ⟨hne, ha⟩
  rw [← heq] at hmem
  exact (Finset.mem_erase.mp hmem).1 rfl

private lemma sum_single_pair {ι : Type*} [Fintype ι]
    (a b : ι) (f : ι → ι → ℂ)
    (g : ι → ι → Prop) [∀ i j, Decidable (g i j)]
    (huniq : ∀ i j, g i j → i = a ∧ j = b)
    (hab : g a b) :
    (∑ i, ∑ j, if g i j then f i j else 0) = f a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro j _ hj
      have hnot : ¬ g a j := fun h => hj (huniq a j h).2
      simp [hnot]
    · simp
  · intro i _ hi
    have hzero : ∀ j, ¬ g i j := fun j h => hi (huniq i j h).1
    simp [hzero]
  · simp

private lemma twoSiteField_inner_unique (h : ℕ)
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * h))
    (S T : A05.Occupation SpinBranch h) (ν₁ ν₂ : SpinBranch) (x : ℤ)
    (a₁ a₂ : Ch01.Band (2 * h))
    (hmem₁ : (ν₁, a₁) ∈ S)
    (hmem₂ : (ν₂, a₂) ∈ S.erase (ν₁, a₁))
    (heqT : (S.erase (ν₁, a₁)).erase (ν₂, a₂) = T)
    (huniq : ∀ k₁ k₂, (ν₁, k₁) ∈ S ∧ (ν₂, k₂) ∈ S.erase (ν₁, k₁) ∧
        (S.erase (ν₁, k₁)).erase (ν₂, k₂) = T → k₁ = a₁ ∧ k₂ = a₂) :
    inner ℂ (A02.ket T) (siteField h b ν₂ x (siteField h b ν₁ x (A02.ket S))) =
      ((A01.normalization (2 * h) : ℂ) ^ 2) *
        (Ch06Ext.twistedCharacter (2 * h) (b ν₂) a₂ x *
          Ch04.fermionSign (ν₂, a₂) (S.erase (ν₁, a₁)) *
          (Ch06Ext.twistedCharacter (2 * h) (b ν₁) a₁ x *
            Ch04.fermionSign (ν₁, a₁) S)) := by
  rw [twoSiteField_ket, inner_smul_right]
  congr 1
  simp_rw [inner_sum]
  let g (k₁ k₂ : Ch01.Band (2 * h)) : Prop :=
    (ν₁, k₁) ∈ S ∧ (ν₂, k₂) ∈ S.erase (ν₁, k₁) ∧ (S.erase (ν₁, k₁)).erase (ν₂, k₂) = T
  have hre : (∑ k₁ : Ch01.Band (2 * h), ∑ k₂ : Ch01.Band (2 * h),
      inner ℂ (A02.ket T)
        (if (ν₁, k₁) ∈ S ∧ (ν₂, k₂) ∈ S.erase (ν₁, k₁) then
          (Ch06Ext.twistedCharacter (2 * h) (b ν₂) k₂ x *
            Ch04.fermionSign (ν₂, k₂) (S.erase (ν₁, k₁)) *
            (Ch06Ext.twistedCharacter (2 * h) (b ν₁) k₁ x *
              Ch04.fermionSign (ν₁, k₁) S)) •
            A02.ket ((S.erase (ν₁, k₁)).erase (ν₂, k₂))
        else 0)) =
      ∑ k₁ : Ch01.Band (2 * h), ∑ k₂ : Ch01.Band (2 * h),
        if g k₁ k₂ then
          Ch06Ext.twistedCharacter (2 * h) (b ν₂) k₂ x *
            Ch04.fermionSign (ν₂, k₂) (S.erase (ν₁, k₁)) *
            (Ch06Ext.twistedCharacter (2 * h) (b ν₁) k₁ x *
              Ch04.fermionSign (ν₁, k₁) S)
        else 0 := by
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun k₂ _ => ?_))
    dsimp only [g]
    by_cases h12 : (ν₁, k₁) ∈ S ∧ (ν₂, k₂) ∈ S.erase (ν₁, k₁)
    · rw [ite_eq_left h12, inner_smul_right, A02.ket_inner]
      by_cases hT : (S.erase (ν₁, k₁)).erase (ν₂, k₂) = T
      · rw [ite_eq_left hT.symm, mul_one, ite_eq_left ⟨h12.1, h12.2, hT⟩]
      · rw [ite_eq_right (fun h => hT h.symm), mul_zero, ite_eq_right (fun h => hT h.2.2)]
    · rw [ite_eq_right h12, inner_zero_right, ite_eq_right (fun h => h12 ⟨h.1, h.2.1⟩)]
  rw [hre]
  exact sum_single_pair a₁ a₂ _ g huniq ⟨hmem₁, hmem₂, heqT⟩

private lemma twoSiteField_unique_pair_of_distinct (h : ℕ)
    (S : A05.Occupation SpinBranch h) (ν₁ ν₂ : SpinBranch) (hν : ν₁ ≠ ν₂)
    (a₁ a₂ : Ch01.Band (2 * h)) :
    ∀ k₁ k₂,
      (ν₁, k₁) ∈ S ∧ (ν₂, k₂) ∈ S.erase (ν₁, k₁) ∧
      (S.erase (ν₁, k₁)).erase (ν₂, k₂) = (S.erase (ν₁, a₁)).erase (ν₂, a₂) →
      k₁ = a₁ ∧ k₂ = a₂ := by
  intro k₁ k₂ ⟨hk₁, hk₂, heq⟩
  have hspec₁ := congrArg (fun U => Ch07.speciesConfiguration h U ν₁) heq
  have hspec₂ := congrArg (fun U => Ch07.speciesConfiguration h U ν₂) heq
  simp only [speciesConfiguration_erase_ch21, ite_eq_right hν, ite_eq_right hν.symm] at hspec₁ hspec₂
  have hk₁S : k₁ ∈ Ch07.speciesConfiguration h S ν₁ :=
    Finset.mem_image.mpr ⟨(ν₁, k₁), Finset.mem_filter.mpr ⟨hk₁, rfl⟩, rfl⟩
  have hk₂S : k₂ ∈ Ch07.speciesConfiguration h S ν₂ :=
    Finset.mem_image.mpr ⟨(ν₂, k₂), Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hk₂, rfl⟩, rfl⟩
  exact ⟨erase_eq_erase_imp_eq hk₁S hspec₁, erase_eq_erase_imp_eq hk₂S hspec₂⟩

private lemma band4_ground0_card : (Ch07.groundConfiguration 2 0).card = 2 := by
  have hz := Ch07.ground_configuration_card 2 (by decide) 0 (by unfold Ch07.admissible; omega)
  omega

private lemma band4_groundM1_card : (Ch07.groundConfiguration 2 (-1)).card = 1 := by
  have hz := Ch07.ground_configuration_card 2 (by decide) (-1) (by unfold Ch07.admissible; omega)
  omega

private lemma band4_prec_zero_ground0 :
    Ch04.precedingCount band4Zero (Ch07.groundConfiguration 2 0) = 1 := by
  have hfilt : (Ch07.groundConfiguration 2 0).filter (· < band4Zero) =
      Ch07.groundConfiguration 2 (-1) := by
    ext l
    simp only [Finset.mem_filter, Ch07.groundConfiguration, Finset.mem_univ, true_and]
    change (l.val ≤ 0 ∧ l.val < (0 : ℤ)) ↔ l.val ≤ -1
    omega
  unfold Ch04.precedingCount
  rw [hfilt]
  exact band4_groundM1_card

private lemma band4_prec_m1 (S : Ch07.Occupation 2) :
    Ch04.precedingCount band4M1 S = 0 := by
  unfold Ch04.precedingCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l _
  have hl := l.property
  simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hl
  change ¬ (l.val < (-1 : ℤ))
  omega

private lemma band4_erase_zero_ground0 :
    (Ch07.groundConfiguration 2 0).erase band4Zero = Ch07.groundConfiguration 2 (-1) := by
  ext l
  simp only [Finset.mem_erase, Ch07.groundConfiguration, Finset.mem_filter, Finset.mem_univ,
    true_and, ne_eq, Subtype.ext_iff, band4Zero]
  omega

/-! ### 7.1 Spin-Singlet Pair Sign Witness (`ex:ch21-pair-sign`, `±1/4` at `h = 2`) -/

theorem singlet_pair_sign_channel1_h2 :
    inner ℂ (A05.groundKet 2 (Ch20.scTarget singletBranchesB (fun _ => 0)))
      (Ch20.orderSC 2 (fun _ => Ch06Ext.periodicTwist (2 * 2)) singletBranchesB 1
        (A05.groundKet 2 (fun _ => 0))) = -(1 / 4 : ℂ) := by
  let b : SpinBranch → Ch06Ext.BoundaryTwist (2 * 2) := fun _ => Ch06Ext.periodicTwist (2 * 2)
  let S₀ : A05.Occupation SpinBranch 2 := A05.groundConfiguration 2 (fun _ => 0)
  let T₁ : A05.Occupation SpinBranch 2 :=
    A05.groundConfiguration 2 (Ch20.scTarget singletBranchesB (fun _ => 0))
  have hS0_mem (ν : SpinBranch) (k : Ch01.Band (2 * 2)) :
      (ν, k) ∈ S₀ ↔ k ∈ Ch07.groundConfiguration 2 0 := by
    simp [S₀, A05.groundConfiguration, A05.jointConfiguration]
  have hS0_spec (ν : SpinBranch) :
      Ch07.speciesConfiguration 2 S₀ ν = Ch07.groundConfiguration 2 0 :=
    A05.species_joint_configuration 2 (fun _ => Ch07.groundConfiguration 2 0) ν
  have hz0 : band4Zero ∈ Ch07.groundConfiguration 2 0 := by
    simp [Ch07.groundConfiguration, band4Zero]
  have ha₁ : (brLDown, band4Zero) ∈ S₀ := (hS0_mem brLDown band4Zero).mpr hz0
  have ha₂ : (brRUp, band4Zero) ∈ S₀ := (hS0_mem brRUp band4Zero).mpr hz0
  have ha₂' : (brRUp, band4Zero) ∈ S₀.erase (brLDown, band4Zero) :=
    Finset.mem_erase.mpr ⟨fun h => brLDown_ne_brRUp.symm (congrArg Prod.fst h), ha₂⟩
  have hT1_mem (ν : SpinBranch) (k : Ch01.Band (2 * 2)) :
      (ν, k) ∈ T₁ ↔ k ∈ Ch07.groundConfiguration 2 (Ch20.scTarget singletBranchesB (fun _ => 0) ν) := by
    simp [T₁, A05.groundConfiguration, A05.jointConfiguration]
  have heqT : (S₀.erase (brLDown, band4Zero)).erase (brRUp, band4Zero) = T₁ := by
    ext ⟨ν, k⟩
    simp only [Finset.mem_erase, ne_eq, Prod.mk.injEq, hS0_mem, hT1_mem]
    fin_cases ν <;>
      simp [Ch20.scTarget_apply, Ch20.scShift, singletBranchesB, brLDown, brRUp,
        Ch07.groundConfiguration, band4Zero, Subtype.ext_iff] <;> omega
  have huniq := twoSiteField_unique_pair_of_distinct 2 S₀ brLDown brRUp brLDown_ne_brRUp
    band4Zero band4Zero
  rw [show Ch20.orderSC 2 b singletBranchesB 1 (A05.groundKet 2 (fun _ => 0)) =
      siteField 2 b brRUp 1 (siteField 2 b brLDown 1 (A02.ket S₀)) from rfl]
  change inner ℂ (A02.ket T₁) (siteField 2 b brRUp 1 (siteField 2 b brLDown 1 (A02.ket S₀))) = _
  rw [twoSiteField_inner_unique 2 b S₀ T₁ brLDown brRUp 1 band4Zero band4Zero ha₁ ha₂' heqT
    (fun k₁ k₂ h => huniq k₁ k₂ ⟨h.1, h.2.1, h.2.2.trans heqT.symm⟩)]
  have hp1 : Ch04.precedingCount (brLDown, band4Zero) S₀ = 3 := by
    rw [A05.preceding_count_split]
    have hfilt : (Finset.univ.filter (· < brLDown) : Finset SpinBranch) = {brLUp} := by decide
    rw [hfilt, Finset.sum_singleton, hS0_spec brLUp, hS0_spec brLDown,
      band4_ground0_card, band4_prec_zero_ground0]
  have hp2 : Ch04.precedingCount (brRUp, band4Zero) (S₀.erase (brLDown, band4Zero)) = 4 := by
    rw [A05.preceding_count_split]
    have hfilt : (Finset.univ.filter (· < brRUp) : Finset SpinBranch) = {brLUp, brLDown} := by
      decide
    rw [hfilt, Finset.sum_insert (by decide), Finset.sum_singleton,
      speciesConfiguration_erase_ch21, speciesConfiguration_erase_ch21,
      speciesConfiguration_erase_ch21,
      ite_eq_right brLUp_ne_brLDown, ite_eq_left rfl, ite_eq_right brLDown_ne_brRUp.symm,
      hS0_spec brLUp, hS0_spec brLDown, hS0_spec brRUp,
      band4_erase_zero_ground0, band4_ground0_card, band4_groundM1_card, band4_prec_zero_ground0]
  have htw (ν : SpinBranch) : Ch06Ext.twistedCharacter (2 * 2) (b ν) band4Zero 1 = 1 := by
    simp [b, Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, Ch06Ext.periodicTwist,
      A01.integerCharacter, band4Zero]
  unfold Ch04.fermionSign
  rw [hp1, hp2, htw brRUp, norm4_sq]
  norm_num

theorem singlet_pair_sign_channel2_h2 :
    inner ℂ (A05.groundKet 2 (Ch20.scTarget singletBranchesA (fun _ => 0)))
      (Ch20.orderSC 2 (fun _ => Ch06Ext.periodicTwist (2 * 2)) singletBranchesA 1
        (A05.groundKet 2 (fun _ => 0))) = -(1 / 4 : ℂ) := by
  let b : SpinBranch → Ch06Ext.BoundaryTwist (2 * 2) := fun _ => Ch06Ext.periodicTwist (2 * 2)
  let S₀ : A05.Occupation SpinBranch 2 := A05.groundConfiguration 2 (fun _ => 0)
  let T₂ : A05.Occupation SpinBranch 2 :=
    A05.groundConfiguration 2 (Ch20.scTarget singletBranchesA (fun _ => 0))
  have hS0_mem (ν : SpinBranch) (k : Ch01.Band (2 * 2)) :
      (ν, k) ∈ S₀ ↔ k ∈ Ch07.groundConfiguration 2 0 := by
    simp [S₀, A05.groundConfiguration, A05.jointConfiguration]
  have hS0_spec (ν : SpinBranch) :
      Ch07.speciesConfiguration 2 S₀ ν = Ch07.groundConfiguration 2 0 :=
    A05.species_joint_configuration 2 (fun _ => Ch07.groundConfiguration 2 0) ν
  have hz0 : band4Zero ∈ Ch07.groundConfiguration 2 0 := by
    simp [Ch07.groundConfiguration, band4Zero]
  have ha₁ : (brLUp, band4Zero) ∈ S₀ := (hS0_mem brLUp band4Zero).mpr hz0
  have ha₂ : (brRDown, band4Zero) ∈ S₀ := (hS0_mem brRDown band4Zero).mpr hz0
  have ha₂' : (brRDown, band4Zero) ∈ S₀.erase (brLUp, band4Zero) :=
    Finset.mem_erase.mpr ⟨fun h => brLUp_ne_brRDown.symm (congrArg Prod.fst h), ha₂⟩
  have hT2_mem (ν : SpinBranch) (k : Ch01.Band (2 * 2)) :
      (ν, k) ∈ T₂ ↔ k ∈ Ch07.groundConfiguration 2 (Ch20.scTarget singletBranchesA (fun _ => 0) ν) := by
    simp [T₂, A05.groundConfiguration, A05.jointConfiguration]
  have heqT : (S₀.erase (brLUp, band4Zero)).erase (brRDown, band4Zero) = T₂ := by
    ext ⟨ν, k⟩
    simp only [Finset.mem_erase, ne_eq, Prod.mk.injEq, hS0_mem, hT2_mem]
    fin_cases ν <;>
      simp [Ch20.scTarget_apply, Ch20.scShift, singletBranchesA, brLUp, brRDown,
        Ch07.groundConfiguration, band4Zero, Subtype.ext_iff] <;> omega
  have huniq := twoSiteField_unique_pair_of_distinct 2 S₀ brLUp brRDown brLUp_ne_brRDown
    band4Zero band4Zero
  rw [show Ch20.orderSC 2 b singletBranchesA 1 (A05.groundKet 2 (fun _ => 0)) =
      siteField 2 b brRDown 1 (siteField 2 b brLUp 1 (A02.ket S₀)) from rfl]
  change inner ℂ (A02.ket T₂) (siteField 2 b brRDown 1 (siteField 2 b brLUp 1 (A02.ket S₀))) = _
  rw [twoSiteField_inner_unique 2 b S₀ T₂ brLUp brRDown 1 band4Zero band4Zero ha₁ ha₂' heqT
    (fun k₁ k₂ h => huniq k₁ k₂ ⟨h.1, h.2.1, h.2.2.trans heqT.symm⟩)]
  have hp1 : Ch04.precedingCount (brLUp, band4Zero) S₀ = 1 := by
    rw [A05.preceding_count_split]
    have hfilt : (Finset.univ.filter (· < brLUp) : Finset SpinBranch) = ∅ := by decide
    rw [hfilt, Finset.sum_empty, zero_add, hS0_spec brLUp, band4_prec_zero_ground0]
  have hp2 : Ch04.precedingCount (brRDown, band4Zero) (S₀.erase (brLUp, band4Zero)) = 6 := by
    rw [A05.preceding_count_split]
    have hfilt : (Finset.univ.filter (· < brRDown) : Finset SpinBranch) =
        {brLUp, brLDown, brRUp} := by decide
    rw [hfilt, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      speciesConfiguration_erase_ch21, speciesConfiguration_erase_ch21,
      speciesConfiguration_erase_ch21, speciesConfiguration_erase_ch21,
      ite_eq_left rfl, ite_eq_right brLUp_ne_brLDown.symm,
      ite_eq_right brLUp_ne_brRUp.symm, ite_eq_right brLUp_ne_brRDown.symm,
      hS0_spec brLUp, hS0_spec brLDown, hS0_spec brRUp, hS0_spec brRDown,
      band4_erase_zero_ground0, band4_groundM1_card, band4_ground0_card, band4_prec_zero_ground0]
    norm_num
  have htw (ν : SpinBranch) : Ch06Ext.twistedCharacter (2 * 2) (b ν) band4Zero 1 = 1 := by
    simp [b, Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, Ch06Ext.periodicTwist,
      A01.integerCharacter, band4Zero]
  unfold Ch04.fermionSign
  rw [hp1, hp2, htw brRDown, norm4_sq]
  norm_num

/-- Opposite singlet ground-to-ground amplitudes `⟨Ω_{T₁}, O_{SSC}(1) Ω₀⟩ = -1/4` and
`⟨Ω_{T₂}, O_{SSC}(1) Ω₀⟩ = +1/4` at `h = 2, L = 4` (`ex:ch21-pair-sign`). -/
theorem singlet_pair_sign_h2 :
    inner ℂ (A05.groundKet 2 (Ch20.scTarget singletBranchesB (fun _ => 0)))
      (singletOrderSC 2 (fun _ => Ch06Ext.periodicTwist (2 * 2)) 1
        (A05.groundKet 2 (fun _ => 0))) = -(1 / 4 : ℂ) ∧
    inner ℂ (A05.groundKet 2 (Ch20.scTarget singletBranchesA (fun _ => 0)))
      (singletOrderSC 2 (fun _ => Ch06Ext.periodicTwist (2 * 2)) 1
        (A05.groundKet 2 (fun _ => 0))) = (1 / 4 : ℂ) := by
  let b : SpinBranch → Ch06Ext.BoundaryTwist (2 * 2) := fun _ => Ch06Ext.periodicTwist (2 * 2)
  have h0sec : A05.groundKet 2 (fun _ => 0) ∈ chargeSector 2 (fun _ => 0) :=
    jointBudget_le_chargeSector 2 (fun _ => 0) 0
      (A05.ground_mem_budget 2 (by decide) (fun _ => 0) (zeroCharge_admissible 2) 0)
  have hTB_adm : A05.admissible 2 (Ch20.scTarget singletBranchesB (fun _ => 0)) := by
    intro ν; fin_cases ν <;>
      simp [Ch07.admissible, Ch20.scTarget_apply, Ch20.scShift, singletBranchesB, brLDown, brRUp]
  have hTA_adm : A05.admissible 2 (Ch20.scTarget singletBranchesA (fun _ => 0)) := by
    intro ν; fin_cases ν <;>
      simp [Ch07.admissible, Ch20.scTarget_apply, Ch20.scShift, singletBranchesA, brLUp, brRDown]
  have hTB_sec : A05.groundKet 2 (Ch20.scTarget singletBranchesB (fun _ => 0)) ∈
      chargeSector 2 (Ch20.scTarget singletBranchesB (fun _ => 0)) :=
    jointBudget_le_chargeSector 2 _ 0 (A05.ground_mem_budget 2 (by decide) _ hTB_adm 0)
  have hTA_sec : A05.groundKet 2 (Ch20.scTarget singletBranchesA (fun _ => 0)) ∈
      chargeSector 2 (Ch20.scTarget singletBranchesA (fun _ => 0)) :=
    jointBudget_le_chargeSector 2 _ 0 (A05.ground_mem_budget 2 (by decide) _ hTA_adm 0)
  have hcross1 : inner ℂ (A05.groundKet 2 (Ch20.scTarget singletBranchesB (fun _ => 0)))
      (Ch20.orderSC 2 b singletBranchesA 1 (A05.groundKet 2 (fun _ => 0))) = 0 :=
    distinct_charge_sectors_orthogonal 2 _ _ (singlet_targets_distinct (fun _ => 0)).symm
      _ hTB_sec _ (orderSC_maps_sector 2 b singletBranchesA 1 (fun _ => 0) _ h0sec)
  have hcross2 : inner ℂ (A05.groundKet 2 (Ch20.scTarget singletBranchesA (fun _ => 0)))
      (Ch20.orderSC 2 b singletBranchesB 1 (A05.groundKet 2 (fun _ => 0))) = 0 :=
    distinct_charge_sectors_orthogonal 2 _ _ (singlet_targets_distinct (fun _ => 0))
      _ hTA_sec _ (orderSC_maps_sector 2 b singletBranchesB 1 (fun _ => 0) _ h0sec)
  constructor
  · change inner ℂ (A05.groundKet 2 (Ch20.scTarget singletBranchesB (fun _ => 0)))
      (singletOrderSC 2 b 1 (A05.groundKet 2 (fun _ => 0))) = _
    simp only [singletOrderSC, LinearMap.sub_apply, inner_sub_right, hcross1, sub_zero]
    exact singlet_pair_sign_channel1_h2
  · change inner ℂ (A05.groundKet 2 (Ch20.scTarget singletBranchesA (fun _ => 0)))
      (singletOrderSC 2 b 1 (A05.groundKet 2 (fun _ => 0))) = _
    simp only [singletOrderSC, LinearMap.sub_apply, inner_sub_right, hcross2, zero_sub]
    rw [singlet_pair_sign_channel2_h2]
    ring

/-! ### 7.2 Singlet Intermediate-Projection Residual Witness (`ex:ch21-pair-residual`, `-i/4` at `h = 2`) -/

/-- Witness target configuration `Ξ` obtained from `Ω₀` by removing `(L↓, -1)` and `(R↑, 0)`. -/
noncomputable def singletResidualWitnessConfig : A05.Occupation SpinBranch 2 :=
  ((A05.groundConfiguration 2 (fun _ => 0)).erase (brLDown, band4M1)).erase (brRUp, band4Zero)

/-- Witness ket `|Ξ⟩` in channel-1 target budget `V_{T₁, 1}` (`ex:ch21-pair-residual`). -/
noncomputable def singletResidualWitnessKet : A05.FockSpace SpinBranch 2 :=
  A02.ket singletResidualWitnessConfig

lemma singletResidualWitnessKet_mem_target :
    singletResidualWitnessKet ∈
      A05.jointBudget 2 (Ch20.scTarget singletBranchesB (fun _ => 0)) 1 := by
  rw [singletResidualWitnessKet, ← ket_instDecidableEqProd_eq 2 singletResidualWitnessConfig]
  rw [A05.jointBudget, Ch07.species_budget_ket]
  have hS0_spec (ν : SpinBranch) :
      Ch07.speciesConfiguration 2 (A05.groundConfiguration 2 (fun _ => 0)) ν =
        Ch07.groundConfiguration 2 0 :=
    A05.species_joint_configuration 2 (fun _ => Ch07.groundConfiguration 2 0) ν
  have hspec0 : Ch07.speciesConfiguration 2 singletResidualWitnessConfig brLUp =
      Ch07.groundConfiguration 2 0 := by
    unfold singletResidualWitnessConfig
    rw [speciesConfiguration_erase_ch21, speciesConfiguration_erase_ch21,
      ite_eq_right brLUp_ne_brRUp, ite_eq_right brLUp_ne_brLDown, hS0_spec]
  have hspec1 : Ch07.speciesConfiguration 2 singletResidualWitnessConfig brLDown =
      (Ch07.groundConfiguration 2 0).erase band4M1 := by
    unfold singletResidualWitnessConfig
    rw [speciesConfiguration_erase_ch21, speciesConfiguration_erase_ch21,
      ite_eq_right brLDown_ne_brRUp, ite_eq_left rfl, hS0_spec]
  have hspec2 : Ch07.speciesConfiguration 2 singletResidualWitnessConfig brRUp =
      Ch07.groundConfiguration 2 (-1) := by
    unfold singletResidualWitnessConfig
    rw [speciesConfiguration_erase_ch21, ite_eq_left rfl,
      speciesConfiguration_erase_ch21, ite_eq_right brLDown_ne_brRUp.symm,
      hS0_spec, band4_erase_zero_ground0]
  have hspec3 : Ch07.speciesConfiguration 2 singletResidualWitnessConfig brRDown =
      Ch07.groundConfiguration 2 0 := by
    unfold singletResidualWitnessConfig
    rw [speciesConfiguration_erase_ch21, speciesConfiguration_erase_ch21,
      ite_eq_right brRUp_ne_brRDown.symm, ite_eq_right brLDown_ne_brRDown.symm, hS0_spec]
  have hm1_mem : band4M1 ∈ Ch07.groundConfiguration 2 0 := by
    simp [Ch07.groundConfiguration, band4M1]
  have h0adm : Ch07.admissible 2 0 := by unfold Ch07.admissible; omega
  have hm1adm : Ch07.admissible 2 (-1) := by unfold Ch07.admissible; omega
  have hchg0 : Ch07.relativeCharge 2 (Ch07.groundConfiguration 2 0) = 0 :=
    Ch07.ground_configuration_charge 2 (by decide) 0 h0adm
  have hchgm1 : Ch07.relativeCharge 2 (Ch07.groundConfiguration 2 (-1)) = -1 :=
    Ch07.ground_configuration_charge 2 (by decide) (-1) hm1adm
  have hexc0 : Ch07.excitationEnergy 2 (Ch07.groundConfiguration 2 0) = 0 :=
    Ch07.ground_configuration_excitation 2 (by decide) 0 h0adm
  have hexcm1 : Ch07.excitationEnergy 2 (Ch07.groundConfiguration 2 (-1)) = 0 :=
    Ch07.ground_configuration_excitation 2 (by decide) (-1) hm1adm
  have hexc_er : Ch07.excitationEnergy 2 ((Ch07.groundConfiguration 2 0).erase band4M1) = 1 := by
    rw [Ch07.excitation_erase 2 _ band4M1 hm1_mem, hexc0, hchg0]
    simp [band4M1]
  refine ⟨?_, ?_⟩
  · intro ν
    fin_cases ν
    · change Ch07.relativeCharge 2 (Ch07.speciesConfiguration 2 singletResidualWitnessConfig brLUp) = _
      rw [hspec0, hchg0]
      simp [Ch20.scTarget_apply, Ch20.scShift, singletBranchesB, brLDown, brRUp]
    · change Ch07.relativeCharge 2 (Ch07.speciesConfiguration 2 singletResidualWitnessConfig brLDown) = _
      rw [hspec1, Ch07.charge_erase 2 _ band4M1 hm1_mem, hchg0]
      simp [Ch20.scTarget_apply, Ch20.scShift, singletBranchesB, brLDown, brRUp]
    · change Ch07.relativeCharge 2 (Ch07.speciesConfiguration 2 singletResidualWitnessConfig brRUp) = _
      rw [hspec2, hchgm1]
      simp [Ch20.scTarget_apply, Ch20.scShift, singletBranchesB, brLDown, brRUp]
    · change Ch07.relativeCharge 2 (Ch07.speciesConfiguration 2 singletResidualWitnessConfig brRDown) = _
      rw [hspec3, hchg0]
      simp [Ch20.scTarget_apply, Ch20.scShift, singletBranchesB, brLDown, brRUp]
  · unfold Ch07.totalExcitation
    rw [Fin.sum_univ_four]
    change Ch07.excitationEnergy 2 (Ch07.speciesConfiguration 2 singletResidualWitnessConfig brLUp) +
        Ch07.excitationEnergy 2 (Ch07.speciesConfiguration 2 singletResidualWitnessConfig brLDown) +
        Ch07.excitationEnergy 2 (Ch07.speciesConfiguration 2 singletResidualWitnessConfig brRUp) +
        Ch07.excitationEnergy 2 (Ch07.speciesConfiguration 2 singletResidualWitnessConfig brRDown) ≤ _
    rw [hspec0, hspec1, hspec2, hspec3, hexc0, hexc_er, hexcm1]
    norm_num

/-- Subtype vector `⟨|Ξ⟩, _⟩ ∈ V_{T₁, 1}` for `ex:ch21-pair-residual`. -/
noncomputable def singletResidualWitnessVec :
    A05.jointBudget 2 (Ch20.scTarget singletBranchesB (fun _ => 0)) 1 :=
  ⟨singletResidualWitnessKet, singletResidualWitnessKet_mem_target⟩

/-- Intermediate-projected composition vanishes on `|Ξ⟩`:
`⟨Ξ, (B_{a,1} ∘ B_{b,1}) Ω₀⟩ = 0` at `h = 2, J_s = 0, J_{m,1} = 0, J_{t,1} = 1`. -/
theorem singlet_pair_residual_comp_zero_h2 :
    inner ℂ singletResidualWitnessVec
      ((Ch14.projectedMap 2
          (Ch13.lowerCharge (fun _ => 0) singletBranchesB.leftSpecies)
          (Ch20.scTarget singletBranchesB (fun _ => 0)) 0 1
          (Ch20.fieldOf 2 (fun _ => Ch06Ext.periodicTwist (2 * 2)) singletBranchesB.rightSpecies 1) ∘ₗ
        Ch14.projectedMap 2 (fun _ => 0)
          (Ch13.lowerCharge (fun _ => 0) singletBranchesB.leftSpecies) 0 0
          (Ch20.fieldOf 2 (fun _ => Ch06Ext.periodicTwist (2 * 2)) singletBranchesB.leftSpecies 1))
        (Ch14.groundVector 2 (by decide) (fun _ => 0) (zeroCharge_admissible 2) 0)) = 0 := by
  let b : SpinBranch → Ch06Ext.BoundaryTwist (2 * 2) := fun _ => Ch06Ext.periodicTwist (2 * 2)
  let M₁ := Ch13.lowerCharge (fun _ => 0) singletBranchesB.leftSpecies
  let T₁ := Ch20.scTarget singletBranchesB (fun _ => 0)
  let w : A05.jointBudget 2 M₁ 0 :=
    Ch14.projectedMap 2 (fun _ => 0) M₁ 0 0 (Ch20.fieldOf 2 b singletBranchesB.leftSpecies 1)
      (Ch14.groundVector 2 (by decide) (fun _ => 0) (zeroCharge_admissible 2) 0)
  have hgoal : ∀ u ∈ A05.jointBudget 2 M₁ 0,
      inner ℂ singletResidualWitnessKet
        (Ch14.projection 2 T₁ 1 (siteField 2 b brRUp 1 u)) = 0 := by
    intro u hu
    have hPfix : Ch14.projection 2 T₁ 1 singletResidualWitnessKet = singletResidualWitnessKet := by
      rw [ch14_projection_eq_prod]
      exact (@A03.projection_fixed_iff (A05.Mode SpinBranch 2) _ instDecidableEqProd
        (Ch14.budgetSet 2 T₁ 1) singletResidualWitnessKet).mpr singletResidualWitnessKet_mem_target
    have hPadj : LinearMap.adjoint (Ch14.projection 2 T₁ 1) = Ch14.projection 2 T₁ 1 := by
      rw [ch14_projection_eq_prod]
      exact @A03.projection_adjoint (A05.Mode SpinBranch 2) _ instDecidableEqProd _
    rw [← LinearMap.adjoint_inner_left, hPadj, hPfix]
    change u ∈ @A03.coordinateSpace (A05.Mode SpinBranch 2) _ instDecidableEqProd
      (Ch14.budgetSet 2 M₁ 0) at hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨U, hU, rfl⟩ := hx
      rw [ket_instDecidableEqProd_eq, siteField_ket, inner_smul_right, inner_sum]
      have hU_exc0 : Ch07.excitationEnergy 2 (Ch07.speciesConfiguration 2 U brLDown) = 0 := by
        have htot := hU.2
        unfold Ch07.totalExcitation at htot
        rw [Fin.sum_univ_four] at htot
        have hnn (ν : SpinBranch) : 0 ≤ Ch07.excitationEnergy 2 (Ch07.speciesConfiguration 2 U ν) :=
          Ch07.excitation_nonneg 2 (by decide) _
        have h0 := hnn 0; have h1 := hnn 1; have h2 := hnn 2; have h3 := hnn 3
        change Ch07.excitationEnergy 2 (Ch07.speciesConfiguration 2 U 1) = 0
        omega
      have hU_ld : Ch07.speciesConfiguration 2 U brLDown = Ch07.groundConfiguration 2 (-1) := by
        have hgr := (Ch07.excitation_zero_iff_ground 2 (by decide) _).mp hU_exc0
        have hchg : Ch07.relativeCharge 2 (Ch07.speciesConfiguration 2 U brLDown) = -1 := by
          simpa [M₁, Ch13.lowerCharge, singletBranchesB] using hU.1 brLDown
        rw [hchg] at hgr
        exact hgr
      have hsum0 : (∑ k : Ch01.Band (2 * 2), inner ℂ singletResidualWitnessKet
          (if (brRUp, k) ∈ U then
            (Ch06Ext.twistedCharacter (2 * 2) (b brRUp) k 1 * Ch04.fermionSign (brRUp, k) U) •
              A02.ket (U.erase (brRUp, k))
          else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        by_cases hk : (brRUp, k) ∈ U
        · rw [ite_eq_left hk, inner_smul_right, singletResidualWitnessKet, A02.ket_inner]
          have hne : singletResidualWitnessConfig ≠ U.erase (brRUp, k) := by
            intro heq
            have hsp := congrArg (fun V => Ch07.speciesConfiguration 2 V brLDown) heq
            rw [speciesConfiguration_erase_ch21, ite_eq_right brLDown_ne_brRUp, hU_ld] at hsp
            have hmemL : band4Zero ∈
                Ch07.speciesConfiguration 2 singletResidualWitnessConfig brLDown := by
              unfold singletResidualWitnessConfig
              rw [speciesConfiguration_erase_ch21, speciesConfiguration_erase_ch21,
                ite_eq_right brLDown_ne_brRUp, ite_eq_left rfl]
              unfold A05.groundConfiguration
              rw [A05.species_joint_configuration 2 (fun _ => Ch07.groundConfiguration 2 0) brLDown]
              simp [Finset.mem_erase, Ch07.groundConfiguration, band4Zero, band4M1, Subtype.ext_iff]
            rw [hsp] at hmemL
            simp [Ch07.groundConfiguration, band4Zero] at hmemL
          simp [hne]
        · simp [hk]
      rw [hsum0, mul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, inner_smul_right, hx, mul_zero]
  exact hgoal w.val w.property

/-- Concrete singlet intermediate-projection residual witness (`ex:ch21-pair-residual`):
`⟨Ξ, R₁ Ω₀⟩ = -i/4` at `h = 2, L = 4, x = 1, J_s = 0, J_{m,1} = 0, J_{t,1} = 1`. -/
theorem singlet_pair_residual_witness_h2 :
    inner ℂ singletResidualWitnessVec
      (Ch14.projectedMap 2 (fun _ => 0) (Ch20.scTarget singletBranchesB (fun _ => 0)) 0 1
        (Ch20.scResidualOp 2 (fun _ => Ch06Ext.periodicTwist (2 * 2)) singletBranchesB 1 (fun _ => 0) 0)
        (Ch14.groundVector 2 (by decide) (fun _ => 0) (zeroCharge_admissible 2) 0)) =
      -(Complex.I / 4) := by
  let b : SpinBranch → Ch06Ext.BoundaryTwist (2 * 2) := fun _ => Ch06Ext.periodicTwist (2 * 2)
  let T₁ := Ch20.scTarget singletBranchesB (fun _ => 0)
  let v₀ := Ch14.groundVector 2 (by decide) (fun _ => 0) (zeroCharge_admissible 2) 0
  have hsplit := congrArg (fun F => inner ℂ singletResidualWitnessVec (F v₀))
    (singletB_projected_residual 2 b 1 (fun _ => 0) 0 0 1)
  dsimp only [b, v₀] at hsplit
  simp only [LinearMap.add_apply, inner_add_right, singlet_pair_residual_comp_zero_h2,
    zero_add] at hsplit
  rw [← hsplit]
  have hPfix : Ch14.projection 2 T₁ 1 singletResidualWitnessKet = singletResidualWitnessKet := by
    rw [ch14_projection_eq_prod]
    exact (@A03.projection_fixed_iff (A05.Mode SpinBranch 2) _ instDecidableEqProd
      (Ch14.budgetSet 2 T₁ 1) singletResidualWitnessKet).mpr singletResidualWitnessKet_mem_target
  have hPadj : LinearMap.adjoint (Ch14.projection 2 T₁ 1) = Ch14.projection 2 T₁ 1 := by
    rw [ch14_projection_eq_prod]
    exact @A03.projection_adjoint (A05.Mode SpinBranch 2) _ instDecidableEqProd _
  change inner ℂ singletResidualWitnessKet
      (Ch14.projection 2 T₁ 1 (Ch20.orderSC 2 b singletBranchesB 1 (A05.groundKet 2 (fun _ => 0)))) = _
  rw [← LinearMap.adjoint_inner_left, hPadj, hPfix]
  let S₀ : A05.Occupation SpinBranch 2 := A05.groundConfiguration 2 (fun _ => 0)
  have hS0_mem (ν : SpinBranch) (k : Ch01.Band (2 * 2)) :
      (ν, k) ∈ S₀ ↔ k ∈ Ch07.groundConfiguration 2 0 := by
    simp [S₀, A05.groundConfiguration, A05.jointConfiguration]
  have hS0_spec (ν : SpinBranch) :
      Ch07.speciesConfiguration 2 S₀ ν = Ch07.groundConfiguration 2 0 :=
    A05.species_joint_configuration 2 (fun _ => Ch07.groundConfiguration 2 0) ν
  have ha₁ : (brLDown, band4M1) ∈ S₀ := (hS0_mem brLDown band4M1).mpr (by
    simp [Ch07.groundConfiguration, band4M1])
  have ha₂ : (brRUp, band4Zero) ∈ S₀ := (hS0_mem brRUp band4Zero).mpr (by
    simp [Ch07.groundConfiguration, band4Zero])
  have ha₂' : (brRUp, band4Zero) ∈ S₀.erase (brLDown, band4M1) :=
    Finset.mem_erase.mpr ⟨fun h => brLDown_ne_brRUp.symm (congrArg Prod.fst h), ha₂⟩
  have huniq := twoSiteField_unique_pair_of_distinct 2 S₀ brLDown brRUp brLDown_ne_brRUp
    band4M1 band4Zero
  change inner ℂ (A02.ket singletResidualWitnessConfig)
      (siteField 2 b brRUp 1 (siteField 2 b brLDown 1 (A02.ket S₀))) = _
  rw [twoSiteField_inner_unique 2 b S₀ singletResidualWitnessConfig brLDown brRUp 1
    band4M1 band4Zero ha₁ ha₂' rfl huniq]
  have hp1 : Ch04.precedingCount (brLDown, band4M1) S₀ = 2 := by
    rw [A05.preceding_count_split, band4_prec_m1]
    have hfilt : (Finset.univ.filter (· < brLDown) : Finset SpinBranch) = {brLUp} := by decide
    rw [hfilt, Finset.sum_singleton, hS0_spec brLUp, band4_ground0_card]
  have hp2 : Ch04.precedingCount (brRUp, band4Zero) (S₀.erase (brLDown, band4M1)) = 4 := by
    rw [A05.preceding_count_split]
    have hfilt : (Finset.univ.filter (· < brRUp) : Finset SpinBranch) = {brLUp, brLDown} := by
      decide
    have hm1_mem : band4M1 ∈ Ch07.groundConfiguration 2 0 := by
      simp [Ch07.groundConfiguration, band4M1]
    rw [hfilt, Finset.sum_insert (by decide), Finset.sum_singleton,
      speciesConfiguration_erase_ch21, speciesConfiguration_erase_ch21,
      speciesConfiguration_erase_ch21,
      ite_eq_right brLUp_ne_brLDown, ite_eq_left rfl, ite_eq_right brLDown_ne_brRUp.symm,
      hS0_spec brLUp, hS0_spec brLDown, hS0_spec brRUp,
      Finset.card_erase_of_mem hm1_mem, band4_ground0_card, band4_prec_zero_ground0]
  have htw0 : Ch06Ext.twistedCharacter (2 * 2) (b brRUp) band4Zero 1 = 1 := by
    simp [b, Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, Ch06Ext.periodicTwist,
      A01.integerCharacter, band4Zero]
  have htwm1 : Ch06Ext.twistedCharacter (2 * 2) (b brLDown) band4M1 1 = -Complex.I := by
    simp [b, Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, Ch06Ext.periodicTwist,
      A01.integerCharacter, band4M1, canonicalRoot_four_eq_I]
  unfold Ch04.fermionSign
  rw [hp1, hp2, htw0, htwm1, norm4_sq]
  ring

theorem singlet_pair_residual_ne_zero_h2 :
    Ch14.projectedMap 2 (fun _ => 0) (Ch20.scTarget singletBranchesB (fun _ => 0)) 0 1
      (Ch20.scResidualOp 2 (fun _ => Ch06Ext.periodicTwist (2 * 2)) singletBranchesB 1 (fun _ => 0) 0) ≠ 0 := by
  intro hzero
  have hw := singlet_pair_residual_witness_h2
  rw [hzero, LinearMap.zero_apply, inner_zero_right] at hw
  have hne : -(Complex.I / 4) ≠ 0 := by
    intro h0
    have hI : Complex.I = 0 := by
      have h1 : Complex.I / 4 = 0 := neg_eq_zero.mp h0
      exact (div_eq_zero_iff.mp h1).resolve_right (by norm_num)
    exact Complex.I_ne_zero hI
  exact hne hw.symm

/-! ### 7.3 Pauli-Blocked Inward-Only Umklapp Witness (`ex:ch21-u-inward-only`, `g_U/16` at `h = 2`) -/

/-- Coordinate set of the per-species charge box `ℬ_{K, B}` (`def:ch21-u-charge-box`). -/
def speciesChargeBoxSet (h K : ℕ) (B : SpinBranch → ℕ) : Set (A05.Occupation SpinBranch h) :=
  {S | (∀ ν, |Ch07.relativeCharge h (Ch07.speciesConfiguration h S ν)| ≤ (B ν : ℤ)) ∧
    Ch07.totalExcitation h S ≤ (K : ℤ)}

/-- Per-species charge box `ℬ_{K, B} ⊆ ℋ_L` (`def:ch21-u-charge-box`). -/
noncomputable def speciesChargeBox (h K : ℕ) (B : SpinBranch → ℕ) :
    Submodule ℂ (A05.FockSpace SpinBranch h) :=
  @A03.coordinateSpace (A05.Mode SpinBranch h) _ instDecidableEqProd (speciesChargeBoxSet h K B)

/-- Orthogonal coordinate projector `P_{K, B}` onto `ℬ_{K, B}`. -/
noncomputable def speciesChargeBoxProjection (h K : ℕ) (B : SpinBranch → ℕ) :
    A05.Operators SpinBranch h :=
  @A03.coordinateProjection (A05.Mode SpinBranch h) _ instDecidableEqProd
    (speciesChargeBoxSet h K B)

/-- Charge-box bounds `B = (2, 2, 1, 1)` for `ex:ch21-u-inward-only`. -/
def umklappInwardBoxBounds : SpinBranch → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1

/-- Source charge vector `(2, 2, -1, -1)` for `ex:ch21-u-inward-only`. -/
def umklappInwardSourceCharge : SpinBranch → ℤ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => -1
  | ⟨3, _⟩ => -1

/-- Pauli-blocked source configuration `|S⟩`: full `L↑, L↓` (`{-1,0,1,2}`), `{-1}` on `R↑, R↓`. -/
noncomputable def umklappInwardSourceConfig : A05.Occupation SpinBranch 2 :=
  A05.groundConfiguration 2 umklappInwardSourceCharge

noncomputable def umklappInwardSourceKet : A05.FockSpace SpinBranch 2 :=
  A02.ket umklappInwardSourceConfig

/-- Inward target species configurations: `{0,1,2}` on `L↑, L↓`, `{-1,2}` on `R↑`, `{-1,0}` on `R↓`. -/
noncomputable def umklappInwardTargetSpeciesConfig : SpinBranch → Ch07.Occupation 2
  | ⟨0, _⟩ => (Ch07.groundConfiguration 2 2).erase band4M1
  | ⟨1, _⟩ => (Ch07.groundConfiguration 2 2).erase band4M1
  | ⟨2, _⟩ => insert band4Two (Ch07.groundConfiguration 2 (-1))
  | ⟨3, _⟩ => insert band4Zero (Ch07.groundConfiguration 2 (-1))

noncomputable def umklappInwardTargetConfig : A05.Occupation SpinBranch 2 :=
  A05.jointConfiguration 2 umklappInwardTargetSpeciesConfig

noncomputable def umklappInwardTargetKet : A05.FockSpace SpinBranch 2 :=
  A02.ket umklappInwardTargetConfig

private lemma band4_excitation_le_four (S : Ch07.Occupation 2) :
    Ch07.excitationEnergy 2 S ≤ 4 := by
  have hsea : Ch05.seaEnergy (2 * 2) = -1 := by
    have he : Ch07.relativeEnergy 2 (Ch07.groundConfiguration 2 (-1)) =
        Ch07.groundEnergy (-1) :=
      Ch07.ground_configuration_energy 2 (by decide) (-1) (by unfold Ch07.admissible; omega)
    have her : Ch05.occupationEnergy (2 * 2) (Ch07.groundConfiguration 2 (-1)) = -1 := by
      have hsing : Ch07.groundConfiguration 2 (-1) = {band4M1} := by
        ext k
        simp only [Ch07.groundConfiguration, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, Subtype.ext_iff, band4M1]
        have hk := k.property
        simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hk
        omega
      rw [Ch05.occupationEnergy, hsing, Finset.sum_singleton]
      rfl
    have hg : Ch07.groundEnergy (-1) = 0 := by
      have hd := Ch07.ground_energy_double (-1)
      omega
    unfold Ch07.relativeEnergy at he
    omega
  have hocc : Ch05.occupationEnergy (2 * 2) S ≤ 3 := by
    have hpos : ∀ k ∈ S, k.val ≤ max k.val 0 := fun k _ => le_max_left _ _
    have hle1 : Ch05.occupationEnergy (2 * 2) S ≤ ∑ k ∈ S, max k.val 0 :=
      Finset.sum_le_sum hpos
    have hle2 : ∑ k ∈ S, max k.val 0 ≤ ∑ k : Ch01.Band (2 * 2), max k.val 0 :=
      Finset.sum_le_univ_sum_of_nonneg (fun k => le_max_right _ _)
    have huniv : (Finset.univ : Finset (Ch01.Band (2 * 2))) =
        {band4M1, band4Zero, band4One, band4Two} := by
      ext k
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff,
        Subtype.ext_iff, band4M1, band4Zero, band4One, band4Two]
      have hk := k.property
      simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hk
      omega
    have hsum3 : (∑ k : Ch01.Band (2 * 2), max k.val 0) = 3 := by
      rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
      simp [band4M1, band4Zero, band4One, band4Two]
    omega
  have hge0 : 0 ≤ Ch07.groundEnergy (Ch07.relativeCharge 2 S) := by
    have hd := Ch07.ground_energy_double (Ch07.relativeCharge 2 S)
    have hnn : 0 ≤ Ch07.relativeCharge 2 S * (Ch07.relativeCharge 2 S + 1) := by
      rcases le_or_gt 0 (Ch07.relativeCharge 2 S) with h | h
      · nlinarith
      · have hle : Ch07.relativeCharge 2 S + 1 ≤ 0 := by omega
        nlinarith
    omega
  unfold Ch07.excitationEnergy Ch07.relativeEnergy
  omega

private lemma umklappInwardSourceKet_mem_sector :
    umklappInwardSourceKet ∈ chargeSector 2 umklappInwardSourceCharge := by
  have hadm : A05.admissible 2 umklappInwardSourceCharge := by
    intro ν; fin_cases ν <;> simp [Ch07.admissible, umklappInwardSourceCharge]
  exact jointBudget_le_chargeSector 2 umklappInwardSourceCharge 0
    (A05.ground_mem_budget 2 (by decide) umklappInwardSourceCharge hadm 0)

lemma umklappInwardSourceKet_mem_box :
    umklappInwardSourceKet ∈ speciesChargeBox 2 16 umklappInwardBoxBounds := by
  rw [umklappInwardSourceKet, ← ket_instDecidableEqProd_eq 2 umklappInwardSourceConfig,
    speciesChargeBox, @A03.ket_mem_coordinate_space (A05.Mode SpinBranch 2) _ instDecidableEqProd]
  have hadm : A05.admissible 2 umklappInwardSourceCharge := by
    intro ν; fin_cases ν <;> simp [Ch07.admissible, umklappInwardSourceCharge]
  refine ⟨?_, ?_⟩
  · intro ν
    have hsp : Ch07.speciesConfiguration 2 umklappInwardSourceConfig ν =
        Ch07.groundConfiguration 2 (umklappInwardSourceCharge ν) :=
      A05.species_joint_configuration 2 _ ν
    rw [hsp, Ch07.ground_configuration_charge 2 (by decide) _ (hadm ν)]
    fin_cases ν <;> simp [umklappInwardSourceCharge, umklappInwardBoxBounds]
  · unfold Ch07.totalExcitation
    rw [Fin.sum_univ_four]
    have h0 := band4_excitation_le_four (Ch07.speciesConfiguration 2 umklappInwardSourceConfig 0)
    have h1 := band4_excitation_le_four (Ch07.speciesConfiguration 2 umklappInwardSourceConfig 1)
    have h2 := band4_excitation_le_four (Ch07.speciesConfiguration 2 umklappInwardSourceConfig 2)
    have h3 := band4_excitation_le_four (Ch07.speciesConfiguration 2 umklappInwardSourceConfig 3)
    omega

/-- Pauli blocking: the outward Umklapp word annihilates `|S⟩` at every site and twist. -/
theorem umklappInward_outward_pauli_blocked
    (b : SpinBranch → Ch06Ext.BoundaryTwist (2 * 2)) (x : ℤ) :
    umklappForwardSite 2 b x umklappInwardSourceKet = 0 := by
  have hmem := umklappForwardSite_maps_sector 2 b x umklappInwardSourceCharge
    umklappInwardSourceKet umklappInwardSourceKet_mem_sector
  have hempty : {S : A05.Occupation SpinBranch 2 |
      ∀ ν, Ch07.relativeCharge 2 (Ch07.speciesConfiguration 2 S ν) =
        umklappForwardTarget umklappInwardSourceCharge ν} = ∅ := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hS
    have h0 := hS brLUp
    have hval : umklappForwardTarget umklappInwardSourceCharge brLUp = 3 := by decide
    rw [hval] at h0
    have hadm := Ch07.charge_admissible 2 (Ch07.speciesConfiguration 2 S brLUp)
    unfold Ch07.admissible at hadm
    omega
  rw [chargeSector, hempty,
    @A03.coordinate_space_empty (A05.Mode SpinBranch 2) _ instDecidableEqProd] at hmem
  simpa using hmem

/-- Exact inward-only Umklapp matrix element `⟨T', H_U(g_U) S⟩ = g_U / 16` (`ex:ch21-u-inward-only`). -/
theorem umklappInward_coeff_h2 (gU : ℝ) :
    inner ℂ umklappInwardTargetKet (periodicUmklappOp 2 gU umklappInwardSourceKet) =
      (gU : ℂ) / 16 := by
  let _ : NeZero (2 * 2) := ⟨by decide⟩
  let b : SpinBranch → Ch06Ext.BoundaryTwist (2 * 2) := fun _ => Ch06Ext.periodicTwist (2 * 2)
  let S := umklappInwardSourceConfig
  let T' := umklappInwardTargetConfig
  have hS_mem (ν : SpinBranch) (k : Ch01.Band (2 * 2)) :
      (ν, k) ∈ S ↔ k ∈ Ch07.groundConfiguration 2 (umklappInwardSourceCharge ν) := by
    simp [S, umklappInwardSourceConfig, A05.groundConfiguration, A05.jointConfiguration]
  have hT_mem (ν : SpinBranch) (k : Ch01.Band (2 * 2)) :
      (ν, k) ∈ T' ↔ k ∈ umklappInwardTargetSpeciesConfig ν := by
    simp [T', umklappInwardTargetConfig, A05.jointConfiguration]
  have hS_spec (ν : SpinBranch) :
      Ch07.speciesConfiguration 2 S ν = Ch07.groundConfiguration 2 (umklappInwardSourceCharge ν) :=
    A05.species_joint_configuration 2 _ ν
  have hT_spec (ν : SpinBranch) :
      Ch07.speciesConfiguration 2 T' ν = umklappInwardTargetSpeciesConfig ν :=
    A05.species_joint_configuration 2 umklappInwardTargetSpeciesConfig ν
  have hcard2 : (Ch07.groundConfiguration 2 2).card = 4 := by
    have hz := Ch07.ground_configuration_card 2 (by decide) 2 (by unfold Ch07.admissible; omega)
    omega
  have hm1_in2 : band4M1 ∈ Ch07.groundConfiguration 2 2 := by
    simp [Ch07.groundConfiguration, band4M1]
  have h2_notin : band4Two ∉ Ch07.groundConfiguration 2 (-1) := by
    simp [Ch07.groundConfiguration, band4Two]
  have h0_notin : band4Zero ∉ Ch07.groundConfiguration 2 (-1) := by
    simp [Ch07.groundConfiguration, band4Zero]
  have hcard_er : ((Ch07.groundConfiguration 2 2).erase band4M1).card = 3 := by
    rw [Finset.card_erase_of_mem hm1_in2, hcard2]
  have hprec_two :
      Ch04.precedingCount band4Two (insert band4Two (Ch07.groundConfiguration 2 (-1))) = 1 := by
    have hfilt : (insert band4Two (Ch07.groundConfiguration 2 (-1))).filter (· < band4Two) =
        Ch07.groundConfiguration 2 (-1) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_insert, Ch07.groundConfiguration, Finset.mem_univ,
        true_and]
      change ((l = band4Two ∨ l.val ≤ -1) ∧ l.val < (2 : ℤ)) ↔ l.val ≤ -1
      constructor
      · rintro ⟨h1 | h1, hlt⟩
        · subst h1; simp [band4Two] at hlt
        · exact h1
      · intro h1; exact ⟨Or.inr h1, by omega⟩
    unfold Ch04.precedingCount
    rw [hfilt]
    exact band4_groundM1_card
  have hprec_zero :
      Ch04.precedingCount band4Zero (insert band4Zero (Ch07.groundConfiguration 2 (-1))) = 1 := by
    have hfilt : (insert band4Zero (Ch07.groundConfiguration 2 (-1))).filter (· < band4Zero) =
        Ch07.groundConfiguration 2 (-1) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_insert, Ch07.groundConfiguration, Finset.mem_univ,
        true_and]
      change ((l = band4Zero ∨ l.val ≤ -1) ∧ l.val < (0 : ℤ)) ↔ l.val ≤ -1
      constructor
      · rintro ⟨h1 | h1, hlt⟩
        · subst h1; simp [band4Zero] at hlt
        · exact h1
      · intro h1; exact ⟨Or.inr h1, by omega⟩
    unfold Ch04.precedingCount
    rw [hfilt]
    exact band4_groundM1_card
  let g (k₀ k₁ k₂ k₃ : Ch01.Band (2 * 2)) : Prop :=
    ((brRUp, k₀) ∈ T' ∧ (brRDown, k₁) ∈ T'.erase (brRUp, k₀)) ∧
      ((brLUp, k₂) ∈ S ∧ (brLDown, k₃) ∈ S.erase (brLUp, k₂)) ∧
      ((T'.erase (brRUp, k₀)).erase (brRDown, k₁) =
        (S.erase (brLUp, k₂)).erase (brLDown, k₃))
  have hsupp : g band4Two band4Zero band4M1 band4M1 := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [hT_mem]; simp [umklappInwardTargetSpeciesConfig, brRUp]
    · rw [Finset.mem_erase, hT_mem]
      exact ⟨fun h => brRUp_ne_brRDown (congrArg Prod.fst h).symm,
        by simp [umklappInwardTargetSpeciesConfig, brRDown]⟩
    · rw [hS_mem]; simpa [umklappInwardSourceCharge, brLUp] using hm1_in2
    · rw [Finset.mem_erase, hS_mem]
      exact ⟨fun h => brLUp_ne_brLDown (congrArg Prod.fst h).symm,
        by simpa [umklappInwardSourceCharge, brLDown] using hm1_in2⟩
    · ext ⟨ν, k⟩
      simp only [Finset.mem_erase, ne_eq, Prod.mk.injEq, hT_mem, hS_mem]
      fin_cases ν
      · simp [umklappInwardTargetSpeciesConfig, umklappInwardSourceCharge,
          brLUp, brLDown, brRUp, brRDown]
      · simp [umklappInwardTargetSpeciesConfig, umklappInwardSourceCharge,
          brLUp, brLDown, brRUp, brRDown]
      · simp [umklappInwardTargetSpeciesConfig, umklappInwardSourceCharge,
          brLUp, brLDown, brRUp, brRDown]
        constructor
        · rintro ⟨hk2, rfl | hk⟩
          · exact absurd rfl hk2
          · exact hk
        · intro hk
          exact ⟨fun h => h2_notin (h ▸ hk), Or.inr hk⟩
      · simp [umklappInwardTargetSpeciesConfig, umklappInwardSourceCharge,
          brLUp, brLDown, brRUp, brRDown]
        constructor
        · rintro ⟨hk0, rfl | hk⟩
          · exact absurd rfl hk0
          · exact hk
        · intro hk
          exact ⟨fun h => h0_notin (h ▸ hk), Or.inr hk⟩
  have huniq : ∀ k₀ k₁ k₂ k₃, g k₀ k₁ k₂ k₃ →
      k₀ = band4Two ∧ k₁ = band4Zero ∧ k₂ = band4M1 ∧ k₃ = band4M1 := by
    intro k₀ k₁ k₂ k₃ ⟨⟨hk₀, hk₁⟩, ⟨hk₂, hk₃⟩, heq⟩
    have h0 : k₀ = band4Two := by
      have hsp := congrArg (fun U => Ch07.speciesConfiguration 2 U brRUp) heq
      simp only [speciesConfiguration_erase_ch21, ite_eq_right brRUp_ne_brRDown,
        ite_eq_right brLUp_ne_brRUp.symm, ite_eq_right brLDown_ne_brRUp.symm,
        hT_spec, hS_spec] at hsp
      have hk₀' : k₀ ∈ umklappInwardTargetSpeciesConfig brRUp := (hT_mem brRUp k₀).mp hk₀
      have hsp2 : (umklappInwardTargetSpeciesConfig brRUp).erase band4Two =
          Ch07.groundConfiguration 2 (umklappInwardSourceCharge brRUp) := by
        simp [umklappInwardTargetSpeciesConfig, umklappInwardSourceCharge, brRUp,
          Finset.erase_insert h2_notin]
      exact erase_eq_erase_imp_eq hk₀' (hsp.trans hsp2.symm)
    have h1 : k₁ = band4Zero := by
      have hsp := congrArg (fun U => Ch07.speciesConfiguration 2 U brRDown) heq
      simp only [speciesConfiguration_erase_ch21, ite_eq_right brRUp_ne_brRDown.symm,
        ite_eq_right brLUp_ne_brRDown.symm, ite_eq_right brLDown_ne_brRDown.symm,
        hT_spec, hS_spec] at hsp
      have hk₁' : k₁ ∈ umklappInwardTargetSpeciesConfig brRDown :=
        (hT_mem brRDown k₁).mp (Finset.mem_of_mem_erase hk₁)
      have hsp2 : (umklappInwardTargetSpeciesConfig brRDown).erase band4Zero =
          Ch07.groundConfiguration 2 (umklappInwardSourceCharge brRDown) := by
        simp [umklappInwardTargetSpeciesConfig, umklappInwardSourceCharge, brRDown,
          Finset.erase_insert h0_notin]
      exact erase_eq_erase_imp_eq hk₁' (hsp.trans hsp2.symm)
    have h2 : k₂ = band4M1 := by
      have hsp := congrArg (fun U => Ch07.speciesConfiguration 2 U brLUp) heq
      simp only [speciesConfiguration_erase_ch21, ite_eq_right brLUp_ne_brRDown,
        ite_eq_right brLUp_ne_brRUp, ite_eq_right brLUp_ne_brLDown,
        hT_spec, hS_spec] at hsp
      have hk₂' : k₂ ∈ Ch07.groundConfiguration 2 2 := by
        simpa [umklappInwardSourceCharge, brLUp] using (hS_mem brLUp k₂).mp hk₂
      exact erase_eq_erase_imp_eq hk₂' (by
        simpa [umklappInwardTargetSpeciesConfig, umklappInwardSourceCharge, brLUp] using hsp.symm)
    have h3 : k₃ = band4M1 := by
      have hsp := congrArg (fun U => Ch07.speciesConfiguration 2 U brLDown) heq
      simp only [speciesConfiguration_erase_ch21, ite_eq_right brLDown_ne_brRDown,
        ite_eq_right brLDown_ne_brRUp, ite_eq_right brLUp_ne_brLDown.symm,
        hT_spec, hS_spec] at hsp
      have hk₃' : k₃ ∈ Ch07.groundConfiguration 2 2 := by
        simpa [umklappInwardSourceCharge, brLDown] using
          (hS_mem brLDown k₃).mp (Finset.mem_of_mem_erase hk₃)
      exact erase_eq_erase_imp_eq hk₃' (by
        simpa [umklappInwardTargetSpeciesConfig, umklappInwardSourceCharge, brLDown] using hsp.symm)
    exact ⟨h0, h1, h2, h3⟩
  have hsign_prod :
      star (Ch04.fermionSign (brRDown, band4Zero) (T'.erase (brRUp, band4Two)) *
          Ch04.fermionSign (brRUp, band4Two) T') *
        (Ch04.fermionSign (brLDown, band4M1) (S.erase (brLUp, band4M1)) *
          Ch04.fermionSign (brLUp, band4M1) S) = (1 : ℂ) := by
    have hp1 : Ch04.precedingCount (brLUp, band4M1) S = 0 := by
      rw [A05.preceding_count_split, band4_prec_m1]
      have hfilt : (Finset.univ.filter (· < brLUp) : Finset SpinBranch) = ∅ := by decide
      rw [hfilt, Finset.sum_empty, zero_add]
    have hp2 : Ch04.precedingCount (brLDown, band4M1) (S.erase (brLUp, band4M1)) = 3 := by
      rw [A05.preceding_count_split, band4_prec_m1]
      have hfilt : (Finset.univ.filter (· < brLDown) : Finset SpinBranch) = {brLUp} := by decide
      rw [hfilt, Finset.sum_singleton, speciesConfiguration_erase_ch21, ite_eq_left rfl,
        hS_spec brLUp]
      simpa [umklappInwardSourceCharge, brLUp] using hcard_er
    have hp3 : Ch04.precedingCount (brRUp, band4Two) T' = 7 := by
      rw [A05.preceding_count_split]
      have hfilt : (Finset.univ.filter (· < brRUp) : Finset SpinBranch) = {brLUp, brLDown} := by
        decide
      rw [hfilt, Finset.sum_insert (by decide), Finset.sum_singleton,
        hT_spec brLUp, hT_spec brLDown, hT_spec brRUp]
      simp only [umklappInwardTargetSpeciesConfig, brLUp, brLDown, brRUp, hcard_er, hprec_two]
    have hp4 : Ch04.precedingCount (brRDown, band4Zero) (T'.erase (brRUp, band4Two)) = 8 := by
      rw [A05.preceding_count_split]
      have hfilt : (Finset.univ.filter (· < brRDown) : Finset SpinBranch) =
          {brLUp, brLDown, brRUp} := by decide
      rw [hfilt, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
        speciesConfiguration_erase_ch21, speciesConfiguration_erase_ch21,
        speciesConfiguration_erase_ch21, speciesConfiguration_erase_ch21,
        ite_eq_right brLUp_ne_brRUp, ite_eq_right brLDown_ne_brRUp, ite_eq_left rfl,
        ite_eq_right brRUp_ne_brRDown.symm,
        hT_spec brLUp, hT_spec brLDown, hT_spec brRUp, hT_spec brRDown]
      simp only [umklappInwardTargetSpeciesConfig, brLUp, brLDown, brRUp, brRDown,
        Finset.erase_insert h2_notin, hcard_er, band4_groundM1_card, hprec_zero]
      norm_num
    unfold Ch04.fermionSign
    rw [hp1, hp2, hp3, hp4]
    norm_num
  have hback : ∀ x : ℤ,
      inner ℂ umklappInwardTargetKet (umklappBackwardSite 2 b x umklappInwardSourceKet) =
        (16 : ℂ)⁻¹ := by
    intro x
    change inner ℂ (A02.ket T') (umklappBackwardSite 2 b x (A02.ket S)) = _
    have hadj : inner ℂ (A02.ket T') (umklappBackwardSite 2 b x (A02.ket S)) =
        inner ℂ (siteField 2 b brRDown x (siteField 2 b brRUp x (A02.ket T')))
          (siteField 2 b brLDown x (siteField 2 b brLUp x (A02.ket S))) := by
      simp only [umklappBackwardSite, Module.End.mul_apply, siteAdjoint, siteField,
        LinearMap.adjoint_inner_right]
    rw [hadj, twoSiteField_ket, twoSiteField_ket, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_pow, A01.normalization_conj (2 * 2), ← mul_assoc, norm4_sq]
    have h16 : (4 : ℂ)⁻¹ * (4 : ℂ)⁻¹ = (16 : ℂ)⁻¹ := by norm_num
    rw [h16]
    simp_rw [sum_inner, inner_sum, inner_ite_zero, inner_smul_left, inner_smul_right,
      A02.ket_inner]
    have hre : (∑ k₀ : Ch01.Band (2 * 2), ∑ k₁ : Ch01.Band (2 * 2),
          ∑ k₂ : Ch01.Band (2 * 2), ∑ k₃ : Ch01.Band (2 * 2),
          if ((brRUp, k₀) ∈ T' ∧ (brRDown, k₁) ∈ T'.erase (brRUp, k₀)) ∧
              ((brLUp, k₂) ∈ S ∧ (brLDown, k₃) ∈ S.erase (brLUp, k₂)) then
            starRingEnd ℂ
              (Ch06Ext.twistedCharacter (2 * 2) (b brRDown) k₁ x *
                Ch04.fermionSign (brRDown, k₁) (T'.erase (brRUp, k₀)) *
                (Ch06Ext.twistedCharacter (2 * 2) (b brRUp) k₀ x *
                  Ch04.fermionSign (brRUp, k₀) T')) *
              ((Ch06Ext.twistedCharacter (2 * 2) (b brLDown) k₃ x *
                  Ch04.fermionSign (brLDown, k₃) (S.erase (brLUp, k₂)) *
                  (Ch06Ext.twistedCharacter (2 * 2) (b brLUp) k₂ x *
                    Ch04.fermionSign (brLUp, k₂) S)) *
                if (T'.erase (brRUp, k₀)).erase (brRDown, k₁) =
                    (S.erase (brLUp, k₂)).erase (brLDown, k₃) then 1 else 0)
          else 0) =
        ∑ k₀ : Ch01.Band (2 * 2), ∑ k₁ : Ch01.Band (2 * 2),
          ∑ k₂ : Ch01.Band (2 * 2), ∑ k₃ : Ch01.Band (2 * 2),
          if g k₀ k₁ k₂ k₃ then
            starRingEnd ℂ
              (Ch06Ext.twistedCharacter (2 * 2) (b brRDown) k₁ x *
                Ch04.fermionSign (brRDown, k₁) (T'.erase (brRUp, k₀)) *
                (Ch06Ext.twistedCharacter (2 * 2) (b brRUp) k₀ x *
                  Ch04.fermionSign (brRUp, k₀) T')) *
              (Ch06Ext.twistedCharacter (2 * 2) (b brLDown) k₃ x *
                Ch04.fermionSign (brLDown, k₃) (S.erase (brLUp, k₂)) *
                (Ch06Ext.twistedCharacter (2 * 2) (b brLUp) k₂ x *
                  Ch04.fermionSign (brLUp, k₂) S))
          else 0 := by
      refine Finset.sum_congr rfl (fun k₀ _ => Finset.sum_congr rfl (fun k₁ _ =>
        Finset.sum_congr rfl (fun k₂ _ => Finset.sum_congr rfl (fun k₃ _ => ?_))))
      dsimp only [g]
      by_cases ha : (brRUp, k₀) ∈ T' ∧ (brRDown, k₁) ∈ T'.erase (brRUp, k₀)
      · by_cases hb : (brLUp, k₂) ∈ S ∧ (brLDown, k₃) ∈ S.erase (brLUp, k₂)
        · by_cases hc : (T'.erase (brRUp, k₀)).erase (brRDown, k₁) =
              (S.erase (brLUp, k₂)).erase (brLDown, k₃)
          · rw [ite_eq_left ⟨ha, hb⟩, ite_eq_left hc, mul_one, ite_eq_left ⟨ha, hb, hc⟩]
          · rw [ite_eq_left ⟨ha, hb⟩, ite_eq_right hc, mul_zero, mul_zero,
              ite_eq_right (fun h => hc h.2.2)]
        · rw [ite_eq_right (fun h => hb h.2), ite_eq_right (fun h => hb h.2.1)]
      · rw [ite_eq_right (fun h => ha h.1), ite_eq_right (fun h => ha h.1)]
    rw [hre, sum_single_quad band4Two band4Zero band4M1 band4M1 _ g huniq hsupp]
    have hchar_prod :
        starRingEnd ℂ (Ch06Ext.twistedCharacter (2 * 2) (b brRDown) band4Zero x) *
          starRingEnd ℂ (Ch06Ext.twistedCharacter (2 * 2) (b brRUp) band4Two x) *
          (Ch06Ext.twistedCharacter (2 * 2) (b brLDown) band4M1 x *
            Ch06Ext.twistedCharacter (2 * 2) (b brLUp) band4M1 x) = 1 := by
      have htw (ν : SpinBranch) (k : Ch01.Band (2 * 2)) :
          Ch06Ext.twistedCharacter (2 * 2) (b ν) k x =
            A01.integerCharacter (A01.canonicalRoot (2 * 2)) k.val x := by
        simp [b, Ch06Ext.twistedCharacter, Ch06Ext.liftPhase, Ch06Ext.periodicTwist]
      simp_rw [htw, starRingEnd_apply,
        A01.complex_character_conj (2 * 2) _ (A01.canonical_root_primitive (2 * 2))]
      have hroot := A01.canonical_root_primitive (2 * 2)
      have hnz : A01.canonicalRoot (2 * 2) ≠ 0 := A01.root_ne_zero (2 * 2) _ hroot
      have hpow1 : A01.canonicalRoot (2 * 2) ^ ((2 * 2 : ℕ) : ℤ) = 1 := by
        rw [zpow_natCast]
        exact hroot.pow_eq_one
      simp only [A01.integerCharacter, band4Two, band4Zero, band4M1]
      rw [← zpow_add₀ hnz, ← zpow_add₀ hnz, ← zpow_add₀ hnz]
      have hexp : (-0) * x + (-2) * x + ((-1) * x + (-1) * x) = ((2 * 2 : ℕ) : ℤ) * (-x) := by
        push_cast; ring
      rw [hexp, zpow_mul, hpow1, one_zpow]
    have hsplit :
        starRingEnd ℂ
            (Ch06Ext.twistedCharacter (2 * 2) (b brRDown) band4Zero x *
              Ch04.fermionSign (brRDown, band4Zero) (T'.erase (brRUp, band4Two)) *
              (Ch06Ext.twistedCharacter (2 * 2) (b brRUp) band4Two x *
                Ch04.fermionSign (brRUp, band4Two) T')) *
            (Ch06Ext.twistedCharacter (2 * 2) (b brLDown) band4M1 x *
              Ch04.fermionSign (brLDown, band4M1) (S.erase (brLUp, band4M1)) *
              (Ch06Ext.twistedCharacter (2 * 2) (b brLUp) band4M1 x *
                Ch04.fermionSign (brLUp, band4M1) S)) =
          (starRingEnd ℂ (Ch06Ext.twistedCharacter (2 * 2) (b brRDown) band4Zero x) *
            starRingEnd ℂ (Ch06Ext.twistedCharacter (2 * 2) (b brRUp) band4Two x) *
            (Ch06Ext.twistedCharacter (2 * 2) (b brLDown) band4M1 x *
              Ch06Ext.twistedCharacter (2 * 2) (b brLUp) band4M1 x)) *
          (star (Ch04.fermionSign (brRDown, band4Zero) (T'.erase (brRUp, band4Two)) *
              Ch04.fermionSign (brRUp, band4Two) T') *
            (Ch04.fermionSign (brLDown, band4M1) (S.erase (brLUp, band4M1)) *
              Ch04.fermionSign (brLUp, band4M1) S)) := by
      simp only [map_mul, starRingEnd_apply, star_mul]
      ring
    rw [hsplit, hchar_prod, one_mul, hsign_prod, mul_one]
  unfold periodicUmklappOp umklappOp
  rw [LinearMap.smul_apply, LinearMap.sum_apply, inner_smul_right, inner_sum]
  simp only [LinearMap.add_apply, inner_add_right]
  simp_rw [show (fun _ : SpinBranch => Ch06Ext.periodicTwist (2 * 2)) = b from rfl,
    umklappInward_outward_pauli_blocked, inner_zero_right, zero_add, hback]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- Non-leakage of `|S⟩`: `H_U(g_U) |S⟩` stays inside `ℬ_{16, (2,2,1,1)}`. -/
lemma umklappInward_mem_box_h2 (gU : ℝ) :
    periodicUmklappOp 2 gU umklappInwardSourceKet ∈
      speciesChargeBox 2 16 umklappInwardBoxBounds := by
  have hsec : periodicUmklappOp 2 gU umklappInwardSourceKet ∈
      chargeSector 2 (umklappBackwardTarget umklappInwardSourceCharge) := by
    unfold periodicUmklappOp umklappOp
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro x _
    rw [umklappInward_outward_pauli_blocked, zero_add]
    exact umklappBackwardSite_maps_sector 2 _ _ umklappInwardSourceCharge
      umklappInwardSourceKet umklappInwardSourceKet_mem_sector
  have hle : chargeSector 2 (umklappBackwardTarget umklappInwardSourceCharge) ≤
      speciesChargeBox 2 16 umklappInwardBoxBounds := by
    unfold chargeSector speciesChargeBox
    apply @A03.coordinate_space_mono (A05.Mode SpinBranch 2) _ instDecidableEqProd
    intro U hU
    refine ⟨?_, ?_⟩
    · intro ν
      rw [hU ν]
      fin_cases ν <;>
        simp [umklappBackwardTarget, umklappInwardSourceCharge, umklappDelta,
          umklappInwardBoxBounds, brLUp, brLDown]
    · unfold Ch07.totalExcitation
      rw [Fin.sum_univ_four]
      have h0 := band4_excitation_le_four (Ch07.speciesConfiguration 2 U 0)
      have h1 := band4_excitation_le_four (Ch07.speciesConfiguration 2 U 1)
      have h2 := band4_excitation_le_four (Ch07.speciesConfiguration 2 U 2)
      have h3 := band4_excitation_le_four (Ch07.speciesConfiguration 2 U 3)
      omega
  exact hle hsec

/-- Complete `ex:ch21-u-inward-only` statement: for `g_U ≠ 0`, `H_U |S⟩ ≠ 0` yet
`(I - P_{16, B}) H_U |S⟩ = 0`. -/
theorem umklappInward_no_leakage_h2 (gU : ℝ) (hg : gU ≠ 0) :
    periodicUmklappOp 2 gU umklappInwardSourceKet ≠ 0 ∧
    (1 - speciesChargeBoxProjection 2 16 umklappInwardBoxBounds)
      (periodicUmklappOp 2 gU umklappInwardSourceKet) = 0 := by
  constructor
  · intro h0
    have hc := umklappInward_coeff_h2 gU
    rw [h0, inner_zero_right] at hc
    have hne : (gU : ℂ) / 16 ≠ 0 :=
      div_ne_zero (Complex.ofReal_ne_zero.mpr hg) (by norm_num)
    exact hne hc.symm
  · have hfix : speciesChargeBoxProjection 2 16 umklappInwardBoxBounds
        (periodicUmklappOp 2 gU umklappInwardSourceKet) =
        periodicUmklappOp 2 gU umklappInwardSourceKet :=
      (@A03.projection_fixed_iff (A05.Mode SpinBranch 2) _ instDecidableEqProd
        (speciesChargeBoxSet 2 16 umklappInwardBoxBounds) _).mpr
        (umklappInward_mem_box_h2 gU)
    simp only [LinearMap.sub_apply, Module.End.one_apply, hfix, sub_self]

end Bosonize.Ch21
