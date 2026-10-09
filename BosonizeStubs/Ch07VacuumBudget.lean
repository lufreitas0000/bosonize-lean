module

public import BosonizeStubs.A03EnergyBudgets
public import Bosonize.Core.Ch05Fermions

/-!
# CH07: integer sectors, ground configurations and coordinate energy budgets
Phase A: complete data and one-sorry review contracts.
The physical model has L = 2*h with h > 0, including the empty/full sectors.
-/

@[expose] public section

namespace Bosonize.Ch07

open scoped BigOperators

abbrev Occupation (h : ℕ) := A02.Occupation (Ch01.Band (2*h))
abbrev FockSpace (h : ℕ) := Ch05.FockSpace (2*h)
abbrev Operators (h : ℕ) := Module.End ℂ (FockSpace h)

def admissible (h : ℕ) (N : ℤ) : Prop := -(h : ℤ) ≤ N ∧ N ≤ (h : ℤ)

def relativeCharge (h : ℕ) (S : Occupation h) : ℤ := (S.card : ℤ)-(h : ℤ)

/-- The energy is vacuum-subtracted, not the bare sum of occupied momenta. -/
def relativeEnergy (h : ℕ) (S : Occupation h) : ℤ :=
  Ch05.occupationEnergy (2*h) S - Ch05.seaEnergy (2*h)

def groundEnergy (N : ℤ) : ℤ := N*(N+1)/2

def excitationEnergy (h : ℕ) (S : Occupation h) : ℤ :=
  relativeEnergy h S - groundEnergy (relativeCharge h S)

/-- Natural extraction is useful only after excitation_nonneg is proved. -/
def excitationNat (h : ℕ) (S : Occupation h) : ℕ := (excitationEnergy h S).toNat

/-- Outside admissible sectors this is only a clipped threshold configuration. -/
def groundConfiguration (h : ℕ) (N : ℤ) : Occupation h :=
  Finset.univ.filter (fun k => k.val ≤ N)

/-- A physical sector ground ket is named only with an admissibility certificate. -/
noncomputable def groundKet (h : ℕ) (N : ℤ) (_hN : admissible h N) : FockSpace h :=
  A02.ket (groundConfiguration h N)

noncomputable def vacuumKet (h : ℕ) : FockSpace h := Ch05.seaKet (2*h)

/-- Index by the actual natural cardinality; the empty configuration needs no special index. -/
noncomputable def sortedMode (h : ℕ) (S : Occupation h) : Fin S.card → Ch01.Band (2*h) :=
  S.orderEmbOfFin rfl

def referenceMode (h : ℕ) (S : Occupation h) (i : Fin S.card) : ℤ :=
  -(h : ℤ)+1+(i.val : ℤ)

noncomputable def displacement (h : ℕ) (S : Occupation h) (i : Fin S.card) : ℤ :=
  (sortedMode h S i).val - referenceMode h S i

noncomputable def chargeObservable (h : ℕ) : Operators h :=
  A03.diagonal (fun S => (relativeCharge h S : ℂ))

noncomputable def excitationObservable (h : ℕ) : Operators h :=
  A03.diagonal (fun S => (excitationEnergy h S : ℂ))

noncomputable def energySpace (h : ℕ) (N E : ℤ) : Submodule ℂ (FockSpace h) :=
  A03.fixedEnergy (relativeCharge h) (excitationEnergy h) N E

/-- Signed cutoffs give the zero space when K < 0, after nonnegativity is established. -/
noncomputable def fixedBudget (h : ℕ) (N K : ℤ) : Submodule ℂ (FockSpace h) :=
  A03.budget (relativeCharge h) (excitationEnergy h) N K

noncomputable def boxBudget (h : ℕ) (K : ℤ) (Nmax : ℕ) : Submodule ℂ (FockSpace h) :=
  A03.chargeBox (relativeCharge h) (excitationEnergy h) K Nmax

noncomputable def fixedProjection (h : ℕ) (N K : ℤ) : Operators h :=
  A03.budgetProjection (relativeCharge h) (excitationEnergy h) N K

noncomputable def boxProjection (h : ℕ) (K : ℤ) (Nmax : ℕ) : Operators h :=
  A03.boxProjection (relativeCharge h) (excitationEnergy h) K Nmax

noncomputable def compressed (h : ℕ) (N K : ℤ) (A : Operators h) : Operators h :=
  fixedProjection h N K * A * fixedProjection h N K

lemma ground_energy_even (N : ℤ) : Even (N*(N+1)) := by sorry

lemma ground_energy_double (N : ℤ) : 2*groundEnergy N = N*(N+1) := by sorry

lemma ground_energy_unique (N t : ℤ) (ht : 2*t = N*(N+1)) : t = groundEnergy N := by sorry

lemma charge_admissible (h : ℕ) (S : Occupation h) : admissible h (relativeCharge h S) := by sorry

lemma ground_configuration_card (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    ((groundConfiguration h N).card : ℤ) = (h : ℤ)+N := by sorry

lemma ground_configuration_charge (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    relativeCharge h (groundConfiguration h N) = N := by sorry

lemma ground_configuration_energy (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    relativeEnergy h (groundConfiguration h N) = groundEnergy N := by sorry

lemma ground_configuration_excitation (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    excitationEnergy h (groundConfiguration h N) = 0 := by sorry

lemma ground_configuration_zero (h : ℕ) : groundConfiguration h 0 = Ch05.seaConfiguration (2*h) := by sorry

lemma ground_configuration_empty (h : ℕ) : groundConfiguration h (-(h : ℤ)) = ∅ := by sorry

lemma ground_configuration_full (h : ℕ) : groundConfiguration h (h : ℤ) = Finset.univ := by sorry

lemma vacuum_charge (h : ℕ) (hh : 0 < h) : relativeCharge h (Ch05.seaConfiguration (2*h)) = 0 := by sorry

lemma vacuum_relative_energy (h : ℕ) : relativeEnergy h (Ch05.seaConfiguration (2*h)) = 0 := by sorry

lemma vacuum_excitation (h : ℕ) (hh : 0 < h) : excitationEnergy h (Ch05.seaConfiguration (2*h)) = 0 := by sorry

lemma ground_ket_ne_zero (h : ℕ) (N : ℤ) (hN : admissible h N) : groundKet h N hN ≠ 0 := by sorry

lemma vacuum_ket_ne_zero (h : ℕ) : vacuumKet h ≠ 0 := by sorry

lemma sorted_mode_mem (h : ℕ) (S : Occupation h) (i : Fin S.card) : sortedMode h S i ∈ S := by sorry

lemma sorted_mode_strict_mono (h : ℕ) (S : Occupation h) :
    StrictMono (fun i => (sortedMode h S i).val) := by sorry

lemma energy_sorted_sum (h : ℕ) (S : Occupation h) :
    Ch05.occupationEnergy (2*h) S = ∑ i : Fin S.card, (sortedMode h S i).val := by sorry

lemma sorted_mode_lower_bound (h : ℕ) (S : Occupation h) (i : Fin S.card) :
    referenceMode h S i ≤ (sortedMode h S i).val := by sorry

lemma displacement_nonneg (h : ℕ) (S : Occupation h) (i : Fin S.card) :
    0 ≤ displacement h S i := by sorry

lemma displacement_mono (h : ℕ) (S : Occupation h) : Monotone (displacement h S) := by sorry

lemma excitation_displacement_sum (h : ℕ) (hh : 0 < h) (S : Occupation h) :
    excitationEnergy h S = ∑ i : Fin S.card, displacement h S i := by sorry

lemma excitation_nonneg (h : ℕ) (hh : 0 < h) (S : Occupation h) : 0 ≤ excitationEnergy h S := by sorry

lemma excitation_nat_cast (h : ℕ) (hh : 0 < h) (S : Occupation h) :
    (excitationNat h S : ℤ) = excitationEnergy h S := by sorry

lemma excitation_zero_iff_ground (h : ℕ) (hh : 0 < h) (S : Occupation h) :
    excitationEnergy h S = 0 ↔ S = groundConfiguration h (relativeCharge h S) := by sorry

lemma charge_observable_ket (h : ℕ) (S : Occupation h) :
    chargeObservable h (A02.ket S) = (relativeCharge h S : ℂ) • A02.ket S := by sorry

lemma excitation_observable_ket (h : ℕ) (S : Occupation h) :
    excitationObservable h (A02.ket S) = (excitationEnergy h S : ℂ) • A02.ket S := by sorry

lemma charge_observable_adjoint (h : ℕ) : LinearMap.adjoint (chargeObservable h) = chargeObservable h := by sorry

lemma excitation_observable_adjoint (h : ℕ) :
    LinearMap.adjoint (excitationObservable h) = excitationObservable h := by sorry

lemma charge_observable_total_number (h : ℕ) :
    chargeObservable h = Ch05.totalNumber (2*h) - (h : ℂ) • (1 : Operators h) := by sorry

lemma relative_hamiltonian_diagonal (h : ℕ) :
    Ch05.shiftedHamiltonian (2*h) = A03.diagonal (fun S => (relativeEnergy h S : ℂ)) := by sorry

lemma ket_mem_fixed_budget (h : ℕ) (S : Occupation h) (N K : ℤ) :
    A02.ket S ∈ fixedBudget h N K ↔ relativeCharge h S = N ∧ excitationEnergy h S ≤ K := by sorry

lemma ground_ket_mem_budget (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) (K : ℕ) :
    groundKet h N hN ∈ fixedBudget h N K := by sorry

lemma vacuum_ket_mem_box (h : ℕ) (hh : 0 < h) (K Nmax : ℕ) :
    vacuumKet h ∈ boxBudget h K Nmax := by sorry

lemma zero_energy_ground_span (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    energySpace h N 0 = Submodule.span ℂ {groundKet h N hN} := by sorry

lemma zero_energy_dimension_one (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    Module.finrank ℂ (energySpace h N 0) = 1 := by sorry

lemma zero_budget_ground_span (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    fixedBudget h N 0 = Submodule.span ℂ {groundKet h N hN} := by sorry

lemma inadmissible_budget (h : ℕ) (N K : ℤ) (hN : ¬ admissible h N) :
    fixedBudget h N K = ⊥ := by sorry

lemma negative_budget (h : ℕ) (hh : 0 < h) (N K : ℤ) (hK : K < 0) : fixedBudget h N K = ⊥ := by sorry

/-- Extremal empty/full sectors cannot supply a one-step excited configuration. -/
lemma excited_configuration_exists (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : -(h : ℤ) < N ∧ N < (h : ℤ)) :
    ∃ S : Occupation h, relativeCharge h S = N ∧ excitationEnergy h S = 1 := by sorry

lemma budget_dimension_ge_two (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : -(h : ℤ) < N ∧ N < (h : ℤ)) (K : ℕ) (hK : 1 ≤ K) :
    2 ≤ Module.finrank ℂ (fixedBudget h N K) := by sorry

lemma displacement_le_budget (h : ℕ) (hh : 0 < h) (S : Occupation h) (K : ℕ)
    (he : excitationEnergy h S ≤ (K : ℤ)) (i : Fin S.card) : displacement h S i ≤ (K : ℤ) := by sorry

lemma frozen_full (h : ℕ) (hh : 0 < h) (S : Occupation h) (N : ℤ) (K : ℕ)
    (hN : relativeCharge h S = N) (he : excitationEnergy h S ≤ (K : ℤ))
    (k : Ch01.Band (2*h)) (hk : k.val ≤ N-(K : ℤ)) : k ∈ S := by sorry

lemma frozen_empty (h : ℕ) (hh : 0 < h) (S : Occupation h) (N : ℤ) (K : ℕ)
    (hN : relativeCharge h S = N) (he : excitationEnergy h S ≤ (K : ℤ))
    (k : Ch01.Band (2*h)) (hk : N+(K : ℤ) < k.val) : k ∉ S := by sorry

lemma missing_deep_energy (h : ℕ) (hh : 0 < h) (S : Occupation h) (K : ℕ)
    (k : Ch01.Band (2*h)) (hk : k.val ≤ relativeCharge h S-(K : ℤ)) (hmiss : k ∉ S) :
    (K : ℤ) < excitationEnergy h S := by sorry

lemma occupied_high_energy (h : ℕ) (hh : 0 < h) (S : Occupation h) (K : ℕ)
    (k : Ch01.Band (2*h)) (hk : relativeCharge h S+(K : ℤ) < k.val) (hocc : k ∈ S) :
    (K : ℤ) < excitationEnergy h S := by sorry

lemma fixed_projection_idempotent (h : ℕ) (N K : ℤ) :
    fixedProjection h N K * fixedProjection h N K = fixedProjection h N K := by sorry

lemma fixed_projection_adjoint (h : ℕ) (N K : ℤ) :
    LinearMap.adjoint (fixedProjection h N K) = fixedProjection h N K := by sorry

lemma fixed_projection_range (h : ℕ) (N K : ℤ) :
    LinearMap.range (fixedProjection h N K) = fixedBudget h N K := by sorry

lemma box_projection_idempotent (h : ℕ) (K : ℤ) (Nmax : ℕ) :
    boxProjection h K Nmax * boxProjection h K Nmax = boxProjection h K Nmax := by sorry

lemma box_projection_adjoint (h : ℕ) (K : ℤ) (Nmax : ℕ) :
    LinearMap.adjoint (boxProjection h K Nmax) = boxProjection h K Nmax := by sorry

lemma box_projection_range (h : ℕ) (K : ℤ) (Nmax : ℕ) :
    LinearMap.range (boxProjection h K Nmax) = boxBudget h K Nmax := by sorry

lemma filtered_budget_map (h : ℕ) (A : Operators h) (q d N K : ℤ)
    (hA : A03.Filtered (relativeCharge h) (excitationEnergy h) A q d) :
    ∀ v ∈ fixedBudget h N K, A v ∈ fixedBudget h (N+q) (K+d) := by sorry

lemma charge_preserving_budget_map (h : ℕ) (A : Operators h) (d N K : ℤ)
    (hA : A03.Filtered (relativeCharge h) (excitationEnergy h) A 0 d) :
    ∀ v ∈ fixedBudget h N K, A v ∈ fixedBudget h N (K+d) := by sorry

lemma negative_shift_annihilates (h : ℕ) (hh : 0 < h) (A : Operators h) (q d N K : ℤ)
    (hA : A03.Filtered (relativeCharge h) (excitationEnergy h) A q d) (hKd : K+d < 0) :
    ∀ v ∈ fixedBudget h N K, A v = 0 := by sorry

lemma charge_insert (h : ℕ) (S : Occupation h) (k : Ch01.Band (2*h)) (hk : k ∉ S) :
    relativeCharge h (insert k S) = relativeCharge h S+1 := by sorry

lemma charge_erase (h : ℕ) (S : Occupation h) (k : Ch01.Band (2*h)) (hk : k ∈ S) :
    relativeCharge h (S.erase k) = relativeCharge h S-1 := by sorry

lemma excitation_insert (h : ℕ) (S : Occupation h) (k : Ch01.Band (2*h)) (hk : k ∉ S) :
    excitationEnergy h (insert k S) = excitationEnergy h S+k.val-(relativeCharge h S+1) := by sorry

lemma excitation_erase (h : ℕ) (S : Occupation h) (k : Ch01.Band (2*h)) (hk : k ∈ S) :
    excitationEnergy h (S.erase k) = excitationEnergy h S-k.val+relativeCharge h S := by sorry

lemma creation_budget_map (h : ℕ) (k : Ch01.Band (2*h)) (N K : ℤ) :
    ∀ v ∈ fixedBudget h N K,
      Ch05.momentumCreation (2*h) k v ∈ fixedBudget h (N+1) (K+k.val-(N+1)) := by sorry

lemma annihilation_budget_map (h : ℕ) (k : Ch01.Band (2*h)) (N K : ℤ) :
    ∀ v ∈ fixedBudget h N K,
      Ch05.momentumAnnihilation (2*h) k v ∈ fixedBudget h (N-1) (K-k.val+N) := by sorry

/-- A numerical window claim, not a density commutator or an implicit operator-word proof. -/
lemma active_window_in_band (h M K Nmax : ℕ) (N j : ℤ)
    (hN : |N| ≤ (Nmax : ℤ)) (hmargin : A03.uniformCutoff h M K Nmax)
    (hj : N-(K : ℤ)-(M : ℤ)+1 ≤ j ∧ j ≤ N+(K : ℤ)+(M : ℤ)) :
    Ch01.inBandPredicate (2*h) j := by sorry

lemma word_window_in_band (h M K Nmax : ℕ) (N j : ℤ) (ds : List ℤ)
    (hN : |N| ≤ (Nmax : ℤ)) (hmargin : A03.wordCutoff h M K Nmax ds)
    (hj : N-(K : ℤ)-A03.upwardExcursion ds-(M : ℤ)+1 ≤ j ∧
      j ≤ N+(K : ℤ)+A03.upwardExcursion ds+(M : ℤ)) :
    Ch01.inBandPredicate (2*h) j := by sorry

section Species
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Recover each species occupation from the actual combined fermionic configuration. -/
def speciesConfiguration (h : ℕ) (S : A02.Occupation (σ × Ch01.Band (2*h))) (ν : σ) : Occupation h :=
  (S.filter (fun p => p.1 = ν)).image Prod.snd

def totalExcitation (h : ℕ) (S : A02.Occupation (σ × Ch01.Band (2*h))) : ℤ :=
  ∑ ν : σ, excitationEnergy h (speciesConfiguration h S ν)

noncomputable def speciesBudget (h : ℕ) (Ns : σ → ℤ) (K : ℤ) :
    Submodule ℂ (A02.FockSpace (σ × Ch01.Band (2*h))) :=
  A03.coordinateSpace {S | (∀ ν, relativeCharge h (speciesConfiguration h S ν) = Ns ν) ∧
    totalExcitation h S ≤ K}

lemma total_excitation_nonneg (h : ℕ) (hh : 0 < h) (S : A02.Occupation (σ × Ch01.Band (2*h))) :
    0 ≤ totalExcitation h S := by sorry

lemma species_budget_ket (h : ℕ) (S : A02.Occupation (σ × Ch01.Band (2*h))) (Ns : σ → ℤ) (K : ℤ) :
    A02.ket S ∈ speciesBudget h Ns K ↔
      (∀ ν, relativeCharge h (speciesConfiguration h S ν) = Ns ν) ∧ totalExcitation h S ≤ K := by sorry

lemma species_budget_negative (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (K : ℤ) (hK : K < 0) :
    speciesBudget h Ns K = ⊥ := by sorry

end Species

end Bosonize.Ch07
