module

public import Bosonize.Core.A03EnergyBudgets
public import Bosonize.Core.Ch05Fermions

/-!
# CH07: integer sectors, ground configurations and coordinate energy budgets
Phase B: complete data and proofs of the approved sector/budget contracts.
The physical model has L = 2*h with h > 0, including the empty/full sectors.
These integer energies use the CH05 reference sea. For arbitrary real offset β,
Ch06Ext.physical_relative_shift and excitation_twist_cancel give the same-sea
physical energy and excitation bridge. The physical charge-energy polynomial is
N*(N+1)/2 + β*N; at centered APBC β = -1/2 it becomes N²/2.
Fields and transport must retain the matching angleTwist choice in downstream
models. This integer excitation coordinate does not choose a boundary condition.
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

lemma ground_energy_even (N : ℤ) : Even (N*(N+1)) := by
  exact Int.even_mul_succ_self N

lemma ground_energy_double (N : ℤ) : 2*groundEnergy N = N*(N+1) := by
  have hd : 2 ∣ N*(N+1) := even_iff_two_dvd.mp (ground_energy_even N)
  unfold groundEnergy
  omega

lemma ground_energy_unique (N t : ℤ) (ht : 2*t = N*(N+1)) : t = groundEnergy N := by
  have hd := ground_energy_double N; omega

lemma charge_admissible (h : ℕ) (S : Occupation h) : admissible h (relativeCharge h S) := by
  have hc := Finset.card_le_card (Finset.subset_univ S)
  have hb : Fintype.card (Ch01.Band (2*h)) = 2*h := by
    by_cases hh : h = 0
    · subst h
      have hz : IsEmpty (Ch01.Band 0) := ⟨by intro k; have hk := k.property; simp [Ch01.inBandPredicate] at hk; omega⟩
      simp
    · exact Ch01.card_band _ (by omega)
  rw [Finset.card_univ, hb] at hc
  unfold admissible relativeCharge
  omega

lemma ground_configuration_card (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    ((groundConfiguration h N).card : ℤ) = (h : ℤ)+N := by
  have _positiveLength := hh
  have hmem (k : Ch01.Band (2*h)) : k ∈ groundConfiguration h N ↔ k.val ≤ N := by simp [groundConfiguration]
  have hin (k : Ch01.Band (2*h)) (hk : k ∈ groundConfiguration h N) :
      (k.val+(h : ℤ)-1).toNat ∈ Finset.range ((h : ℤ)+N).toNat := by
    have hkN := (hmem k).mp hk
    have hb := k.property
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hb
    simp only [Finset.mem_range]
    rcases hN with ⟨hlo, hhi⟩
    omega
  have hinj (k l : Ch01.Band (2*h)) (hk : k ∈ groundConfiguration h N)
      (hl : l ∈ groundConfiguration h N)
      (he : (k.val+(h : ℤ)-1).toNat = (l.val+(h : ℤ)-1).toNat) : k = l := by
    have hb := k.property
    have hc := l.property
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hb hc
    apply Subtype.ext
    omega
  have hsurj (n : ℕ) (hn : n ∈ Finset.range ((h : ℤ)+N).toNat) :
      ∃ k, ∃ hk : k ∈ groundConfiguration h N, (k.val+(h : ℤ)-1).toNat = n := by
    simp only [Finset.mem_range] at hn
    have hb : Ch01.inBandPredicate (2*h) (-(h : ℤ)+1+(n : ℤ)) := by
      simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]
      rcases hN with ⟨hlo, hhi⟩
      omega
    refine ⟨⟨-(h : ℤ)+1+(n : ℤ), hb⟩, ?_, ?_⟩
    · apply (hmem _).mpr
      rcases hN with ⟨hlo, hhi⟩
      dsimp
      omega
    · dsimp
      omega
  have hc := Finset.card_bij (fun (k : Ch01.Band (2*h)) _ => (k.val+(h : ℤ)-1).toNat)
    hin (fun k hk l hl => hinj k l hk hl) hsurj
  rw [Finset.card_range] at hc
  rw [hc]
  exact Int.toNat_of_nonneg (by have := hN.1; omega)

lemma ground_configuration_charge (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    relativeCharge h (groundConfiguration h N) = N := by
  unfold relativeCharge; rw [ground_configuration_card h hh N hN]; omega

lemma ground_configuration_energy (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    relativeEnergy h (groundConfiguration h N) = groundEnergy N := by
  have hmem (k : Ch01.Band (2*h)) : k ∈ groundConfiguration h N ↔ k.val ≤ N := by simp [groundConfiguration]
  have hin (k : Ch01.Band (2*h)) (hk : k ∈ groundConfiguration h N) :
      (k.val+(h : ℤ)-1).toNat ∈ Finset.range ((h : ℤ)+N).toNat := by
    have hkN := (hmem k).mp hk
    have hb := k.property
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hb
    simp only [Finset.mem_range]
    rcases hN with ⟨hlo, hhi⟩
    omega
  have hinj (k l : Ch01.Band (2*h)) (hk : k ∈ groundConfiguration h N)
      (hl : l ∈ groundConfiguration h N)
      (he : (k.val+(h : ℤ)-1).toNat = (l.val+(h : ℤ)-1).toNat) : k = l := by
    have hb := k.property
    have hc := l.property
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hb hc
    apply Subtype.ext
    omega
  have hsurj (n : ℕ) (hn : n ∈ Finset.range ((h : ℤ)+N).toNat) :
      ∃ k, ∃ hk : k ∈ groundConfiguration h N, (k.val+(h : ℤ)-1).toNat = n := by
    simp only [Finset.mem_range] at hn
    have hb : Ch01.inBandPredicate (2*h) (-(h : ℤ)+1+(n : ℤ)) := by
      simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]
      rcases hN with ⟨hlo, hhi⟩
      omega
    refine ⟨⟨-(h : ℤ)+1+(n : ℤ), hb⟩, ?_, ?_⟩
    · apply (hmem _).mpr
      rcases hN with ⟨hlo, hhi⟩
      dsimp
      omega
    · dsimp
      omega
  have hsum : Ch05.occupationEnergy (2*h) (groundConfiguration h N) =
      ∑ n ∈ Finset.range ((h : ℤ)+N).toNat, (-(h : ℤ)+1+(n : ℤ)) := by
    unfold Ch05.occupationEnergy
    apply Finset.sum_bij (fun (k : Ch01.Band (2*h)) _ => (k.val+(h : ℤ)-1).toNat)
      hin (fun k hk l hl => hinj k l hk hl) hsurj
    intro k hk
    have hb := k.property
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hb
    omega
  have sumDouble (p : ℕ) : 2*(∑ n ∈ Finset.range p, (-(h : ℤ)+1+(n : ℤ))) =
      (p : ℤ)*((p : ℤ)-2*(h : ℤ)+1) := by
    induction p with
    | zero => simp
    | succ p ih => rw [Finset.sum_range_succ]; push_cast; nlinarith
  have hp : (((h : ℤ)+N).toNat : ℤ) = (h : ℤ)+N := Int.toNat_of_nonneg (by have := hN.1; omega)
  have hs := sumDouble ((h : ℤ)+N).toNat
  rw [hp, ← hsum] at hs
  have hg := ground_energy_double ((h : ℤ)-1)
  unfold groundEnergy at hg
  have prodEq : ((h : ℤ)-1)*((h : ℤ)-1+1) = (h : ℤ)*((h : ℤ)-1) := by ring
  rw [prodEq] at hg
  have hsea := Ch05.sea_energy_even h hh
  have ht := ground_energy_double N
  unfold relativeEnergy
  rw [hsea]
  nlinarith

lemma ground_configuration_excitation (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    excitationEnergy h (groundConfiguration h N) = 0 := by
  unfold excitationEnergy; rw [ground_configuration_charge h hh N hN, ground_configuration_energy h hh N hN]; omega

lemma ground_configuration_zero (h : ℕ) : groundConfiguration h 0 = Ch05.seaConfiguration (2*h) := by
  rfl

lemma ground_configuration_empty (h : ℕ) : groundConfiguration h (-(h : ℤ)) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  have hb := k.property
  simp only [groundConfiguration, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hb
  omega

lemma ground_configuration_full (h : ℕ) : groundConfiguration h (h : ℤ) = Finset.univ := by
  apply Finset.filter_eq_self.mpr
  intro k _
  have hb := k.property
  simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hb
  omega

lemma vacuum_charge (h : ℕ) (hh : 0 < h) : relativeCharge h (Ch05.seaConfiguration (2*h)) = 0 := by
  unfold relativeCharge; rw [Ch05.sea_card_even h hh]; omega

lemma vacuum_relative_energy (h : ℕ) : relativeEnergy h (Ch05.seaConfiguration (2*h)) = 0 := by
  simp [relativeEnergy, Ch05.seaEnergy]

lemma vacuum_excitation (h : ℕ) (hh : 0 < h) : excitationEnergy h (Ch05.seaConfiguration (2*h)) = 0 := by
  simp [excitationEnergy, vacuum_charge h hh, vacuum_relative_energy, groundEnergy]

lemma ground_ket_ne_zero (h : ℕ) (N : ℤ) (hN : admissible h N) : groundKet h N hN ≠ 0 := by
  exact A02.ket_ne_zero _

lemma vacuum_ket_ne_zero (h : ℕ) : vacuumKet h ≠ 0 := by
  exact Ch05.sea_ket_ne_zero _

lemma sorted_mode_mem (h : ℕ) (S : Occupation h) (i : Fin S.card) : sortedMode h S i ∈ S := by
  exact S.orderEmbOfFin_mem rfl i

lemma sorted_mode_strict_mono (h : ℕ) (S : Occupation h) :
    StrictMono (fun i => (sortedMode h S i).val) := by
  intro i j hij
  exact (S.orderEmbOfFin rfl).strictMono hij

lemma energy_sorted_sum (h : ℕ) (S : Occupation h) :
    Ch05.occupationEnergy (2*h) S = ∑ i : Fin S.card, (sortedMode h S i).val := by
  unfold Ch05.occupationEnergy sortedMode
  conv_lhs => rw [← S.map_orderEmbOfFin_univ rfl]
  rw [Finset.sum_map]
  rfl

lemma sorted_mode_lower_bound (h : ℕ) (S : Occupation h) (i : Fin S.card) :
    referenceMode h S i ≤ (sortedMode h S i).val := by
  have lower (n : ℕ) (hn : n < S.card) : -(h : ℤ)+1+(n : ℤ) ≤ (sortedMode h S ⟨n, hn⟩).val := by
    induction n with
    | zero =>
      have hb := (sortedMode h S ⟨0, hn⟩).property
      simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hb
      omega
    | succ n ih =>
      have hn' : n < S.card := by omega
      have hb := ih hn'
      have hm := sorted_mode_strict_mono h S (show (⟨n, hn'⟩ : Fin S.card) < ⟨n+1, hn⟩ by exact Nat.lt_succ_self n)
      push_cast at *
      omega
  exact lower i.val i.isLt

lemma displacement_nonneg (h : ℕ) (S : Occupation h) (i : Fin S.card) :
    0 ≤ displacement h S i := by
  unfold displacement; have := sorted_mode_lower_bound h S i; omega

lemma displacement_mono (h : ℕ) (S : Occupation h) : Monotone (displacement h S) := by
  intro i j hij
  have grow (a b : ℕ) (ha : a < S.card) (hb : b < S.card) (hab : a ≤ b) :
      (sortedMode h S ⟨a, ha⟩).val+(b-a : ℕ) ≤ (sortedMode h S ⟨b, hb⟩).val := by
    induction b with
    | zero =>
      have he : a = 0 := by omega
      subst a
      simp
    | succ b ih =>
      by_cases he : a = b+1
      · subst a; simp
      · have hb' : b < S.card := by omega
        have hh := ih hb' (by omega)
        have hm := sorted_mode_strict_mono h S (show (⟨b, hb'⟩ : Fin S.card) < ⟨b+1, hb⟩ by exact Nat.lt_succ_self b)
        change (sortedMode h S ⟨b, hb'⟩).val < (sortedMode h S ⟨b+1, hb⟩).val at hm
        have hn : (b+1-a : ℕ) = (b-a)+1 := by omega
        rw [hn, Nat.cast_add, Nat.cast_one]
        omega
  have hg := grow i.val j.val i.isLt j.isLt hij
  change (sortedMode h S i).val + (j.val-i.val : ℕ) ≤ (sortedMode h S j).val at hg
  unfold displacement referenceMode
  rw [Nat.cast_sub hij] at hg
  omega

lemma excitation_displacement_sum (h : ℕ) (hh : 0 < h) (S : Occupation h) :
    excitationEnergy h S = ∑ i : Fin S.card, displacement h S i := by
  have sumDouble (p : ℕ) : 2*(∑ n ∈ Finset.range p, (-(h : ℤ)+1+(n : ℤ))) =
      (p : ℤ)*((p : ℤ)-2*(h : ℤ)+1) := by
    induction p with
    | zero => simp
    | succ p ih => rw [Finset.sum_range_succ]; push_cast; nlinarith
  have href : (∑ i : Fin S.card, referenceMode h S i) =
      ∑ n ∈ Finset.range S.card, (-(h : ℤ)+1+(n : ℤ)) := by
    exact Fin.sum_univ_eq_sum_range (fun n => (-(h : ℤ)+1+(n : ℤ))) S.card
  have hs := sumDouble S.card
  rw [← href] at hs
  have hg := ground_energy_double (relativeCharge h S)
  have hsea := Ch05.sea_energy_even h hh
  have hhg := ground_energy_double ((h : ℤ)-1)
  unfold groundEnergy at hhg
  have prodEq : ((h : ℤ)-1)*((h : ℤ)-1+1) = (h : ℤ)*((h : ℤ)-1) := by ring
  rw [prodEq] at hhg
  unfold displacement
  rw [Finset.sum_sub_distrib, ← energy_sorted_sum]
  unfold excitationEnergy relativeEnergy relativeCharge at *
  rw [hsea]
  nlinarith

lemma excitation_nonneg (h : ℕ) (hh : 0 < h) (S : Occupation h) : 0 ≤ excitationEnergy h S := by
  rw [excitation_displacement_sum h hh S]; exact Finset.sum_nonneg (by intro i _; exact displacement_nonneg h S i)

lemma excitation_nat_cast (h : ℕ) (hh : 0 < h) (S : Occupation h) :
    (excitationNat h S : ℤ) = excitationEnergy h S := by
  exact Int.toNat_of_nonneg (excitation_nonneg h hh S)

lemma excitation_zero_iff_ground (h : ℕ) (hh : 0 < h) (S : Occupation h) :
    excitationEnergy h S = 0 ↔ S = groundConfiguration h (relativeCharge h S) := by
  constructor
  · intro he
    have hz (i : Fin S.card) : displacement h S i = 0 := by
      have hb := Finset.single_le_sum (fun j _ => displacement_nonneg h S j) (Finset.mem_univ i)
      rw [← excitation_displacement_sum h hh S, he] at hb
      have hn := displacement_nonneg h S i
      omega
    have hsub : S ⊆ groundConfiguration h (relativeCharge h S) := by
      intro k hk
      have hr := S.range_orderEmbOfFin rfl
      have hm : k ∈ Set.range (S.orderEmbOfFin rfl) := by rw [hr]; exact hk
      obtain ⟨i, hi⟩ := hm
      have hd := hz i
      unfold displacement referenceMode sortedMode at hd
      rw [hi] at hd
      simp only [groundConfiguration, Finset.mem_filter, Finset.mem_univ, true_and]
      unfold relativeCharge
      have := i.isLt
      omega
    apply Finset.eq_of_subset_of_card_le hsub
    have hc := ground_configuration_card h hh (relativeCharge h S) (charge_admissible h S)
    change ((groundConfiguration h (relativeCharge h S)).card : ℤ) = (h : ℤ)+((S.card : ℤ)-(h : ℤ)) at hc
    omega
  · intro he
    rw [he]
    exact ground_configuration_excitation h hh _ (charge_admissible h S)

lemma charge_observable_ket (h : ℕ) (S : Occupation h) :
    chargeObservable h (A02.ket S) = (relativeCharge h S : ℂ) • A02.ket S := by
  exact A03.diagonal_ket _ S

lemma excitation_observable_ket (h : ℕ) (S : Occupation h) :
    excitationObservable h (A02.ket S) = (excitationEnergy h S : ℂ) • A02.ket S := by
  exact A03.diagonal_ket _ S

lemma charge_observable_adjoint (h : ℕ) : LinearMap.adjoint (chargeObservable h) = chargeObservable h := by
  unfold chargeObservable
  rw [A03.diagonal_adjoint]
  congr 1
  funext S
  simp

lemma excitation_observable_adjoint (h : ℕ) :
    LinearMap.adjoint (excitationObservable h) = excitationObservable h := by
  unfold excitationObservable
  rw [A03.diagonal_adjoint]
  congr 1
  funext S
  simp

lemma charge_observable_total_number (h : ℕ) :
    chargeObservable h = Ch05.totalNumber (2*h) - (h : ℂ) • (1 : Operators h) := by
  apply A02.end_ext_basis
  intro S
  rw [charge_observable_ket]
  simp [Ch05.total_number_ket, relativeCharge, sub_smul]

lemma relative_hamiltonian_diagonal (h : ℕ) :
    Ch05.shiftedHamiltonian (2*h) = A03.diagonal (fun S => (relativeEnergy h S : ℂ)) := by
  apply A02.end_ext_basis
  intro S
  rw [Ch05.shifted_hamiltonian_ket, A03.diagonal_ket]
  rfl

lemma ket_mem_fixed_budget (h : ℕ) (S : Occupation h) (N K : ℤ) :
    A02.ket S ∈ fixedBudget h N K ↔ relativeCharge h S = N ∧ excitationEnergy h S ≤ K := by
  exact A03.ket_mem_coordinate_space _ S

lemma ground_ket_mem_budget (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) (K : ℕ) :
    groundKet h N hN ∈ fixedBudget h N K := by
  apply (ket_mem_fixed_budget h _ N K).mpr
  exact ⟨ground_configuration_charge h hh N hN, by rw [ground_configuration_excitation h hh N hN]; omega⟩

lemma vacuum_ket_mem_box (h : ℕ) (hh : 0 < h) (K Nmax : ℕ) :
    vacuumKet h ∈ boxBudget h K Nmax := by
  apply (A03.ket_mem_coordinate_space _ _).mpr
  exact ⟨by rw [vacuum_excitation h hh]; omega, by rw [vacuum_charge h hh]; simp⟩

lemma zero_energy_ground_span (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    energySpace h N 0 = Submodule.span ℂ {groundKet h N hN} := by
  have hs : {S | relativeCharge h S = N ∧ excitationEnergy h S = 0} = {groundConfiguration h N} := by
    ext S
    constructor
    · intro hS
      have hg := (excitation_zero_iff_ground h hh S).mp hS.2
      rw [hS.1] at hg
      exact hg
    · intro hS
      change S = groundConfiguration h N at hS
      subst S
      exact ⟨ground_configuration_charge h hh N hN, ground_configuration_excitation h hh N hN⟩
  unfold energySpace A03.fixedEnergy A03.coordinateSpace groundKet
  rw [hs, Set.image_singleton]

lemma zero_energy_dimension_one (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    Module.finrank ℂ (energySpace h N 0) = 1 := by
  rw [zero_energy_ground_span h hh N hN]
  exact finrank_span_singleton (ground_ket_ne_zero h N hN)

lemma zero_budget_ground_span (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : admissible h N) :
    fixedBudget h N 0 = Submodule.span ℂ {groundKet h N hN} := by
  have heq : {S | relativeCharge h S = N ∧ excitationEnergy h S ≤ 0} =
      {S | relativeCharge h S = N ∧ excitationEnergy h S = 0} := by
    ext S
    have hn := excitation_nonneg h hh S
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro hS <;> exact ⟨hS.1, by omega⟩
  unfold fixedBudget A03.budget
  rw [heq]
  exact zero_energy_ground_span h hh N hN

lemma inadmissible_budget (h : ℕ) (N K : ℤ) (hN : ¬ admissible h N) :
    fixedBudget h N K = ⊥ := by
  have hs : {S | relativeCharge h S = N ∧ excitationEnergy h S ≤ K} = ∅ := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hS
    exact hN (hS.1 ▸ charge_admissible h S)
  change A03.coordinateSpace _ = _
  rw [hs, A03.coordinate_space_empty]

lemma negative_budget (h : ℕ) (hh : 0 < h) (N K : ℤ) (hK : K < 0) : fixedBudget h N K = ⊥ := by
  exact A03.negative_budget _ _ (excitation_nonneg h hh) N K hK

/-- Extremal empty/full sectors cannot supply a one-step excited configuration. -/
lemma excited_configuration_exists (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : -(h : ℤ) < N ∧ N < (h : ℤ)) :
    ∃ S : Occupation h, relativeCharge h S = N ∧ excitationEnergy h S = 1 := by
  have hNa : admissible h N := ⟨by omega, by omega⟩
  have hb0 : Ch01.inBandPredicate (2*h) N := by
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]
    omega
  have hb1 : Ch01.inBandPredicate (2*h) (N+1) := by
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]
    omega
  let k : Ch01.Band (2*h) := ⟨N, hb0⟩
  let l : Ch01.Band (2*h) := ⟨N+1, hb1⟩
  let G := groundConfiguration h N
  have hk : k ∈ G := by simp [G, k, groundConfiguration]
  have hl : l ∉ G := by simp [G, l, groundConfiguration]
  have hle : l ∉ G.erase k := fun he => hl (Finset.mem_of_mem_erase he)
  have hpos := Finset.card_pos.mpr ⟨k, hk⟩
  have hc : relativeCharge h (insert l (G.erase k)) = N := by
    unfold relativeCharge
    rw [Finset.card_insert_of_notMem hle, Finset.card_erase_of_mem hk]
    have hg := ground_configuration_card h hh N hNa
    change ((G.card : ℤ)) = (h : ℤ)+N at hg
    omega
  have hp : Ch05.occupationEnergy (2*h) (insert l (G.erase k)) = Ch05.occupationEnergy (2*h) G+1 := by
    unfold Ch05.occupationEnergy
    rw [Finset.sum_insert hle]
    have he := Finset.add_sum_erase G (fun k : Ch01.Band (2*h) => k.val) hk
    dsimp [k, l] at *
    omega
  refine ⟨insert l (G.erase k), hc, ?_⟩
  unfold excitationEnergy relativeEnergy
  rw [hc, hp]
  have hg := ground_configuration_energy h hh N hNa
  change Ch05.occupationEnergy (2*h) G-Ch05.seaEnergy (2*h) = groundEnergy N at hg
  omega

lemma budget_dimension_ge_two (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : -(h : ℤ) < N ∧ N < (h : ℤ)) (K : ℕ) (hK : 1 ≤ K) :
    2 ≤ Module.finrank ℂ (fixedBudget h N K) := by
  obtain ⟨S, hc, he⟩ := excited_configuration_exists h hh N hN
  have hNa : admissible h N := ⟨by omega, by omega⟩
  have hG := ground_ket_mem_budget h hh N hNa K
  have hS : A02.ket S ∈ fixedBudget h N K := (ket_mem_fixed_budget h S N K).mpr ⟨hc, by omega⟩
  have hne : groundConfiguration h N ≠ S := by
    intro hEq
    have hz := ground_configuration_excitation h hh N hNa
    rw [hEq, he] at hz
    omega
  let f : Fin 2 → Occupation h := fun i => if i = 0 then groundConfiguration h N else S
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  let v : Fin 2 → fixedBudget h N K := fun i => if i = 0 then ⟨groundKet h N hNa, hG⟩ else ⟨A02.ket S, hS⟩
  have hi : LinearIndependent ℂ (fun i => A02.ket (f i)) :=
    (A02.occupationBasis (Ch01.Band (2*h))).linearIndependent.comp f hf
  have hv : LinearIndependent ℂ v := by
    apply LinearIndependent.of_comp (fixedBudget h N K).subtype
    simpa only [Function.comp_def, v, f, groundKet, apply_ite, Submodule.subtype_apply] using hi
  simpa using hv.fintype_card_le_finrank

lemma displacement_le_budget (h : ℕ) (hh : 0 < h) (S : Occupation h) (K : ℕ)
    (he : excitationEnergy h S ≤ (K : ℤ)) (i : Fin S.card) : displacement h S i ≤ (K : ℤ) := by
  have hi := Finset.single_le_sum (fun i _ => displacement_nonneg h S i) (Finset.mem_univ i)
  rw [← excitation_displacement_sum h hh S] at hi
  exact hi.trans he

lemma frozen_full (h : ℕ) (hh : 0 < h) (S : Occupation h) (N : ℤ) (K : ℕ)
    (hN : relativeCharge h S = N) (he : excitationEnergy h S ≤ (K : ℤ))
    (k : Ch01.Band (2*h)) (hk : k.val ≤ N-(K : ℤ)) : k ∈ S := by
  by_contra hmiss
  have hc : relativeCharge h (insert k S) = N+1 := by
    unfold relativeCharge at *
    rw [Finset.card_insert_of_notMem hmiss, Nat.cast_add, Nat.cast_one]
    omega
  have hp : Ch05.occupationEnergy (2*h) (insert k S) = k.val+Ch05.occupationEnergy (2*h) S := by
    unfold Ch05.occupationEnergy
    exact Finset.sum_insert hmiss
  have hn := excitation_nonneg h hh (insert k S)
  have g1 := ground_energy_double N
  have g2 := ground_energy_double (N+1)
  unfold excitationEnergy relativeEnergy at hn he
  rw [hc, hp] at hn
  rw [hN] at he
  nlinarith

lemma frozen_empty (h : ℕ) (hh : 0 < h) (S : Occupation h) (N : ℤ) (K : ℕ)
    (hN : relativeCharge h S = N) (he : excitationEnergy h S ≤ (K : ℤ))
    (k : Ch01.Band (2*h)) (hk : N+(K : ℤ) < k.val) : k ∉ S := by
  intro hocc
  have hpos := Finset.card_pos.mpr ⟨k, hocc⟩
  have hc : relativeCharge h (S.erase k) = N-1 := by
    unfold relativeCharge at *
    rw [Finset.card_erase_of_mem hocc, Nat.cast_sub hpos, Nat.cast_one]
    omega
  have hp : Ch05.occupationEnergy (2*h) (S.erase k) = Ch05.occupationEnergy (2*h) S-k.val := by
    unfold Ch05.occupationEnergy
    have he := Finset.add_sum_erase S (fun k : Ch01.Band (2*h) => k.val) hocc
    omega
  have hn := excitation_nonneg h hh (S.erase k)
  have g1 := ground_energy_double N
  have g2 := ground_energy_double (N-1)
  unfold excitationEnergy relativeEnergy at hn he
  rw [hc, hp] at hn
  rw [hN] at he
  nlinarith

lemma missing_deep_energy (h : ℕ) (hh : 0 < h) (S : Occupation h) (K : ℕ)
    (k : Ch01.Band (2*h)) (hk : k.val ≤ relativeCharge h S-(K : ℤ)) (hmiss : k ∉ S) :
    (K : ℤ) < excitationEnergy h S := by
  by_contra hn
  have he : excitationEnergy h S ≤ (K : ℤ) := by omega
  exact hmiss (frozen_full h hh S (relativeCharge h S) K rfl he k hk)

lemma occupied_high_energy (h : ℕ) (hh : 0 < h) (S : Occupation h) (K : ℕ)
    (k : Ch01.Band (2*h)) (hk : relativeCharge h S+(K : ℤ) < k.val) (hocc : k ∈ S) :
    (K : ℤ) < excitationEnergy h S := by
  by_contra hn
  have he : excitationEnergy h S ≤ (K : ℤ) := by omega
  exact frozen_empty h hh S (relativeCharge h S) K rfl he k hk hocc

lemma fixed_projection_idempotent (h : ℕ) (N K : ℤ) :
    fixedProjection h N K * fixedProjection h N K = fixedProjection h N K := by
  exact A03.projection_idempotent _

lemma fixed_projection_adjoint (h : ℕ) (N K : ℤ) :
    LinearMap.adjoint (fixedProjection h N K) = fixedProjection h N K := by
  exact A03.projection_adjoint _

lemma fixed_projection_range (h : ℕ) (N K : ℤ) :
    LinearMap.range (fixedProjection h N K) = fixedBudget h N K := by
  exact A03.projection_range _

lemma box_projection_idempotent (h : ℕ) (K : ℤ) (Nmax : ℕ) :
    boxProjection h K Nmax * boxProjection h K Nmax = boxProjection h K Nmax := by
  exact A03.projection_idempotent _

lemma box_projection_adjoint (h : ℕ) (K : ℤ) (Nmax : ℕ) :
    LinearMap.adjoint (boxProjection h K Nmax) = boxProjection h K Nmax := by
  exact A03.projection_adjoint _

lemma box_projection_range (h : ℕ) (K : ℤ) (Nmax : ℕ) :
    LinearMap.range (boxProjection h K Nmax) = boxBudget h K Nmax := by
  exact A03.projection_range _

lemma filtered_budget_map (h : ℕ) (A : Operators h) (q d N K : ℤ)
    (hA : A03.Filtered (relativeCharge h) (excitationEnergy h) A q d) :
    ∀ v ∈ fixedBudget h N K, A v ∈ fixedBudget h (N+q) (K+d) := by
  exact A03.filtered_budget_map _ _ A q d N K hA

lemma charge_preserving_budget_map (h : ℕ) (A : Operators h) (d N K : ℤ)
    (hA : A03.Filtered (relativeCharge h) (excitationEnergy h) A 0 d) :
    ∀ v ∈ fixedBudget h N K, A v ∈ fixedBudget h N (K+d) := by
  simpa using filtered_budget_map h A 0 d N K hA

lemma negative_shift_annihilates (h : ℕ) (hh : 0 < h) (A : Operators h) (q d N K : ℤ)
    (hA : A03.Filtered (relativeCharge h) (excitationEnergy h) A q d) (hKd : K+d < 0) :
    ∀ v ∈ fixedBudget h N K, A v = 0 := by
  exact A03.filtered_lowering_zero _ _ (excitation_nonneg h hh) A q d N K hA hKd

lemma charge_insert (h : ℕ) (S : Occupation h) (k : Ch01.Band (2*h)) (hk : k ∉ S) :
    relativeCharge h (insert k S) = relativeCharge h S+1 := by
  simp [relativeCharge, Finset.card_insert_of_notMem hk]; omega

lemma charge_erase (h : ℕ) (S : Occupation h) (k : Ch01.Band (2*h)) (hk : k ∈ S) :
    relativeCharge h (S.erase k) = relativeCharge h S-1 := by
  have hp := Finset.card_pos.mpr ⟨k, hk⟩
  simp [relativeCharge, Finset.card_erase_of_mem hk, Nat.cast_sub hp]
  omega

lemma excitation_insert (h : ℕ) (S : Occupation h) (k : Ch01.Band (2*h)) (hk : k ∉ S) :
    excitationEnergy h (insert k S) = excitationEnergy h S+k.val-(relativeCharge h S+1) := by
  have hc := charge_insert h S k hk
  have hsum : Ch05.occupationEnergy (2*h) (insert k S) = k.val + Ch05.occupationEnergy (2*h) S := by
    unfold Ch05.occupationEnergy
    exact Finset.sum_insert hk
  have g1 := ground_energy_double (relativeCharge h S)
  have g2 := ground_energy_double (relativeCharge h S+1)
  unfold excitationEnergy relativeEnergy
  rw [hc, hsum]
  nlinarith

lemma excitation_erase (h : ℕ) (S : Occupation h) (k : Ch01.Band (2*h)) (hk : k ∈ S) :
    excitationEnergy h (S.erase k) = excitationEnergy h S-k.val+relativeCharge h S := by
  have hc := charge_erase h S k hk
  have hsum : Ch05.occupationEnergy (2*h) (S.erase k) = Ch05.occupationEnergy (2*h) S-k.val := by
    unfold Ch05.occupationEnergy
    have he := Finset.add_sum_erase S (fun k : Ch01.Band (2*h) => k.val) hk
    omega
  have g1 := ground_energy_double (relativeCharge h S)
  have g2 := ground_energy_double (relativeCharge h S-1)
  unfold excitationEnergy relativeEnergy
  rw [hc, hsum]
  nlinarith

lemma creation_budget_map (h : ℕ) (k : Ch01.Band (2*h)) (N K : ℤ) :
    ∀ v ∈ fixedBudget h N K,
      Ch05.momentumCreation (2*h) k v ∈ fixedBudget h (N+1) (K+k.val-(N+1)) := by
  intro v hv
  change v ∈ A03.coordinateSpace _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    change relativeCharge h S = N ∧ excitationEnergy h S ≤ K at hS
    have hck : Ch05.momentumCreation (2*h) k (A02.ket S) = if k ∈ S then 0 else Ch04.fermionSign k S • A02.ket (insert k S) := by
      convert Ch04.creation_ket k S using 1
      all_goals simp [Ch05.momentumCreation, Ch05.FockSpace, A02.ket, A02.occupationBasis, A02.occupationONB]
      all_goals split_ifs <;> first | rfl | (congr 2; ext i; simp only [Finset.mem_insert])
    rw [hck]
    by_cases hk : k ∈ S
    · simp [hk]
    · rw [ite_eq_right hk]
      apply Submodule.smul_mem
      apply (ket_mem_fixed_budget h _ _ _).mpr
      rw [charge_insert h S k hk, excitation_insert h S k hk, hS.1]
      exact ⟨rfl, by omega⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

lemma annihilation_budget_map (h : ℕ) (k : Ch01.Band (2*h)) (N K : ℤ) :
    ∀ v ∈ fixedBudget h N K,
      Ch05.momentumAnnihilation (2*h) k v ∈ fixedBudget h (N-1) (K-k.val+N) := by
  intro v hv
  change v ∈ A03.coordinateSpace _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    change relativeCharge h S = N ∧ excitationEnergy h S ≤ K at hS
    have hak : Ch05.momentumAnnihilation (2*h) k (A02.ket S) = if k ∈ S then Ch04.fermionSign k S • A02.ket (S.erase k) else 0 := by
      convert Ch04.annihilation_ket k S using 1
      all_goals simp [Ch05.momentumAnnihilation, Ch05.FockSpace, A02.ket, A02.occupationBasis, A02.occupationONB]
      all_goals split_ifs <;> congr 3
      all_goals exact Subsingleton.elim _ _
    rw [hak]
    by_cases hk : k ∈ S
    · rw [ite_eq_left hk]
      apply Submodule.smul_mem
      apply (ket_mem_fixed_budget h _ _ _).mpr
      rw [charge_erase h S k hk, excitation_erase h S k hk, hS.1]
      exact ⟨rfl, by omega⟩
    · simp [hk]
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

/-- A numerical window claim, not a density commutator or an implicit operator-word proof. -/
lemma active_window_in_band (h M K Nmax : ℕ) (N j : ℤ)
    (hN : |N| ≤ (Nmax : ℤ)) (hmargin : A03.uniformCutoff h M K Nmax)
    (hj : N-(K : ℤ)-(M : ℤ)+1 ≤ j ∧ j ≤ N+(K : ℤ)+(M : ℤ)) :
    Ch01.inBandPredicate (2*h) j := by
  have hn := abs_le.mp hN
  unfold A03.uniformCutoff at hmargin
  simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]
  omega

lemma word_window_in_band (h M K Nmax : ℕ) (N j : ℤ) (ds : List ℤ)
    (hN : |N| ≤ (Nmax : ℤ)) (hmargin : A03.wordCutoff h M K Nmax ds)
    (hj : N-(K : ℤ)-A03.upwardExcursion ds-(M : ℤ)+1 ≤ j ∧
      j ≤ N+(K : ℤ)+A03.upwardExcursion ds+(M : ℤ)) :
    Ch01.inBandPredicate (2*h) j := by
  have hn := abs_le.mp hN
  have hd := A03.excursion_nonneg ds
  have hc := Int.toNat_of_nonneg hd
  unfold A03.wordCutoff at hmargin
  simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]
  omega

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
    0 ≤ totalExcitation h S := by
  exact Finset.sum_nonneg (by intro ν _; exact excitation_nonneg h hh _)

lemma species_budget_ket (h : ℕ) (S : A02.Occupation (σ × Ch01.Band (2*h))) (Ns : σ → ℤ) (K : ℤ) :
    A02.ket S ∈ speciesBudget h Ns K ↔
      (∀ ν, relativeCharge h (speciesConfiguration h S ν) = Ns ν) ∧ totalExcitation h S ≤ K := by
  exact A03.ket_mem_coordinate_space _ S

lemma species_budget_negative (h : ℕ) (hh : 0 < h) (Ns : σ → ℤ) (K : ℤ) (hK : K < 0) :
    speciesBudget h Ns K = ⊥ := by
  have hs : {S | (∀ ν, relativeCharge h (speciesConfiguration h S ν) = Ns ν) ∧ totalExcitation h S ≤ K} = ∅ := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hS
    have := total_excitation_nonneg h hh S
    omega
  unfold speciesBudget
  rw [hs, A03.coordinate_space_empty]

end Species

end Bosonize.Ch07
