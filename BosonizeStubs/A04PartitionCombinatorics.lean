module

public import Bosonize.Core.Ch07VacuumBudget
public import Mathlib.Combinatorics.Enumerative.Partition.Basic

@[expose] public section
namespace Bosonize.A04Partitions
open scoped BigOperators Classical

abbrev EnergyConfigurations (h : ℕ) (N : ℤ) (K : ℕ) :=
  {S : Ch07.Occupation h // Ch07.relativeCharge h S = N ∧ Ch07.excitationEnergy h S = (K : ℤ)}

noncomputable def displacementParts (h : ℕ) (S : Ch07.Occupation h) : Multiset ℕ :=
  (Finset.univ.val.map fun i : Fin S.card => (Ch07.displacement h S i).toNat).filter (· ≠ 0)

noncomputable def displacementWeight (h : ℕ) (S : Ch07.Occupation h) : ℕ :=
  (displacementParts h S).sum

/-- The intrinsic weight keeps this complete data construction independent of unproved casts. -/
noncomputable def displacementPartition (h : ℕ) (S : Ch07.Occupation h) :
    Nat.Partition (displacementWeight h S) := Nat.Partition.ofMultiset (displacementParts h S)

def FitsRectangle {K : ℕ} (rows cols : ℕ) (p : Nat.Partition K) : Prop :=
  p.parts.card ≤ rows ∧ ∀ m ∈ p.parts, m ≤ cols

/-- Ascending displacements, including the omitted zero rows. -/
def paddedRows {K : ℕ} (rows : ℕ) (p : Nat.Partition K) : List ℕ :=
  List.replicate (rows-p.parts.card) 0 ++ p.parts.sort (· ≤ ·)

/-- The explicit inverse uses actual frozen integer momentum labels. -/
noncomputable def inverseConfiguration {K : ℕ} (h rows : ℕ) (p : Nat.Partition K) : Ch07.Occupation h :=
  Finset.univ.filter fun k => ∃ i : Fin rows,
    k.val = -(h : ℤ)+1+(i.val : ℤ)+((paddedRows rows p).getD i.val 0 : ℤ)

lemma displacement_parts_pos (h : ℕ) (S : Ch07.Occupation h) :
    ∀ m ∈ displacementParts h S, 0 < m := by sorry

lemma displacement_weight_energy (h : ℕ) (hh : 0 < h) (S : Ch07.Occupation h) :
    (displacementWeight h S : ℤ) = Ch07.excitationEnergy h S := by sorry

lemma displacement_partition_parts (h : ℕ) (S : Ch07.Occupation h) :
    (displacementPartition h S).parts = displacementParts h S := by sorry

lemma displacement_upper_bound (h : ℕ) (S : Ch07.Occupation h) (i : Fin S.card) :
    Ch07.displacement h S i ≤ (2*h-S.card : ℕ) := by sorry

lemma displacement_partition_rectangle (h : ℕ) (S : Ch07.Occupation h) :
    FitsRectangle S.card (2*h-S.card) (displacementPartition h S) := by sorry

lemma padded_rows_length {K : ℕ} (rows cols : ℕ) (p : Nat.Partition K)
    (hp : FitsRectangle rows cols p) : (paddedRows rows p).length = rows := by sorry

lemma padded_rows_monotone {K : ℕ} (rows : ℕ) (p : Nat.Partition K) : (paddedRows rows p).Pairwise (· ≤ ·) := by sorry

lemma padded_rows_sum {K : ℕ} (rows : ℕ) (p : Nat.Partition K) : (paddedRows rows p).sum = K := by sorry

lemma partition_card_le {K : ℕ} (p : Nat.Partition K) : p.parts.card ≤ K := by sorry

lemma padded_rows_filter {K : ℕ} (rows : ℕ) (p : Nat.Partition K) :
    ((paddedRows rows p : Multiset ℕ).filter (· ≠ 0)) = p.parts := by sorry

lemma padded_rows_get_le {K : ℕ} (rows cols : ℕ) (p : Nat.Partition K)
    (hp : FitsRectangle rows cols p) (i : Fin rows) :
    (paddedRows rows p).getD i.val 0 ≤ cols := by sorry

lemma inverse_labels_in_band {K : ℕ} (h rows : ℕ) (hr : rows ≤ 2*h)
    (p : Nat.Partition K) (hp : FitsRectangle rows (2*h-rows) p) (i : Fin rows) :
    Ch01.inBandPredicate (2*h)
      (-(h : ℤ)+1+(i.val : ℤ)+((paddedRows rows p).getD i.val 0 : ℤ)) := by sorry

lemma inverse_labels_strict_mono {K : ℕ} (rows cols : ℕ) (p : Nat.Partition K)
    (hp : FitsRectangle rows cols p) :
    StrictMono (fun i : Fin rows => (i.val : ℤ)+((paddedRows rows p).getD i.val 0 : ℤ)) := by sorry

lemma inverse_configuration_card {K : ℕ} (h rows : ℕ) (hr : rows ≤ 2*h)
    (p : Nat.Partition K) (hp : FitsRectangle rows (2*h-rows) p) :
    (inverseConfiguration h rows p).card = rows := by sorry

lemma inverse_configuration_charge {K : ℕ} (h rows : ℕ) (hr : rows ≤ 2*h)
    (p : Nat.Partition K) (hp : FitsRectangle rows (2*h-rows) p) :
    Ch07.relativeCharge h (inverseConfiguration h rows p) = (rows : ℤ)-(h : ℤ) := by sorry

lemma inverse_configuration_sorted_label {K : ℕ} (h rows : ℕ) (hr : rows ≤ 2*h)
    (p : Nat.Partition K) (hp : FitsRectangle rows (2*h-rows) p)
    (i : Fin (inverseConfiguration h rows p).card) :
    (Ch07.sortedMode h (inverseConfiguration h rows p) i).val =
      -(h : ℤ)+1+(i.val : ℤ)+((paddedRows rows p).getD i.val 0 : ℤ) := by sorry

lemma inverse_configuration_energy {K : ℕ} (h rows : ℕ) (hh : 0 < h)
    (hr : rows ≤ 2*h) (p : Nat.Partition K) (hp : FitsRectangle rows (2*h-rows) p) :
    Ch07.excitationEnergy h (inverseConfiguration h rows p) = (K : ℤ) := by sorry

lemma inverse_displacement_parts {K : ℕ} (h rows : ℕ) (hh : 0 < h)
    (hr : rows ≤ 2*h) (p : Nat.Partition K) (hp : FitsRectangle rows (2*h-rows) p) :
    displacementParts h (inverseConfiguration h rows p) = p.parts := by sorry

/-- Recover every row, including zeros omitted from the positive partition parts. -/
lemma padded_displacement_recovery (h : ℕ) (S : Ch07.Occupation h) :
    paddedRows S.card (displacementPartition h S) =
      List.ofFn (fun i : Fin S.card => (Ch07.displacement h S i).toNat) := by sorry

lemma displacement_inverse_configuration (h : ℕ) (S : Ch07.Occupation h) :
    inverseConfiguration h S.card (displacementPartition h S) = S := by sorry

/-- R1 removes both finite rectangle restrictions, including K=0 and empty/full sectors. -/
lemma partition_fits_r1 (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N) (K : ℕ)
    (hR1 : (K : ℤ) ≤ min ((h : ℤ)+N) ((h : ℤ)-N)) (p : Nat.Partition K) :
    FitsRectangle ((h : ℤ)+N).toNat ((h : ℤ)-N).toNat p := by sorry

/-- Construct the equivalence from the explicit maps and proved inverse identities.
Its statement names both actual maps rather than postulating a count. -/
theorem rectangle_equiv (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N) (K : ℕ) :
    ∃ e : EnergyConfigurations h N K ≃
      {p : Nat.Partition K // FitsRectangle ((h : ℤ)+N).toNat ((h : ℤ)-N).toNat p},
      (∀ S, (e S).val.parts = displacementParts h S.val) ∧
      (∀ p, (e.symm p).val = inverseConfiguration h ((h : ℤ)+N).toNat p.val) := by sorry

theorem unrestricted_equiv_r1 (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ)
    (hR1 : (K : ℤ) ≤ min ((h : ℤ)+N) ((h : ℤ)-N)) :
    ∃ e : EnergyConfigurations h N K ≃ Nat.Partition K,
      (∀ S, (e S).parts = displacementParts h S.val) ∧
      (∀ p, (e.symm p).val = inverseConfiguration h ((h : ℤ)+N).toNat p) := by sorry

lemma energy_space_finrank_coordinates (h : ℕ) (N : ℤ) (K : ℕ) :
    Module.finrank ℂ (Ch07.energySpace h N K) = Fintype.card (EnergyConfigurations h N K) := by sorry

theorem energy_space_finrank_r1 (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ)
    (hR1 : (K : ℤ) ≤ min ((h : ℤ)+N) ((h : ℤ)-N)) :
    Module.finrank ℂ (Ch07.energySpace h N K) = Fintype.card (Nat.Partition K) := by sorry

end Bosonize.A04Partitions
