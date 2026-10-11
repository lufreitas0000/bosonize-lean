# A04 constructive partition combinatorics — verified Core companion

Phase C is complete: 25 proved theorem targets and 7 complete data/abbreviation declarations. The module is frozen in [Core](../../../../Bosonize/Core/A04PartitionCombinatorics.lean). Source SHA-256: `7ca50bf6373bef397268ebfe2117df9cf9f9e67eddd4b53ec73e0473deaba399`. All original sixteen Core modules are unchanged.

Initial independent interface freeze: `c788bb3`; complete proof integration and reviewed geometric cleanup: `0ae13df`; independently reviewed Hall-recurrence cleanup: `ed3ad48`. The two cleanups remove redundant hypotheses without changing the physical Gram regime. The current signatures and proof bodies appear in the exact Core snapshot below; historical Phase A material is retained as design provenance.

Fresh Core-aggregator audits cover all 76 new declarations with permitted standard axioms only. Both library builds, all 69 guard tests, strict interface verification and complete-source freeze checks pass; both native MCP diagnostics are complete and empty. No warnings or placeholders remain in either source. The [Phase C validation](../../../../note/ch11_phase_c_validation_2026-10-11.md), [independent proof review](../../../../note/ch11_phase_b_review_2026-10-11.md), [cross-review](../../../../note/ch11_phase_b_cross_review_2026-10-11.md) and [pedagogical review](../../../../note/ch11_pedagogical_review_2026-10-11.md) record the evidence.

The complementary [pedagogical lecture](../../../../notes/appendices/a04_density_partitions_and_sugawara.md) preserves the reference theory and explains the actual finite construction. The chapter lecture realizes partition state order, exact grading, right-remainder contraction, Hall Gram and fixed/budget bases; the appendix lecture realizes positive displacement multisets, zero-padding, the explicit band-label inverse and the R1 dimension theorem. Sugawara remains Chapter 12 work.

# Historical A04 Phase A design

At Phase A this was a reviewed-interface candidate, not a proved partition count. Its support is restricted to CH11; no Sugawara declaration is included. Existing Core remains unchanged.

Sources: `notes/md/ch11_Haldane_completeness.md` §§11.1–11.3, `notes/appendices/a04_density_partitions_and_sugawara.md` Partitions and completeness, `notes/md/TOC.md`, and historical P06/P07 in `note/proof_suggestions_revision_2026-10-09.md`. The historical review is advisory. `docs/stub_suggestion/` and `docs/proof_suggestion/` are absent in this checkout. The source's partition suggestion is adopted after checking the installed `Mathlib.Combinatorics.Enumerative.Partition.Basic`: `Nat.Partition.parts`, `parts_pos`, `parts_sum`, `ofMultiset`, `ofSums` and the `Fintype` instance exist. No hypothetical partition enumeration API is used.

Flash and Pro provider names are not exposed by the available agent tool. Drafting uses the inherited available model; this is an explicit provider fallback, not an invocation of either requested provider.

The carrier is the actual CH07 occupation finset on the frozen positive-Nyquist integer band. Forward data filter the zero displacements from the natural extraction of CH07's actual sorted integer displacements. `displacementPartition` has intrinsic weight `displacementWeight`; hence its complete construction does not depend on an unproved energy cast. The energy equality is a separate theorem. `EnergyConfigurations` fixes actual charge and excitation energy. This retains the same-sea integer grading; existing CH06Ext/CH09 cancellation explains its compatibility with arbitrary physical offsets, without changing the reference sea.

The inverse is explicit: prepend omitted zero rows to the ascending partition parts, then occupy precisely frozen band labels `-h+1+i+d_i`. Filtering the band gives a complete data definition even before the rectangle certificates are proved. The rectangle ensures these labels are in the band and strictly increasing, making cardinality and sorted recovery exact. For empty/full sectors the only R1 energy is zero; zero rows and the empty finset are retained.

`rectangle_equiv` and `unrestricted_equiv_r1` are existential theorem contracts identifying both maps by exact parts/configuration equations. They assert an actual equivalence, not merely cardinal equality. The proofs will assemble the explicit maps only after energy and inverse identities are established. No data declaration contains an equivalence filled by placeholders or depends on staging theorem proofs.

Proof dependency plan:

1. Use CH07 displacement nonnegativity, monotonicity and sum to establish positivity and weight preservation. Upper displacement bound follows by monotonicity at the final occupied index and the upper band endpoint; handle an empty occupation by eliminating its index.
2. Prove elementary padding length/sum/filter/monotonicity/get bounds. `padded_rows_sum` and `padded_rows_monotone` have no rectangle premise: those identities hold for every padding length.
3. Show inverse labels lie in the band and are strictly increasing. Prove inverse cardinality, charge and sorted-label recovery. Installed `Finset.orderEmbOfFin_unique` identifies the sorted embedding from range membership and strict monotonicity.
4. Recover the inverse displacement list; establish energy and both inverse identities, then build the rectangle equivalence. R1 uses positivity to bound part count and each part by K, removing both rectangle restrictions.
5. Restrict the existing occupation basis to the coordinate set to establish finrank = configuration count, then transport the equivalence's finite cardinality. No dimension, Gram or spanning statement is assumed as a hypothesis.

Every statement remains exactly one `by sorry` for independent Phase A review. Phase B must replace them with proofs before any result is described as established.

Validation snapshot (2026-10-11):

- Source SHA-256: `e946bfcb008176ab178e1959085a42d8f0fd3094a6e7120432b242d6e886c535`.
- 25 theorem/lemma declarations, 25 expected placeholders; all theorem bodies satisfy the single-sorry contract.
- 7 complete data/abbreviation declarations. Fresh `#print axioms` for all 15 data declarations across both modules reports only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- `lake build BosonizeStubs.A04PartitionCombinatorics BosonizeStubs.Ch11HaldaneCompleteness` succeeds with expected staging sorry warnings only.
- Native Lean MCP error diagnostics for CH11 succeeded with complete, nonpartial empty error results. This is elaboration evidence, not proof completion.

Historical Phase A signatures (superseded by the complete Core source below):

```lean
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

lemma padded_displacement_recovery (h : ℕ) (S : Ch07.Occupation h) :
    paddedRows S.card (displacementPartition h S) =
      List.ofFn (fun i : Fin S.card => (Ch07.displacement h S i).toNat) := by sorry

lemma displacement_inverse_configuration (h : ℕ) (S : Ch07.Occupation h) :
    inverseConfiguration h S.card (displacementPartition h S) = S := by sorry

lemma partition_fits_r1 (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N) (K : ℕ)
    (hR1 : (K : ℤ) ≤ min ((h : ℤ)+N) ((h : ℤ)-N)) (p : Nat.Partition K) :
    FitsRectangle ((h : ℤ)+N).toNat ((h : ℤ)-N).toNat p := by sorry

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

```

## Phase B integration and scoped interface review

All theorem bodies are complete. Initial reviewed baseline: `c788bb3`. The [independent proof and migration review](../../../../note/ch11_phase_b_review_2026-10-11.md) approved dropping only the redundant positive-size hypothesis of `inverse_displacement_parts`; its geometric recovery proof also covers the empty h=0 case. The sole caller was adjusted; every other header, data declaration and existing Core file is unchanged. The signatures above are the historical Phase A snapshot. Fresh whole-module builds and all-declaration axiom audits precede promotion.

## Fresh Core axiom audit

```text
Bosonize.A04Partitions.EnergyConfigurations: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.displacementParts: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.displacementWeight: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.displacementPartition: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.FitsRectangle: propext
Bosonize.A04Partitions.paddedRows: propext, Quot.sound
Bosonize.A04Partitions.inverseConfiguration: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.displacement_parts_pos: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.displacement_weight_energy: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.displacement_partition_parts: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.displacement_upper_bound: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.displacement_partition_rectangle: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.padded_rows_length: propext, Quot.sound
Bosonize.A04Partitions.padded_rows_monotone: propext, Quot.sound
Bosonize.A04Partitions.padded_rows_sum: propext, Quot.sound
Bosonize.A04Partitions.partition_card_le: propext, Quot.sound
Bosonize.A04Partitions.padded_rows_filter: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.padded_rows_get_le: propext, Quot.sound
Bosonize.A04Partitions.inverse_labels_in_band: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.inverse_labels_strict_mono: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.inverse_configuration_card: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.inverse_configuration_charge: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.inverse_configuration_sorted_label: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.inverse_configuration_energy: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.inverse_displacement_parts: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.padded_displacement_recovery: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.displacement_inverse_configuration: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.partition_fits_r1: propext, Quot.sound
Bosonize.A04Partitions.rectangle_equiv: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.unrestricted_equiv_r1: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.energy_space_finrank_coordinates: propext, Classical.choice, Quot.sound
Bosonize.A04Partitions.energy_space_finrank_r1: propext, Classical.choice, Quot.sound
```

## Exact verified Core source

```lean
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
    ∀ m ∈ displacementParts h S, 0 < m := by
  intro m hm
  have hn := (Multiset.mem_filter.mp hm).2
  omega

lemma displacement_weight_energy (h : ℕ) (hh : 0 < h) (S : Ch07.Occupation h) :
    (displacementWeight h S : ℤ) = Ch07.excitationEnergy h S := by
  let ds := Finset.univ.val.map fun i : Fin S.card => (Ch07.displacement h S i).toNat
  have hfiltered : (ds.filter (· ≠ 0)).sum = ds.sum := by
    have hz : (ds.filter (· = 0)).sum = 0 := by
      apply Multiset.sum_eq_zero
      intro m hm
      exact (Multiset.mem_filter.mp hm).2
    have he := congrArg Multiset.sum (Multiset.filter_add_not (· = 0) ds)
    simpa [hz] using he
  change ((ds.filter (· ≠ 0)).sum : ℤ) = _
  rw [hfiltered, Nat.cast_multiset_sum, Multiset.map_map]
  change (∑ i : Fin S.card, ((Ch07.displacement h S i).toNat : ℤ)) = _
  simp only [Int.toNat_of_nonneg (Ch07.displacement_nonneg h S _)]
  exact (Ch07.excitation_displacement_sum h hh S).symm

lemma displacement_partition_parts (h : ℕ) (S : Ch07.Occupation h) :
    (displacementPartition h S).parts = displacementParts h S := by
  unfold displacementPartition Nat.Partition.ofMultiset Nat.Partition.ofSums
  exact Multiset.filter_eq_self.mpr (fun m hm => (displacement_parts_pos h S m hm).ne')

lemma displacement_upper_bound (h : ℕ) (S : Ch07.Occupation h) (i : Fin S.card) :
    Ch07.displacement h S i ≤ (2*h-S.card : ℕ) := by
  have hi := i.isLt
  let j : Fin S.card := ⟨S.card-1, by omega⟩
  have hij : i ≤ j := by change i.val ≤ S.card-1; omega
  have hm := Ch07.displacement_mono h S hij
  have hb : (Ch07.sortedMode h S j).val ≤ (h : ℤ) := by
    have hband := (Ch07.sortedMode h S j).property
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hband
    omega
  have hc := (Ch07.charge_admissible h S).2
  unfold Ch07.relativeCharge at hc
  have hj : j.val = S.card-1 := rfl
  unfold Ch07.displacement Ch07.referenceMode at hm ⊢
  rw [hj] at hm
  omega

lemma displacement_partition_rectangle (h : ℕ) (S : Ch07.Occupation h) :
    FitsRectangle S.card (2*h-S.card) (displacementPartition h S) := by
  rw [FitsRectangle, displacement_partition_parts]
  constructor
  · apply (Multiset.card_le_card (Multiset.filter_le _ _)).trans
    simp
  · intro m hm
    obtain ⟨hm, _⟩ := Multiset.mem_filter.mp hm
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hm
    have hb := displacement_upper_bound h S i
    have hn := Ch07.displacement_nonneg h S i
    omega

lemma padded_rows_length {K : ℕ} (rows cols : ℕ) (p : Nat.Partition K)
    (hp : FitsRectangle rows cols p) : (paddedRows rows p).length = rows := by
  have hc := hp.1
  simp only [paddedRows, List.length_append, List.length_replicate, Multiset.length_sort]
  omega

lemma padded_rows_monotone {K : ℕ} (rows : ℕ) (p : Nat.Partition K) : (paddedRows rows p).Pairwise (· ≤ ·) := by
  apply List.pairwise_append.mpr
  refine ⟨?_, Multiset.pairwise_sort _ _, ?_⟩
  · simp
  · intro a ha b hb
    have ha0 : a = 0 := by exact (List.mem_replicate.mp ha).2
    omega

lemma padded_rows_sum {K : ℕ} (rows : ℕ) (p : Nat.Partition K) : (paddedRows rows p).sum = K := by
  have hs : (p.parts.sort (· ≤ ·)).sum = K := by
    rw [← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]
  simpa [paddedRows] using hs

lemma partition_card_le {K : ℕ} (p : Nat.Partition K) : p.parts.card ≤ K := by
  have aux (s : Multiset ℕ) (hp : ∀ x ∈ s, 0 < x) : s.card ≤ s.sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      have ha := hp a (by simp)
      have hs := ih (by intro x hx; exact hp x (by simp [hx]))
      simp only [Multiset.card_cons, Multiset.sum_cons]
      omega
  simpa [p.parts_sum] using aux p.parts (fun x hx => p.parts_pos hx)

lemma padded_rows_filter {K : ℕ} (rows : ℕ) (p : Nat.Partition K) :
    ((paddedRows rows p : Multiset ℕ).filter (· ≠ 0)) = p.parts := by
  rw [paddedRows, ← Multiset.coe_add, Multiset.filter_add, Multiset.sort_eq]
  have hr : ((List.replicate (rows-p.parts.card) 0 : List ℕ) : Multiset ℕ).filter (· ≠ 0) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro x hx
    have hz : x = 0 := by exact (List.mem_replicate.mp hx).2
    simp [hz]
  rw [hr, zero_add]
  exact Multiset.filter_eq_self.mpr (fun x hx => (p.parts_pos hx).ne')

lemma padded_rows_get_le {K : ℕ} (rows cols : ℕ) (p : Nat.Partition K)
    (hp : FitsRectangle rows cols p) (i : Fin rows) :
    (paddedRows rows p).getD i.val 0 ≤ cols := by
  have hb : ∀ a ∈ paddedRows rows p, a ≤ cols := by
    intro a ha
    rcases List.mem_append.mp ha with hz | hm
    · have hz0 := (List.mem_replicate.mp hz).2
      omega
    · exact hp.2 a (Multiset.mem_sort (fun a b : ℕ => a ≤ b) |>.mp hm)
  have hi : i.val < (paddedRows rows p).length := by rw [padded_rows_length rows cols p hp]; exact i.isLt
  simp only [List.getD_eq_getElem?_getD, getElem?_pos (paddedRows rows p) i.val hi, Option.getD_some]
  exact hb _ (List.getElem_mem hi)

lemma inverse_labels_in_band {K : ℕ} (h rows : ℕ) (hr : rows ≤ 2*h)
    (p : Nat.Partition K) (hp : FitsRectangle rows (2*h-rows) p) (i : Fin rows) :
    Ch01.inBandPredicate (2*h)
      (-(h : ℤ)+1+(i.val : ℤ)+((paddedRows rows p).getD i.val 0 : ℤ)) := by
  have hd := padded_rows_get_le rows (2*h-rows) p hp i
  have hi := i.isLt
  simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]
  omega

lemma inverse_labels_strict_mono {K : ℕ} (rows cols : ℕ) (p : Nat.Partition K)
    (hp : FitsRectangle rows cols p) :
    StrictMono (fun i : Fin rows => (i.val : ℤ)+((paddedRows rows p).getD i.val 0 : ℤ)) := by
  intro i j hij
  have hi : i.val < (paddedRows rows p).length := by rw [padded_rows_length rows cols p hp]; exact i.isLt
  have hj : j.val < (paddedRows rows p).length := by rw [padded_rows_length rows cols p hp]; exact j.isLt
  have hm := (padded_rows_monotone rows p).sortedLE.getElem_le_getElem_of_le (hi := hi) (hj := hj) (le_of_lt hij)
  simp only [List.getD_eq_getElem?_getD, getElem?_pos (paddedRows rows p) i.val hi, getElem?_pos (paddedRows rows p) j.val hj, Option.getD_some]
  have hij' : i.val < j.val := hij
  omega

lemma inverse_configuration_card {K : ℕ} (h rows : ℕ) (hr : rows ≤ 2*h)
    (p : Nat.Partition K) (hp : FitsRectangle rows (2*h-rows) p) :
    (inverseConfiguration h rows p).card = rows := by
  let f : Fin rows → Ch01.Band (2*h) := fun i =>
    ⟨-(h : ℤ)+1+(i.val : ℤ)+((paddedRows rows p).getD i.val 0 : ℤ),
      inverse_labels_in_band h rows hr p hp i⟩
  have hf : Function.Injective f := by
    intro i j he
    have hev := congrArg Subtype.val he
    have hmono := (inverse_labels_strict_mono rows (2*h-rows) p hp).injective
    apply hmono
    dsimp [f] at hev
    dsimp only
    omega
  have hs : inverseConfiguration h rows p = Finset.univ.image f := by
    ext k
    simp only [inverseConfiguration, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi.symm⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (congrArg Subtype.val hi).symm⟩
  rw [hs, Finset.card_image_of_injective _ hf]
  simp

lemma inverse_configuration_charge {K : ℕ} (h rows : ℕ) (hr : rows ≤ 2*h)
    (p : Nat.Partition K) (hp : FitsRectangle rows (2*h-rows) p) :
    Ch07.relativeCharge h (inverseConfiguration h rows p) = (rows : ℤ)-(h : ℤ) := by
  simp [Ch07.relativeCharge, inverse_configuration_card h rows hr p hp]

lemma inverse_configuration_sorted_label {K : ℕ} (h rows : ℕ) (hr : rows ≤ 2*h)
    (p : Nat.Partition K) (hp : FitsRectangle rows (2*h-rows) p)
    (i : Fin (inverseConfiguration h rows p).card) :
    (Ch07.sortedMode h (inverseConfiguration h rows p) i).val =
      -(h : ℤ)+1+(i.val : ℤ)+((paddedRows rows p).getD i.val 0 : ℤ) := by
  let S := inverseConfiguration h rows p
  have hc : S.card = rows := inverse_configuration_card h rows hr p hp
  let f : Fin S.card → Ch01.Band (2*h) := fun j =>
    ⟨-(h : ℤ)+1+(j.val : ℤ)+((paddedRows rows p).getD j.val 0 : ℤ),
      inverse_labels_in_band h rows hr p hp (Fin.cast hc j)⟩
  have hmem : ∀ j, f j ∈ S := by
    intro j
    simp only [S, inverseConfiguration, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Fin.cast hc j, rfl⟩
  have hm : StrictMono f := by
    intro a b hab
    have hm := inverse_labels_strict_mono rows (2*h-rows) p hp
      (show Fin.cast hc a < Fin.cast hc b from hab)
    change -(h : ℤ)+1+(a.val : ℤ)+((paddedRows rows p).getD a.val 0 : ℤ) <
      -(h : ℤ)+1+(b.val : ℤ)+((paddedRows rows p).getD b.val 0 : ℤ)
    change (a.val : ℤ)+((paddedRows rows p).getD a.val 0 : ℤ) <
      (b.val : ℤ)+((paddedRows rows p).getD b.val 0 : ℤ) at hm
    omega
  have heq := Finset.orderEmbOfFin_unique (s := S) rfl hmem hm
  change ((S.orderEmbOfFin rfl) i).val = _
  rw [← heq]

lemma inverse_configuration_energy {K : ℕ} (h rows : ℕ) (hh : 0 < h)
    (hr : rows ≤ 2*h) (p : Nat.Partition K) (hp : FitsRectangle rows (2*h-rows) p) :
    Ch07.excitationEnergy h (inverseConfiguration h rows p) = (K : ℤ) := by
  have hc := inverse_configuration_card h rows hr p hp
  have hl := padded_rows_length rows (2*h-rows) p hp
  have hd (i : Fin (inverseConfiguration h rows p).card) :
      Ch07.displacement h (inverseConfiguration h rows p) i =
        ((paddedRows rows p).getD i.val 0 : ℤ) := by
    unfold Ch07.displacement Ch07.referenceMode
    rw [inverse_configuration_sorted_label h rows hr p hp]
    omega
  have heq : List.ofFn (fun i : Fin (inverseConfiguration h rows p).card =>
      (paddedRows rows p).getD i.val 0) = paddedRows rows p := by
    apply List.ext_getElem
    · simpa using hc.trans hl.symm
    · intro i hi hj
      simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD,
        getElem?_pos (paddedRows rows p) i hj, Option.getD_some]
  rw [Ch07.excitation_displacement_sum h hh]
  simp_rw [hd]
  have hs : (∑ i : Fin (inverseConfiguration h rows p).card,
      (paddedRows rows p).getD i.val 0) = K := by
    rw [← List.sum_ofFn, heq, padded_rows_sum]
  exact_mod_cast hs

lemma inverse_displacement_parts {K : ℕ} (h rows : ℕ)
    (hr : rows ≤ 2*h) (p : Nat.Partition K) (hp : FitsRectangle rows (2*h-rows) p) :
    displacementParts h (inverseConfiguration h rows p) = p.parts := by
  have hc := inverse_configuration_card h rows hr p hp
  have hl := padded_rows_length rows (2*h-rows) p hp
  have hd (i : Fin (inverseConfiguration h rows p).card) :
      Ch07.displacement h (inverseConfiguration h rows p) i =
        ((paddedRows rows p).getD i.val 0 : ℤ) := by
    unfold Ch07.displacement Ch07.referenceMode
    rw [inverse_configuration_sorted_label h rows hr p hp]
    omega
  have heq : List.ofFn (fun i : Fin (inverseConfiguration h rows p).card =>
      (paddedRows rows p).getD i.val 0) = paddedRows rows p := by
    apply List.ext_getElem
    · simpa using hc.trans hl.symm
    · intro i hi hj
      simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD,
        getElem?_pos (paddedRows rows p) i hj, Option.getD_some]
  unfold displacementParts
  simp_rw [hd, Int.toNat_natCast]
  rw [Fin.univ_val_map, heq]
  exact padded_rows_filter rows p

/-- Recover every row, including zeros omitted from the positive partition parts. -/
lemma padded_displacement_recovery (h : ℕ) (S : Ch07.Occupation h) :
    paddedRows S.card (displacementPartition h S) =
      List.ofFn (fun i : Fin S.card => (Ch07.displacement h S i).toNat) := by
  let l := List.ofFn (fun i : Fin S.card => (Ch07.displacement h S i).toNat)
  let m : Multiset ℕ := l
  have hparts : (displacementPartition h S).parts = m.filter (· ≠ 0) := by
    rw [displacement_partition_parts]
    unfold displacementParts
    rw [Fin.univ_val_map]
  have hlen : m.card = S.card := by simp [m, l]
  have hs := Multiset.filter_add_not (fun x : ℕ => x = 0) m
  have hz : m.filter (· = 0) = Multiset.replicate (m.filter (· = 0)).card 0 := by
    apply Multiset.eq_replicate_card.mpr
    intro x hx
    exact (Multiset.mem_filter.mp hx).2
  have hcard : (m.filter (· = 0)).card = S.card-(displacementPartition h S).parts.card := by
    have hc := congrArg Multiset.card hs
    rw [Multiset.card_add, hlen, ← hparts] at hc
    omega
  have hm : (paddedRows S.card (displacementPartition h S) : Multiset ℕ) = m := by
    rw [paddedRows, ← Multiset.coe_add, Multiset.coe_replicate, Multiset.sort_eq]
    rw [← hcard, ← hz, hparts]
    exact hs
  have hsort : l.Pairwise (· ≤ ·) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    have hd := Ch07.displacement_mono h S (le_of_lt hij)
    exact Int.toNat_le_toNat hd
  apply List.Perm.eq_of_pairwise' (padded_rows_monotone _ _) hsort
  exact Multiset.coe_eq_coe.mp hm

lemma displacement_inverse_configuration (h : ℕ) (S : Ch07.Occupation h) :
    inverseConfiguration h S.card (displacementPartition h S) = S := by
  ext k
  simp only [inverseConfiguration, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [padded_displacement_recovery]
  constructor
  · rintro ⟨i, hi⟩
    have hget : (List.ofFn (fun i : Fin S.card => (Ch07.displacement h S i).toNat)).getD i.val 0 =
        (Ch07.displacement h S i).toNat := by
      simp [List.getD_eq_getElem?_getD]
    rw [hget, Int.toNat_of_nonneg (Ch07.displacement_nonneg h S i)] at hi
    have he : k = Ch07.sortedMode h S i := by
      apply Subtype.ext
      unfold Ch07.displacement Ch07.referenceMode at hi
      omega
    rw [he]
    exact Ch07.sorted_mode_mem h S i
  · intro hk
    obtain ⟨i, hi⟩ : ∃ i : Fin S.card, Ch07.sortedMode h S i = k := by
      have hi := Finset.range_orderEmbOfFin S rfl
      rw [Set.ext_iff] at hi
      exact (hi k).mpr hk
    refine ⟨i, ?_⟩
    have hget : (List.ofFn (fun i : Fin S.card => (Ch07.displacement h S i).toNat)).getD i.val 0 =
        (Ch07.displacement h S i).toNat := by
      simp [List.getD_eq_getElem?_getD]
    rw [hget, Int.toNat_of_nonneg (Ch07.displacement_nonneg h S i)]
    have hv := congrArg Subtype.val hi
    unfold Ch07.displacement Ch07.referenceMode
    omega

/-- R1 removes both finite rectangle restrictions, including K=0 and empty/full sectors. -/
lemma partition_fits_r1 (h : ℕ) (N : ℤ) (hN : Ch07.admissible h N) (K : ℕ)
    (hR1 : (K : ℤ) ≤ min ((h : ℤ)+N) ((h : ℤ)-N)) (p : Nat.Partition K) :
    FitsRectangle ((h : ℤ)+N).toNat ((h : ℤ)-N).toNat p := by
  constructor
  · have hc := partition_card_le p
    have hn := hN.1
    have hR := (le_min_iff.mp hR1).1
    omega
  · intro m hm
    have hb := p.le_of_mem_parts hm
    have hn := hN.2
    have hR := (le_min_iff.mp hR1).2
    omega

/-- Construct the equivalence from the explicit maps and proved inverse identities.
Its statement names both actual maps rather than postulating a count. -/
theorem rectangle_equiv (h : ℕ) (hh : 0 < h) (N : ℤ) (hN : Ch07.admissible h N) (K : ℕ) :
    ∃ e : EnergyConfigurations h N K ≃
      {p : Nat.Partition K // FitsRectangle ((h : ℤ)+N).toNat ((h : ℤ)-N).toNat p},
      (∀ S, (e S).val.parts = displacementParts h S.val) ∧
      (∀ p, (e.symm p).val = inverseConfiguration h ((h : ℤ)+N).toNat p.val) := by
  have hlo := hN.1
  have hhi := hN.2
  let rows := ((h : ℤ)+N).toNat
  let cols := ((h : ℤ)-N).toNat
  have hrows : (rows : ℤ) = (h : ℤ)+N := by dsimp [rows]; omega
  have hcols : (cols : ℤ) = (h : ℤ)-N := by dsimp [cols]; omega
  have hr : rows ≤ 2*h := by omega
  have hrc : 2*h-rows = cols := by omega
  have card_eq (S : EnergyConfigurations h N K) : S.val.card = rows := by
    have hc := S.property.1
    unfold Ch07.relativeCharge at hc
    omega
  let forwardPartition (S : EnergyConfigurations h N K) : Nat.Partition K :=
    { parts := displacementParts h S.val
      parts_pos := fun hm => displacement_parts_pos h S.val _ hm
      parts_sum := by
        have he := displacement_weight_energy h hh S.val
        have hE := S.property.2
        unfold displacementWeight at he
        omega }
  have forwardFits (S : EnergyConfigurations h N K) : FitsRectangle rows cols (forwardPartition S) := by
    have hp := displacement_partition_rectangle h S.val
    rw [FitsRectangle, displacement_partition_parts] at hp
    change (displacementParts h S.val).card ≤ rows ∧ ∀ m ∈ displacementParts h S.val, m ≤ cols
    rw [card_eq S, hrc] at hp
    exact hp
  let forward (S : EnergyConfigurations h N K) :
      {p : Nat.Partition K // FitsRectangle rows cols p} := ⟨forwardPartition S, forwardFits S⟩
  let backward (p : {p : Nat.Partition K // FitsRectangle rows cols p}) : EnergyConfigurations h N K :=
    ⟨inverseConfiguration h rows p.val, by
      have hp : FitsRectangle rows (2*h-rows) p.val := by simpa [hrc] using p.property
      constructor
      · rw [inverse_configuration_charge h rows hr p.val hp, hrows]
        omega
      · exact inverse_configuration_energy h rows hh hr p.val hp⟩
  have leftInv (S : EnergyConfigurations h N K) : backward (forward S) = S := by
    apply Subtype.ext
    change inverseConfiguration h rows (forwardPartition S) = S.val
    rw [← card_eq S]
    have hid : inverseConfiguration h S.val.card (forwardPartition S) =
        inverseConfiguration h S.val.card (displacementPartition h S.val) := by
      unfold inverseConfiguration paddedRows
      rw [displacement_partition_parts]
    rw [hid, displacement_inverse_configuration]
  have rightInv (p : {p : Nat.Partition K // FitsRectangle rows cols p}) : forward (backward p) = p := by
    apply Subtype.ext
    apply Nat.Partition.ext
    change displacementParts h (inverseConfiguration h rows p.val) = p.val.parts
    apply inverse_displacement_parts h rows hr p.val
    simpa [hrc] using p.property
  let e : EnergyConfigurations h N K ≃ {p : Nat.Partition K // FitsRectangle rows cols p} :=
    { toFun := forward, invFun := backward, left_inv := leftInv, right_inv := rightInv }
  refine ⟨e, ?_, ?_⟩
  · intro S; rfl
  · intro p; rfl

theorem unrestricted_equiv_r1 (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ)
    (hR1 : (K : ℤ) ≤ min ((h : ℤ)+N) ((h : ℤ)-N)) :
    ∃ e : EnergyConfigurations h N K ≃ Nat.Partition K,
      (∀ S, (e S).parts = displacementParts h S.val) ∧
      (∀ p, (e.symm p).val = inverseConfiguration h ((h : ℤ)+N).toNat p) := by
  obtain ⟨e, he, hi⟩ := rectangle_equiv h hh N hN K
  let forget : {p : Nat.Partition K // FitsRectangle ((h : ℤ)+N).toNat ((h : ℤ)-N).toNat p} ≃ Nat.Partition K :=
    { toFun := fun p => p.val
      invFun := fun p => ⟨p, partition_fits_r1 h N hN K hR1 p⟩
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun p => rfl }
  refine ⟨e.trans forget, ?_, ?_⟩
  · intro S; exact he S
  · intro p; exact hi ⟨p, partition_fits_r1 h N hN K hR1 p⟩

lemma energy_space_finrank_coordinates (h : ℕ) (N : ℤ) (K : ℕ) :
    Module.finrank ℂ (Ch07.energySpace h N K) = Fintype.card (EnergyConfigurations h N K) := by
  set_option maxHeartbeats 800000 in
    let v : EnergyConfigurations h N K → Ch07.FockSpace h :=
      fun S => A02.occupationBasis (Ch01.Band (2*h)) S.val
    have hli : LinearIndependent ℂ v :=
      (A02.occupationBasis (Ch01.Band (2*h))).linearIndependent.comp (fun S : EnergyConfigurations h N K => S.val) Subtype.val_injective
    have hrange : Set.range v = A02.ket '' {S | Ch07.relativeCharge h S = N ∧ Ch07.excitationEnergy h S = (K : ℤ)} := by
      ext x
      constructor
      · rintro ⟨S, rfl⟩
        exact ⟨S.val, S.property, rfl⟩
      · rintro ⟨S, hS, rfl⟩
        exact ⟨⟨S, hS⟩, rfl⟩
    change Module.finrank ℂ (Submodule.span ℂ (A02.ket '' _)) = _
    rw [← hrange]
    exact finrank_span_eq_card hli

theorem energy_space_finrank_r1 (h : ℕ) (hh : 0 < h) (N : ℤ)
    (hN : Ch07.admissible h N) (K : ℕ)
    (hR1 : (K : ℤ) ≤ min ((h : ℤ)+N) ((h : ℤ)-N)) :
    Module.finrank ℂ (Ch07.energySpace h N K) = Fintype.card (Nat.Partition K) := by
  obtain ⟨e, _, _⟩ := unrestricted_equiv_r1 h hh N hN K hR1
  rw [energy_space_finrank_coordinates]
  exact Fintype.card_congr e

end Bosonize.A04Partitions
```
