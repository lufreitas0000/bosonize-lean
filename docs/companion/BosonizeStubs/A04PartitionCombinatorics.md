# A04 partition combinatorics — Phase A companion

This is a reviewed-interface candidate, not a proved partition count. Its support is restricted to CH11; no Sugawara declaration is included. Existing Core remains unchanged.

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

Exact proposed signatures:

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
