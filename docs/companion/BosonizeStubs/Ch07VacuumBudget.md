# CH07 companion notebook — sectors, excitation energy and budgets

Status (2026-10-09): **Phase A complete; unlocked and unproved, awaiting interface review.** Baseline: `509f323`. This draft has 26 complete data declarations and 67 theorem stubs. It depends on the proposed A03 interface; combined elaboration does not prove either module.

## Source reconciliation and scope

Read [CH07](../../../notes/md/ch07_vacuum_budget_space.md), [A03](../../../notes/appendices/a03_energy_budgets_and_filtered_maps.md), [TOC](../../../notes/md/TOC.md), [appendix index](../../../notes/appendices/README.md), [revision guide](../../../note/proof_suggestions_revision_2026-10-09.md) P07/P08, and the relevant [proof-design contracts](../../../.agents/skills/formalizer/references/proof_design.md). No chapter-specific suggestion file is available. Adopt the finite occupation model and actual positive-Nyquist band from frozen CH01/CH04/CH05. Source snippets remain advisory; no bare natural subtraction or reflection-symmetric band is introduced.

The physical lemmas explicitly take h>0 and use L=2*h. Algebraic data also elaborate at h=0; no positive-sea interpretation is assigned there. Admissibility is inclusive `-h ≤ N ≤ h`, including empty and full sectors. A03's opening word “strictly” is interpreted according to its written inclusive inequalities and the chapter's explicit endpoint discussion; excited witness statements require the separate strict interior condition. The source files are preserved.

## Carriers, integer energy and rank

`Occupation h` is `Finset (Ch01.Band (2*h))`, and the Hilbert carrier is the frozen CH05/A02 finite occupation space. Charge is `(S.card : ℤ)-h`. Relative energy is the bare sum minus `Ch05.seaEnergy (2*h)`. Ground energy is `N*(N+1)/2` in ℤ. Evenness, the double identity, and uniqueness are explicit theorem stubs, covering negative charges too. Excitation is relative energy minus that ground energy. `excitationNat` is defined using toNat, but its faithful integer cast is a stub requiring nonnegativity; no later theorem should assume toNat has preserved a negative value.

`groundConfiguration h N` is the threshold filter k≤N. Outside admissibility it is merely clipped; `groundKet` explicitly requires an admissibility certificate, so it cannot be called a ground state in an empty sector. Empty/full ground configurations are separate endpoint stubs. Vacuum data reuse the actual frozen sea ket. Ground/vacuum nonzero statements are proposed witnesses, not proved facts.

Sorted modes use the installed `Finset.orderEmbOfFin rfl`, indexed by `Fin S.card`; this covers S=∅ without natural conversion of h+N. Reference modes are `-h+1+i`, with integer subtraction. Nonnegative and nondecreasing displacements are independent stubs; the reindexed sum and excitation=sum(displacements) supply the intended minimal-energy proof. Ground uniqueness concerns configurations; zero-energy dimension one concerns the span of their nonzero ket.

`chargeObservable` and `excitationObservable` are genuine diagonal linear maps constructed by A03. Their adjoints, basis action and identification of relative charge with total number minus hI are stubs. The vacuum-subtracted Hamiltonian is identified with the relative-energy diagonal, not with excitation across all sectors. Subtracting the charge-dependent triangular term distinguishes these observables.

## Budget data, witnesses, action and margins

`energySpace`, `fixedBudget`, `boxBudget`, `fixedProjection`, `boxProjection` and `compressed` retain their full N/K/Nmax labels. Integer K avoids natural subtraction for lowering operations. Projections are constructed from coordinates and require later range/idempotence/adjoint proofs. Ground membership is proposed for every admissible charge and every natural cutoff, including K=0. Zero energy/budget is the ground span. The excited-configuration and dimension≥2 witnesses use `-h<N<h` and K≥1, since an extremal empty/full sector has only one configuration.

Frozen-full and frozen-empty statements quantify actual in-band modes: k≤N-K is occupied, k>N+K is empty. The opposite assumptions imply excitation>K. They require the displacement bounds, rather than a loose unsupported bound on individual occupations. These are configuration statements; linear budget statements follow through coordinate support.

Creation/annihilation have sector-dependent excitation changes. For an unoccupied k, creation changes charge by +1 and excitation by `k-(N+1)`; annihilation at occupied k changes charge by -1 and excitation by `N-k`. The proposed budget maps retain these shifts and target sectors. They do not assume momentum generators are energy-homogeneous with one global excitation shift. Generic filtered maps inherit A03's exact support condition; keeping the same charge sector requires q=0 explicitly. Negative target cutoff gives annihilation after excitation nonnegativity.

`active_window_in_band` and `word_window_in_band` are exact numerical interval statements. They use actual asymmetric bounds and the conservative 2M+K+excursion+Nmax≤h regime. They do not assert density commutators, operator-word hypotheses or an unstated charge-preserving property. Such operators are future chapter scope. Restricted equality, typed composition and projection remainders are supplied by A03.

For multiple finite species σ, the combined carrier is `A02.FockSpace (σ × Band (2*h))`. `speciesConfiguration` extracts each species from the actual combined occupation. `totalExcitation` sums over species, and `speciesBudget` fixes the charge vector with one bound on that sum. This is not a tensor product of independently cutoff budgets. Nonnegativity, ket membership and negative-budget vanishing are proposed stubs; no unproved finite-species decomposition is built into the definitions.

## Proposed Phase B dependency order and unresolved obligations

1. Integer triangular identities and ground threshold cardinality/energy, using frozen sea/band arithmetic.
2. Sorted-mode reindexing, rank lower bound, monotone displacements and excitation sum, including empty/full configurations.
3. Nonnegative energy, ground uniqueness, exact integer extraction and genuine nonzero/one-step witnesses.
4. Reuse proved A03 coordinate calculus for observables, ground spans, dimensions and budget projections.
5. Frozen occupation margins and sector-dependent particle-action budget maps, with explicit carrier-instance transport if needed.
6. Apply generic filtered/word helpers to the numerical window bounds and total-species energy convention.

No supporting stub is consumed by a definition. These obligations can need local decompositions in Phase B; any new top-level helper/interface must receive review. No current/density scalar CCR, oscillator representation, charge-sector isometry or analytic limit is claimed.

## Validation and review boundary

Direct compilation and staging build pass with exactly 67 expected sorry warnings and no other warnings/errors. Native Lean MCP diagnostics complete with success=true, partial=false, 67 sorry-category warnings, and no failed dependencies. All 26 data declarations have only standard axioms (or none); all 67 theorem stubs expose sorryAx. Both library builds and all 69 guard tests pass. Against `509f323`, all 271 approved statements/225 commands and eight complete Core hashes are unchanged. Strict verification rejects exactly the two new unlocked drafts. All manifests, dependency/toolchain state and the Core aggregator are preserved.

A separate finite Python sanity check covers 340 configurations for h=1..4: rank/displacement identity, ground uniqueness, full/empty margins, creation/annihilation excitation shifts, and an interior-sector one-step witness. It supplies counterexample screening only, not Lean proof evidence. The primary formalizer used the repository skill without subagents. Review integer-energy conventions, admissible endpoints, signed budgets, nonvacuous interior witnesses and the proposed A03 contracts together before locking or Phase B.

## Reviewed source provenance

| Reviewed source | SHA-256 |
| --- | --- |
| `notes/appendices/a03_energy_budgets_and_filtered_maps.md` | `95a46eb53d1144e787e458677be2f1014832e84df8a5e2c7113cbebb47fad83b` |
| `notes/md/ch07_vacuum_budget_space.md` | `54f2a5d89b7f220cf2c850c44587b2eb3d6952b00d26d141ea9b61772496d81b` |
| `notes/md/TOC.md` | `5ea6b32bdecf8f9c65a345dc12356ff767b176c0b131e32acdb836778b054977` |
| `notes/appendices/README.md` | `ce871fab4a58ecb41a2b99d4ad4b055bb55e400753249fa88edde45fd15ebcd9` |
| `note/proof_suggestions_revision_2026-10-09.md` | `1db5f28b3e392d3b400ccc219ac640778fc5ceabc5cba17dfeb44b225a1b383c` |
| `.agents/skills/formalizer/references/proof_design.md` | `4d4391b355f701cee468d726a4c165010a4aa82c67449ec00e8a221759db585b` |

## Fresh data and stub axiom output

```text
'Bosonize.Ch07.Occupation' depends on axioms: [propext, Quot.sound]
'Bosonize.Ch07.FockSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.Operators' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.admissible' does not depend on any axioms
'Bosonize.Ch07.relativeCharge' depends on axioms: [propext, Quot.sound]
'Bosonize.Ch07.relativeEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.groundEnergy' does not depend on any axioms
'Bosonize.Ch07.excitationEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.excitationNat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.groundConfiguration' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.groundKet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.vacuumKet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.sortedMode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.referenceMode' depends on axioms: [propext, Quot.sound]
'Bosonize.Ch07.displacement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.chargeObservable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.excitationObservable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.energySpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.fixedBudget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.boxBudget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.fixedProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.boxProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.compressed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.speciesConfiguration' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.totalExcitation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.speciesBudget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch07.ground_energy_even' depends on axioms: [sorryAx]
'Bosonize.Ch07.ground_energy_double' depends on axioms: [sorryAx]
'Bosonize.Ch07.ground_energy_unique' depends on axioms: [sorryAx]
'Bosonize.Ch07.charge_admissible' depends on axioms: [propext, sorryAx, Quot.sound]
'Bosonize.Ch07.ground_configuration_card' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.ground_configuration_charge' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.ground_configuration_energy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.ground_configuration_excitation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.ground_configuration_zero' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.ground_configuration_empty' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.ground_configuration_full' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.vacuum_charge' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.vacuum_relative_energy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.vacuum_excitation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.ground_ket_ne_zero' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.vacuum_ket_ne_zero' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.sorted_mode_mem' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.sorted_mode_strict_mono' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.energy_sorted_sum' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.sorted_mode_lower_bound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.displacement_nonneg' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.displacement_mono' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.excitation_displacement_sum' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.excitation_nonneg' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.excitation_nat_cast' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.excitation_zero_iff_ground' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.charge_observable_ket' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.excitation_observable_ket' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.charge_observable_adjoint' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.excitation_observable_adjoint' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.charge_observable_total_number' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.relative_hamiltonian_diagonal' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.ket_mem_fixed_budget' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.ground_ket_mem_budget' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.vacuum_ket_mem_box' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.zero_energy_ground_span' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.zero_energy_dimension_one' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.zero_budget_ground_span' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.inadmissible_budget' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.negative_budget' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.excited_configuration_exists' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.budget_dimension_ge_two' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.displacement_le_budget' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.frozen_full' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.frozen_empty' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.missing_deep_energy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.occupied_high_energy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.fixed_projection_idempotent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.fixed_projection_adjoint' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.fixed_projection_range' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.box_projection_idempotent' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.box_projection_adjoint' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.box_projection_range' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.filtered_budget_map' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.charge_preserving_budget_map' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.negative_shift_annihilates' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.charge_insert' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.charge_erase' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.excitation_insert' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.excitation_erase' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.creation_budget_map' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.annihilation_budget_map' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.active_window_in_band' depends on axioms: [propext, sorryAx]
'Bosonize.Ch07.word_window_in_band' depends on axioms: [propext, sorryAx]
'Bosonize.Ch07.total_excitation_nonneg' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.species_budget_ket' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Bosonize.Ch07.species_budget_negative' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Exact Lean source snapshot

Module SHA-256: `70777c777381ed0ad84ecd0a695c2206a02ac8d00b5fd0ebd0bf520f12bd334c`. The block below matches the draft byte-for-byte and contains all exact signatures.

```lean
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
```
