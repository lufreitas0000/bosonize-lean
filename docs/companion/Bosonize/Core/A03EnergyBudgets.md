# A03 companion notebook — coordinate budgets and filtered maps

Status (2026-10-09): **Phase C: promoted and frozen in Core following the user's authorization.** Initial interface baseline: `20ed09b`; Phase B proof completion: `2b3186f`. A03 has 47 theorem proofs/19 data declarations; CH07 has 67 proofs/26 data declarations. Both are exposed through `import Bosonize`. All nine previously frozen Core sources remain unchanged.

The design/review sections below retain the historical Phase A rationale. References to proposed stubs in those sections describe the earlier design; all theorem bodies now have complete proofs.

## Source reconciliation and design choices

Read [A03](../../../../notes/appendices/a03_energy_budgets_and_filtered_maps.md), [CH07](../../../../notes/md/ch07_vacuum_budget_space.md), [TOC](../../../../notes/md/TOC.md), [appendix index](../../../../notes/appendices/README.md), the [proof revision guide](../../../../note/proof_suggestions_revision_2026-10-09.md) P07/P08, and the restricted-map, grading, and witness sections of [proof design](../../../../.agents/skills/formalizer/references/proof_design.md). Suggestion directories contain no available A03 or CH07 files. Old TOC/index claims that only CH01–CH02 are frozen are historical; the current Core has CH01–CH06, A01 and finite-CAR A02.

A03 supplies the reusable coordinate calculus; the chapter-specific integer charge, sea subtraction, sorted configurations and ground states live in CH07. This avoids a circular appendix/chapter import. The generic carrier is the actual finite occupation Hilbert space `A02.FockSpace ι` with `Fintype ι` and `DecidableEq ι`. It requires no artificial order on the mode type. `A02.extendBasis` constructs diagonal operators; coordinate spans are `Submodule.span ℂ (ket '' U)`. The projection uses the indicator of retained basis coordinates. These are complete definitions, without using unproved lemmas.

`budget charge energy N K` uses signed `K : ℤ`; negative budgets become zero only under the explicit hypothesis that the supplied energy function is nonnegative. Natural-cutoff extraction is a downstream operation. A03's generic charge and energy functions deliberately have no positivity assumption baked into their data. `fixedEnergy` and `chargeBox` distinguish an exact joint eigenspace, a fixed-sector upper cutoff, and an absolute-charge upper cutoff. Pairwise orthogonality and supremum decompositions describe their orthogonal direct-sum behavior without assuming a separate direct-sum basis.

`Filtered` requires every actual basis output to lie in the coordinate span with charge exactly shifted by q and energy bounded above by input energy+d. It has no hidden K parameter and implies maps for every signed budget. `ExactShift` has exact energy support and supplies the charge/energy observable commutators; an upper-bound shift alone does not imply the energy commutator. The identity witness is a theorem stub, not an assumed field of an operator structure. `restrictedMap` is an actual submodule-to-submodule linear map accepting an explicit image certificate. It does not manufacture that certificate from an unproved staging theorem.

Endomorphism multiplication acts right-to-left. `applicationWord [A,B]` evaluates to B*A because lists are in application order. `prefixShifts` scans signed shifts from zero; `upwardExcursion` takes the largest scanned value with zero included. Both `[2,-2]` and `[-2,2]` are explicit stub examples. `filtered_application_word` carries total charge/energy shifts, while `charge_preserving_word_prefix` bounds every actual prefix by the input cutoff plus maximum excursion. This latter wrapper requires q=0 for every step. Words that change charge require a separate intermediate charge-box bound; `wordCutoff` alone does not certify them.

The projection calculus retains `Ptarget*A*(1-Pmiddle)*B*Psource`. Equality is equivalent to its vanishing; preserving the intermediate image is a sufficient condition, not a required strengthening of every identity. The restricted adjoint reverses the projection side. `compress` is P*A*P on the ambient carrier, and its square differs from compressing A² by the explicit intermediate-escape term. No scalar finite-slice CCR is claimed. Polynomial oscillator constructions are deferred to CH08; these generic helpers state only the available coordinate/restriction calculus.

## Historical Phase A proof plan and review obligations

1. Basis-coordinate support and diagonal action; span monotonicity, unions and orthogonality.
2. Indicator projections: basis action, range, fixed vectors, idempotence, actual adjoint and commuting intersections; nonzero projection witness.
3. Signed budgets and exact-energy/charge-box decompositions, with nonnegative-energy premises where needed.
4. Filtered basis action to budget maps and composition; exact-shift observable commutators; negative-output annihilation.
5. Typed restricted maps, adjoint reversal, compression and exact remainder identities.
6. Prefix excursion arithmetic and application-order word bounds.

Every proposed theorem remains a one-sorry stub. The upstream basis APIs and construction types elaborate, but this does not establish the listed identities. Local proof support can be introduced inside Phase B bodies; new top-level helper declarations would need reviewed interfaces. Source advice to clip a negative output cutoff to zero is adapted to signed budgets so that annihilation below zero is not lost. Multi-species total energy is instantiated in CH07 on the combined mode carrier, not modeled as independent per-species cutoffs.

## Historical Phase A validation and phase boundary

Direct compilation and staging build pass with exactly 47 expected sorry warnings and no other warnings/errors. Native Lean MCP diagnostics complete with success=true, partial=false, 47 sorry-category warnings, and no failed dependencies. All 19 data declarations have only standard axioms (or none); all 47 theorem stubs depend on sorryAx. Guard tests: 69 passed. Core build passed. Against `509f323`, non-strict interface verification preserves 271 statements/225 commands, and all eight Core source hashes remain unchanged. Strict verification rejects exactly A03 and CH07 as new unlocked files, as intended. Full strict CI is not reported as passing for these unreviewed drafts. Toolchain, dependency manifest, both lock manifests and Core aggregator remain unchanged.

The primary agent used the repository formalizer skill; no subagents were dispatched for this phase. Unrelated source edits and suggestion-file deletions are preserved outside this task. Review the generic signed-cutoff API, projection side/order and application-order convention before approving the interface lock and Phase B.

## Historical Phase B proof strategy and validation

The user's Phase B instruction approved locking the two existing interfaces. The local A03/CH07 manifest entries were checked against their actual sources and committed at `20ed09b`; every pre-existing lock record remains unchanged. No new public declarations, imports, hypotheses or definitions were introduced. Only theorem bodies and module documentation changed.

Proof construction follows the actual occupation basis: coordinate support via span induction and finite expansion; diagonal adjoints via basis pairings; indicator projections via basis action; signed budget composition and exact-shift eigenspace commutators; actual restricted adjoints and noncommutative projection remainders. The original direct word-composition term exceeded elaboration limits, so that attempt was stopped. A separate local induction over signed budgets proves word action and every prefix before taking the maximum excursion; it avoids that term and compiles with the normal heartbeat limit. No limit or linter is disabled.

CH07 proves ground cardinality/energy by a bijection to a natural range and a doubled arithmetic-series identity. Sorted occupied labels give nonnegative, monotone displacements and their excitation sum. Zero excitation forces the unique threshold configuration; nonzero kets and an explicit one-step interior excitation provide the one-/two-dimensional witnesses. Frozen occupation margins follow from nonnegative energies after hypothetical insertion/erasure. Particle budget maps use the actual CAR basis action, reconciling order-derived and subtype decidable-equality instances without changing carriers. Multi-species budgets bound the sum of species energies.

Validation on the final sources:

- `STUB_LOCK_BASELINE_REF=20ed09b make ci`: all 69 regression tests, strict guard (457 statements/342 commands), all nine complete Core hashes and both library builds passed (`CI OK`). Neither staging chapter contains placeholders.
- Fresh warning-as-error compilation of both files: exit 0, no diagnostic output. CH07 was compiled after its A03 dependency finished rebuilding.
- Fresh `import BosonizeStubs` audit: 114 theorem proofs plus 45 data declarations use only `propext`, `Classical.choice`, `Quot.sound`, or no axioms; no `sorryAx`. This notebook reproduces its own results below.
- Native MCP diagnostics for each file: success=true, partial=false, timed_out=false, no items or failed dependencies. Native goal retrieval inspected ground uniqueness. Local MCP search failed because its child PATH lacks `rg`; shell search supplied installed source/signature retrieval. This does not affect the successful goal/diagnostic tools.
- Exact notebook/source snapshots and module SHA-256 values checked. Existing Core files, toolchain and dependency manifest remain unchanged.

One primary agent used the repository formalizer skill; no subagents were dispatched. Unrelated source-note edits and suggestion deletions remain preserved. This section records the pre-promotion Phase B snapshot; Phase C is recorded separately below.

## Twist-angle dictionary

A03 is generic coordinate calculus. CH07 uses integer reference energies on the existing sea. Choose the same real offset β and `b = Ch06Ext.angleTwist (2*h) β` for the physical fields and transport. `Ch06Ext.physical_relative_shift` adds β times relative charge; subtract the matching physical polynomial `N(N+1)/2 + β*N`. The proved `excitation_twist_cancel`, together with CH07's doubled ground-energy identity, identifies the resulting real excitation with the cast of `Ch07.excitationEnergy`. Thus these excitation budgets have the same labels for this sea and linear dispersion, while relative/ground physical energies and field transport retain their parameters. Centered APBC uses β = -1/2 and physical ground polynomial N²/2. Another sea, dispersion or species model requires its own bridge.

A standalone Lean example importing both chapters checks this exact bridge under warnings-as-errors. It is documented here and does not add a public declaration or alter the approved imports. See the [Ch06Ext notebook](Ch06Ext.md) for the proved transport/holonomy contracts.

### Checked standalone twist bridge

The following scratch example compiled with `lake env lean -DwarningAsError=true`, exit 0 and no diagnostics. It is separate from the locked module interface.

```lean
import Bosonize.Core.Ch07VacuumBudget
import Bosonize.Core.Ch06Ext

example (h : ℕ) (hh : 0 < h) (β : ℝ) (S : Bosonize.Ch07.Occupation h) :
    Bosonize.Ch06Ext.physicalRelativeEnergy (2*h) β S -
      Bosonize.Ch06Ext.physicalGroundEnergy β (Bosonize.Ch07.relativeCharge h S) =
      (Bosonize.Ch07.excitationEnergy h S : ℝ) := by
  simp only [Bosonize.Ch07.relativeCharge]
  rw [Bosonize.Ch06Ext.excitation_twist_cancel h hh β S]
  have hd := Bosonize.Ch07.ground_energy_double (Bosonize.Ch07.relativeCharge h S)
  have hr : 2*(Bosonize.Ch07.groundEnergy (Bosonize.Ch07.relativeCharge h S) : ℝ) =
      (Bosonize.Ch07.relativeCharge h S : ℝ)*((Bosonize.Ch07.relativeCharge h S : ℝ)+1) := by
    exact_mod_cast hd
  change ((Bosonize.Ch07.relativeEnergy h S : ℤ) : ℝ) -
      Bosonize.Ch06Ext.physicalGroundEnergy 0 (Bosonize.Ch07.relativeCharge h S) = _
  unfold Bosonize.Ch07.excitationEnergy Bosonize.Ch06Ext.physicalGroundEnergy
  push_cast
  nlinarith
```

## Phase C promotion and verification

The user authorized Phase C after proof completion at `2b3186f`. A03 moves byte-for-byte to Core. CH07 changes only `public import BosonizeStubs.A03EnergyBudgets` to `public import Bosonize.Core.A03EnergyBudgets`; every definition, explicit statement and proof body is preserved. Its single import-command record and 67 dependent theorem context hashes follow that authorized migration; theorem header hashes remain unchanged. All other existing interface entries and all nine earlier complete Core hashes are unchanged. The two whole-source hashes now freeze their proofs as well as interfaces. Both modules are exposed through `import Bosonize`, and direct staging imports are removed. The legacy manifest is retained.

Final verification on freshly built Core:

- `make ci`: all 69 guard tests, strict interface guard (457 statements/342 commands), eleven complete Core hashes and both library builds passed, with no warnings or placeholders (`CI OK`). `make lock-check` also passed.
- Each promoted source passes `lake env lean -DwarningAsError=true`, exit 0 and empty diagnostic output.
- Fresh `import Bosonize` audit covers all 457 Core theorems and all 45 newly promoted data declarations: 502 reports with only `propext`, `Classical.choice`, `Quot.sound`, or no axioms; no `sorryAx`. This module's data/theorem output is reproduced below.
- Native Lean MCP diagnostics on each Core file: success=true, partial=false, timed_out=false, zero items and zero failed dependencies. Native goal retrieval inspected the promoted CH07 ground-uniqueness proof.
- The standalone twist bridge above was recompiled with Core imports under warnings-as-errors, exit 0. It remains a documented checked example, not a new public theorem.
- Source snapshots, SHA values, migration-only source diffs and preserved earlier Core hashes were checked. No frozen proof is modified.

Use the committed Phase C promotion checkpoint as the current committed baseline. The historical `20ed09b` and `2b3186f` staging references precede the path/import migration. One primary formalizer used the repository skill; no subagents were dispatched. Unrelated note edits and suggestion deletions remain outside the commit. CH08/A04 Phase A is the planned next step and is not started.

## Reviewed source provenance

| Reviewed source | SHA-256 |
| --- | --- |
| `notes/appendices/a03_energy_budgets_and_filtered_maps.md` | `95a46eb53d1144e787e458677be2f1014832e84df8a5e2c7113cbebb47fad83b` |
| `notes/md/ch07_vacuum_budget_space.md` | `54f2a5d89b7f220cf2c850c44587b2eb3d6952b00d26d141ea9b61772496d81b` |
| `notes/md/TOC.md` | `5ea6b32bdecf8f9c65a345dc12356ff767b176c0b131e32acdb836778b054977` |
| `notes/appendices/README.md` | `ce871fab4a58ecb41a2b99d4ad4b055bb55e400753249fa88edde45fd15ebcd9` |
| `note/proof_suggestions_revision_2026-10-09.md` | `1db5f28b3e392d3b400ccc219ac640778fc5ceabc5cba17dfeb44b225a1b383c` |
| `.agents/skills/formalizer/references/proof_design.md` | `4d4391b355f701cee468d726a4c165010a4aa82c67449ec00e8a221759db585b` |

## Fresh Phase C data and theorem axiom output

```text
'Bosonize.A03.diagonal_ket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.diagonal_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.ket_mem_coordinate_space' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.coordinate_space_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.coordinate_space_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.coordinate_space_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.coordinate_space_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.coordinate_space_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.coordinate_space_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.projection_ket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.projection_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.projection_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.projection_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.projection_fixed_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.projection_intersection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.projection_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.projection_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.budget_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.box_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.negative_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.energy_spaces_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.budget_energy_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.box_sector_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.exact_shift_filtered' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.filtered_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.filtered_budget_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.filtered_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.filtered_lowering_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.exact_shift_charge_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.exact_shift_energy_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.compression_maps' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.compression_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.restricted_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.compressed_square_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.restricted_map_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.comp_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.projection_product_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.projected_product_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.projected_product_eq_of_maps' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.excursion_nonneg' depends on axioms: [propext]
'Bosonize.A03.prefix_le_excursion' depends on axioms: [propext]
'Bosonize.A03.excursion_le_positive' depends on axioms: [propext, Quot.sound]
'Bosonize.A03.excursion_up_down' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.excursion_down_up' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.word_cutoff_prefix' depends on axioms: [propext, Quot.sound]
'Bosonize.A03.filtered_application_word' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.charge_preserving_word_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.Operators' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.coordinateSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.coordinateProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.fixedEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.chargeBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.budgetProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.boxProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.Filtered' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.ExactShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.compress' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.restrictedMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.applicationWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.A03.prefixShifts' does not depend on any axioms
'Bosonize.A03.upwardExcursion' does not depend on any axioms
'Bosonize.A03.positiveExcursion' depends on axioms: [propext]
'Bosonize.A03.uniformCutoff' does not depend on any axioms
'Bosonize.A03.wordCutoff' does not depend on any axioms
```

## Exact Lean source snapshot

Module SHA-256: `6b1815b12c365614333ef59fc0e71dfcbea8955c5bb2e64b081f1b9317477291`. The block below matches the frozen Core module byte-for-byte and contains all exact signatures.

```lean
module

public import Bosonize.Core.A02CARHilbert

/-!
# A03: coordinate budgets and filtered maps
Phase B: complete constructions and proofs of the approved coordinate contracts.
Signed integer cutoffs retain negative-energy annihilation and composition excursions.
This coordinate calculus is generic in charge and energy. For the same-sea linear
model, Ch06Ext.excitation_twist_cancel relates the integer excitation labels to
arbitrary real twist offsets; no twist is silently selected by this module.
-/

@[expose] public section

namespace Bosonize.A03

open scoped BigOperators Classical

section Coordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Operators (ι : Type*) [Fintype ι] [DecidableEq ι] := Module.End ℂ (A02.FockSpace ι)

noncomputable def coordinateSpace (U : Set (A02.Occupation ι)) : Submodule ℂ (A02.FockSpace ι) :=
  Submodule.span ℂ (A02.ket '' U)

noncomputable def diagonal (a : A02.Occupation ι → ℂ) : Operators ι :=
  A02.extendBasis (fun S => a S • A02.ket S)

noncomputable def coordinateProjection (U : Set (A02.Occupation ι)) : Operators ι := by
  classical
  exact diagonal (fun S => if S ∈ U then 1 else 0)

noncomputable def fixedEnergy (charge energy : A02.Occupation ι → ℤ) (N E : ℤ) :
    Submodule ℂ (A02.FockSpace ι) :=
  coordinateSpace {S | charge S = N ∧ energy S = E}

noncomputable def budget (charge energy : A02.Occupation ι → ℤ) (N K : ℤ) :
    Submodule ℂ (A02.FockSpace ι) :=
  coordinateSpace {S | charge S = N ∧ energy S ≤ K}

noncomputable def chargeBox (charge energy : A02.Occupation ι → ℤ) (K : ℤ) (Nmax : ℕ) :
    Submodule ℂ (A02.FockSpace ι) :=
  coordinateSpace {S | energy S ≤ K ∧ |charge S| ≤ (Nmax : ℤ)}

noncomputable def budgetProjection (charge energy : A02.Occupation ι → ℤ) (N K : ℤ) : Operators ι :=
  coordinateProjection {S | charge S = N ∧ energy S ≤ K}

noncomputable def boxProjection (charge energy : A02.Occupation ι → ℤ) (K : ℤ) (Nmax : ℕ) : Operators ι :=
  coordinateProjection {S | energy S ≤ K ∧ |charge S| ≤ (Nmax : ℤ)}

/-- Every input basis vector has output supported in the stated shifted coordinate set. -/
def Filtered (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ) : Prop :=
  ∀ S, A (A02.ket S) ∈ coordinateSpace {T | charge T = charge S + q ∧ energy T ≤ energy S + d}

/-- Equality of the energy shift, for observable commutators rather than mere bounds. -/
def ExactShift (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ) : Prop :=
  ∀ S, A (A02.ket S) ∈ coordinateSpace {T | charge T = charge S + q ∧ energy T = energy S + d}

noncomputable def compress (U : Set (A02.Occupation ι)) (A : Operators ι) : Operators ι :=
  coordinateProjection U * A * coordinateProjection U

lemma diagonal_ket (a : A02.Occupation ι → ℂ) (S : A02.Occupation ι) :
    diagonal a (A02.ket S) = a S • A02.ket S := by
  exact A02.extend_basis_ket _ S

lemma diagonal_adjoint (a : A02.Occupation ι → ℂ) :
    LinearMap.adjoint (diagonal a) = diagonal (fun S => star (a S)) := by
  apply (A02.adjoint_of_basis_pairing _ _ ?_).symm
  intro S T
  rw [diagonal_ket, diagonal_ket, inner_smul_right, inner_smul_left,
    A02.ket_inner]
  by_cases h : S = T
  · subst T; simp
  · simp [h]

lemma ket_mem_coordinate_space (U : Set (A02.Occupation ι)) (S : A02.Occupation ι) :
    A02.ket S ∈ coordinateSpace U ↔ S ∈ U := by
  constructor
  · intro h
    by_contra hn
    have hz : ∀ v ∈ coordinateSpace U, v S = 0 := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨T, hT, rfl⟩ := hx
        simp [A02.ket_apply, show S ≠ T by intro he; subst T; exact hn hT]
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul a x _ hx => simp [hx]
    have := hz _ h
    simp [A02.ket_apply] at this
  · intro h
    exact Submodule.subset_span ⟨S, h, rfl⟩

lemma coordinate_space_support (U : Set (A02.Occupation ι)) (v : A02.FockSpace ι) :
    v ∈ coordinateSpace U ↔ ∀ S, S ∉ U → A02.coordinates ι v S = 0 := by
  constructor
  · intro h S hS
    change v S = 0
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨T, hT, rfl⟩ := hx
      simp [A02.ket_apply, show S ≠ T by intro he; subst T; exact hS hT]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  · intro hv
    rw [A02.occupation_expansion v]
    apply Submodule.sum_mem
    intro S _
    by_cases hS : S ∈ U
    · exact Submodule.smul_mem _ _ ((ket_mem_coordinate_space U S).mpr hS)
    · have hz := hv S hS
      change v S = 0 at hz
      simp [hz]

lemma coordinate_space_mono (U V : Set (A02.Occupation ι)) (hUV : U ⊆ V) :
    coordinateSpace U ≤ coordinateSpace V := by
  exact Submodule.span_mono (Set.image_mono hUV)

lemma coordinate_space_empty : coordinateSpace (∅ : Set (A02.Occupation ι)) = ⊥ := by
  simp [coordinateSpace]

lemma coordinate_space_univ : coordinateSpace (Set.univ : Set (A02.Occupation ι)) = ⊤ := by
  apply top_unique
  intro v _
  exact (coordinate_space_support _ v).mpr (by simp)

lemma coordinate_space_union (U V : Set (A02.Occupation ι)) :
    coordinateSpace (U ∪ V) = coordinateSpace U ⊔ coordinateSpace V := by
  simp [coordinateSpace, Set.image_union, Submodule.span_union]

lemma coordinate_space_disjoint (U V : Set (A02.Occupation ι)) (hUV : Disjoint U V) :
    ∀ u ∈ coordinateSpace U, ∀ v ∈ coordinateSpace V, inner ℂ u v = 0 := by
  intro u hu v hv
  rw [A02.fock_inner]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : S ∈ U
  · have hn : S ∉ V := fun hV => Set.disjoint_left.mp hUV hS hV
    have hz := (coordinate_space_support V v).mp hv S hn
    change v S = 0 at hz
    simp [hz]
  · have hz := (coordinate_space_support U u).mp hu S hS
    change u S = 0 at hz
    simp [hz]

lemma projection_ket (U : Set (A02.Occupation ι)) (S : A02.Occupation ι) :
    coordinateProjection U (A02.ket S) = if S ∈ U then A02.ket S else 0 := by
  classical
  simp [coordinateProjection, diagonal_ket]

lemma projection_idempotent (U : Set (A02.Occupation ι)) :
    coordinateProjection U * coordinateProjection U = coordinateProjection U := by
  apply A02.end_ext_basis
  intro S
  classical
  simp only [Module.End.mul_apply, projection_ket]
  split_ifs <;> simp [projection_ket, *]

lemma projection_adjoint (U : Set (A02.Occupation ι)) :
    LinearMap.adjoint (coordinateProjection U) = coordinateProjection U := by
  classical
  unfold coordinateProjection
  rw [diagonal_adjoint]
  congr 1
  funext S
  split_ifs <;> simp

lemma projection_range (U : Set (A02.Occupation ι)) :
    LinearMap.range (coordinateProjection U) = coordinateSpace U := by
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    rw [A02.occupation_expansion w, map_sum]
    apply Submodule.sum_mem
    intro S _
    rw [map_smul, projection_ket]
    split_ifs with hS
    · exact Submodule.smul_mem _ _ ((ket_mem_coordinate_space _ _).mpr hS)
    · simp
  · apply Submodule.span_le.mpr
    rintro v ⟨S, hS, rfl⟩
    exact ⟨A02.ket S, by simp [projection_ket, hS]⟩

lemma projection_fixed_iff (U : Set (A02.Occupation ι)) (v : A02.FockSpace ι) :
    coordinateProjection U v = v ↔ v ∈ coordinateSpace U := by
  constructor
  · intro h
    rw [← h]
    rw [← projection_range]
    exact ⟨v, rfl⟩
  · intro hv
    rw [← projection_range] at hv
    obtain ⟨w, rfl⟩ := hv
    exact congrArg (fun A : Operators ι => A w) (projection_idempotent U)

lemma projection_intersection (U V : Set (A02.Occupation ι)) :
    coordinateProjection U * coordinateProjection V = coordinateProjection (U ∩ V) := by
  apply A02.end_ext_basis
  intro S
  classical
  simp only [Module.End.mul_apply, projection_ket]
  by_cases hU : S ∈ U <;> by_cases hV : S ∈ V <;> simp [hU, hV, projection_ket]

lemma projection_commute (U V : Set (A02.Occupation ι)) :
    coordinateProjection U * coordinateProjection V = coordinateProjection V * coordinateProjection U := by
  rw [projection_intersection, projection_intersection, Set.inter_comm]

lemma projection_nonzero (U : Set (A02.Occupation ι)) (hU : U.Nonempty) :
    coordinateProjection U ≠ 0 := by
  obtain ⟨S, hS⟩ := hU
  intro hz
  have he := projection_ket U S
  rw [hz] at he
  simp only [LinearMap.zero_apply, ite_eq_left hS] at he
  exact A02.ket_ne_zero S he.symm

lemma budget_mono (charge energy : A02.Occupation ι → ℤ) (N K K' : ℤ) (hK : K ≤ K') :
    budget charge energy N K ≤ budget charge energy N K' := by
  apply coordinate_space_mono
  intro S hS
  exact ⟨hS.1, hS.2.trans hK⟩

lemma box_mono (charge energy : A02.Occupation ι → ℤ) (K K' : ℤ) (Nmax Nmax' : ℕ)
    (hK : K ≤ K') (hN : Nmax ≤ Nmax') :
    chargeBox charge energy K Nmax ≤ chargeBox charge energy K' Nmax' := by
  apply coordinate_space_mono
  intro S hS
  exact ⟨hS.1.trans hK, hS.2.trans (by exact_mod_cast hN)⟩

lemma negative_budget (charge energy : A02.Occupation ι → ℤ)
    (he : ∀ S, 0 ≤ energy S) (N K : ℤ) (hK : K < 0) : budget charge energy N K = ⊥ := by
  have hs : {S | charge S = N ∧ energy S ≤ K} = ∅ := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hS
    have := he S
    omega
  change coordinateSpace _ = _
  rw [hs, coordinate_space_empty]

lemma energy_spaces_orthogonal (charge energy : A02.Occupation ι → ℤ)
    (N E N' E' : ℤ) (hne : N ≠ N' ∨ E ≠ E') :
    ∀ u ∈ fixedEnergy charge energy N E, ∀ v ∈ fixedEnergy charge energy N' E',
      inner ℂ u v = 0 := by
  apply coordinate_space_disjoint
  apply Set.disjoint_left.mpr
  intro S hS hS'
  rcases hne with h | h
  · exact h (hS.1.symm.trans hS'.1)
  · exact h (hS.2.symm.trans hS'.2)

lemma budget_energy_decomposition (charge energy : A02.Occupation ι → ℤ)
    (he : ∀ S, 0 ≤ energy S) (N : ℤ) (K : ℕ) :
    budget charge energy N K = ⨆ E : Fin (K+1), fixedEnergy charge energy N (E.val : ℤ) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨S, hS, rfl⟩
    change charge S = N ∧ energy S ≤ (K : ℤ) at hS
    have hE := he S
    have hbound : (energy S).toNat < K+1 := by omega
    apply (le_iSup (fun E : Fin (K+1) => fixedEnergy charge energy N (E.val : ℤ)) ⟨(energy S).toNat, hbound⟩)
    apply (ket_mem_coordinate_space _ S).mpr
    exact ⟨hS.1, (Int.toNat_of_nonneg hE).symm⟩
  · apply iSup_le
    intro E
    apply coordinate_space_mono
    intro S hS
    change charge S = N ∧ energy S = (E.val : ℤ) at hS
    exact ⟨hS.1, by have := E.isLt; omega⟩

lemma box_sector_decomposition (charge energy : A02.Occupation ι → ℤ) (K : ℤ) (Nmax : ℕ) :
    chargeBox charge energy K Nmax = ⨆ N : {N : ℤ // |N| ≤ (Nmax : ℤ)}, budget charge energy N.val K := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨S, hS, rfl⟩
    apply (le_iSup (fun N : {N : ℤ // |N| ≤ (Nmax : ℤ)} => budget charge energy N.val K) ⟨charge S, hS.2⟩)
    apply (ket_mem_coordinate_space _ S).mpr
    exact ⟨rfl, hS.1⟩
  · apply iSup_le
    intro N
    apply coordinate_space_mono
    intro S hS
    exact ⟨hS.2, by rw [hS.1]; exact N.property⟩

lemma exact_shift_filtered (charge energy : A02.Occupation ι → ℤ) (A : Operators ι) (q d : ℤ)
    (hA : ExactShift charge energy A q d) : Filtered charge energy A q d := by
  intro S
  apply coordinate_space_mono _ _ (by intro T hT; change charge T = charge S + q ∧ energy T = energy S + d at hT; exact ⟨hT.1, hT.2.le⟩)
  exact hA S

lemma filtered_identity (charge energy : A02.Occupation ι → ℤ) :
    Filtered charge energy (1 : Operators ι) 0 0 := by
  intro S
  apply (ket_mem_coordinate_space _ S).mpr
  simp

lemma filtered_budget_map (charge energy : A02.Occupation ι → ℤ) (A : Operators ι)
    (q d N K : ℤ) (hA : Filtered charge energy A q d) :
    ∀ v ∈ budget charge energy N K, A v ∈ budget charge energy (N+q) (K+d) := by
  intro v hv
  change v ∈ coordinateSpace _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    change charge S = N ∧ energy S ≤ K at hS
    apply coordinate_space_mono _ _ (by
      intro T hT
      change charge T = charge S + q ∧ energy T ≤ energy S + d at hT
      exact ⟨by omega, by omega⟩)
    exact hA S
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

lemma filtered_comp (charge energy : A02.Occupation ι → ℤ) (A B : Operators ι)
    (qA dA qB dB : ℤ) (hA : Filtered charge energy A qA dA) (hB : Filtered charge energy B qB dB) :
    Filtered charge energy (A*B) (qB+qA) (dB+dA) := by
  intro S
  change A (B (A02.ket S)) ∈ _
  have hm := filtered_budget_map charge energy A qA dA (charge S+qB) (energy S+dB) hA _ (hB S)
  simpa [budget, add_assoc] using hm

lemma filtered_lowering_zero (charge energy : A02.Occupation ι → ℤ)
    (he : ∀ S, 0 ≤ energy S) (A : Operators ι) (q d N K : ℤ)
    (hA : Filtered charge energy A q d) (hKd : K+d < 0) :
    ∀ v ∈ budget charge energy N K, A v = 0 := by
  intro v hv
  have hm := filtered_budget_map charge energy A q d N K hA v hv
  rw [negative_budget charge energy he (N+q) (K+d) hKd] at hm
  exact hm

lemma exact_shift_charge_commutator (charge energy : A02.Occupation ι → ℤ)
    (A : Operators ι) (q d : ℤ) (hA : ExactShift charge energy A q d) :
    A02.commutator (diagonal (fun S => (charge S : ℂ))) A = (q : ℂ) • A := by
  apply A02.end_ext_basis
  intro S
  have eig : diagonal (fun T => (charge T : ℂ)) (A (A02.ket S)) =
      ((charge S+q : ℤ) : ℂ) • A (A02.ket S) := by
    have hs := (coordinate_space_support _ _).mp (hA S)
    conv_lhs => rw [A02.occupation_expansion (A (A02.ket S))]
    conv_rhs => rw [A02.occupation_expansion (A (A02.ket S))]
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : T ∈ {T | charge T = charge S+q ∧ energy T = energy S+d}
    · simp only [map_smul, diagonal_ket, smul_smul]
      rw [hT.1]
      congr 1; ring
    · have hz := hs T hT
      change A (A02.ket S) T = 0 at hz
      simp [hz]
  change diagonal (fun T => (charge T : ℂ)) (A (A02.ket S)) -
      A (diagonal (fun T => (charge T : ℂ)) (A02.ket S)) = (q : ℂ) • A (A02.ket S)
  rw [eig, diagonal_ket, map_smul, ← sub_smul]
  congr 1
  push_cast
  ring

lemma exact_shift_energy_commutator (charge energy : A02.Occupation ι → ℤ)
    (A : Operators ι) (q d : ℤ) (hA : ExactShift charge energy A q d) :
    A02.commutator (diagonal (fun S => (energy S : ℂ))) A = (d : ℂ) • A := by
  apply A02.end_ext_basis
  intro S
  have eig : diagonal (fun T => (energy T : ℂ)) (A (A02.ket S)) =
      ((energy S+d : ℤ) : ℂ) • A (A02.ket S) := by
    have hs := (coordinate_space_support _ _).mp (hA S)
    conv_lhs => rw [A02.occupation_expansion (A (A02.ket S))]
    conv_rhs => rw [A02.occupation_expansion (A (A02.ket S))]
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : T ∈ {T | charge T = charge S+q ∧ energy T = energy S+d}
    · simp only [map_smul, diagonal_ket, smul_smul]
      rw [hT.2]
      congr 1; ring
    · have hz := hs T hT
      change A (A02.ket S) T = 0 at hz
      simp [hz]
  change diagonal (fun T => (energy T : ℂ)) (A (A02.ket S)) -
      A (diagonal (fun T => (energy T : ℂ)) (A02.ket S)) = (d : ℂ) • A (A02.ket S)
  rw [eig, diagonal_ket, map_smul, ← sub_smul]
  congr 1
  push_cast
  ring

lemma compression_maps (U : Set (A02.Occupation ι)) (A : Operators ι) :
    ∀ v ∈ coordinateSpace U, compress U A v ∈ coordinateSpace U := by
  intro v _
  rw [← projection_range]
  exact ⟨A (coordinateProjection U v), rfl⟩

lemma compression_adjoint (U : Set (A02.Occupation ι)) (A : Operators ι) :
    LinearMap.adjoint (compress U A) = compress U (LinearMap.adjoint A) := by
  change LinearMap.adjoint ((coordinateProjection U).comp (A.comp (coordinateProjection U))) = _
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, projection_adjoint]
  rfl

lemma restricted_adjoint (P A B : Operators ι) (hP : LinearMap.adjoint P = P)
    (hAB : (A-B)*P = 0) : P*(LinearMap.adjoint A-LinearMap.adjoint B) = 0 := by
  have h := congrArg LinearMap.adjoint hAB
  rw [map_zero] at h
  change LinearMap.adjoint ((A-B).comp P) = 0 at h
  simpa only [LinearMap.adjoint_comp, map_sub, hP, Module.End.mul_eq_comp] using h

lemma compressed_square_remainder (U : Set (A02.Occupation ι)) (A : Operators ι) :
    compress U (A^2) - (compress U A)^2 =
      coordinateProjection U*A*(1-coordinateProjection U)*A*coordinateProjection U := by
  unfold compress
  have hP := projection_idempotent U
  simp only [pow_two]
  calc
    coordinateProjection U * (A*A) * coordinateProjection U -
        (coordinateProjection U*A*coordinateProjection U)*(coordinateProjection U*A*coordinateProjection U) =
        coordinateProjection U*A*A*coordinateProjection U -
        coordinateProjection U*A*(coordinateProjection U*coordinateProjection U)*A*coordinateProjection U := by simp only [mul_assoc]
    _ = _ := by rw [hP]; noncomm_ring

end Coordinates

section Restricted
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An actual linear map between submodule carriers, given its checked image condition. -/
def restrictedMap (U W : Submodule ℂ V) (A : Module.End ℂ V)
    (hA : ∀ v ∈ U, A v ∈ W) : U →ₗ[ℂ] W :=
  (A.domRestrict U).codRestrict W (fun v => hA v v.property)

/-- The list is in application order: [A,B] evaluates to B*A. -/
def applicationWord (As : List (Module.End ℂ V)) : Module.End ℂ V := As.reverse.prod

lemma restricted_map_apply (U W : Submodule ℂ V) (A : Module.End ℂ V)
    (hA : ∀ v ∈ U, A v ∈ W) (v : U) : (restrictedMap U W A hA v : V) = A v := by
  rfl

lemma comp_agree (U W : Submodule ℂ V) (A B C : Module.End ℂ V)
    (hC : ∀ v ∈ U, C v ∈ W) (hAB : ∀ w ∈ W, A w = B w) :
    ∀ v ∈ U, (A*C) v = (B*C) v := by
  intro v hv; exact hAB _ (hC v hv)

lemma projection_product_remainder (Ptarget Pmiddle Psource A B : Module.End ℂ V) :
    Ptarget*A*B*Psource - Ptarget*A*Pmiddle*B*Psource =
      Ptarget*A*(1-Pmiddle)*B*Psource := by
  noncomm_ring

lemma projected_product_eq_iff (Ptarget Pmiddle Psource A B : Module.End ℂ V) :
    Ptarget*A*B*Psource = Ptarget*A*Pmiddle*B*Psource ↔
      Ptarget*A*(1-Pmiddle)*B*Psource = 0 := by
  rw [← projection_product_remainder]; exact sub_eq_zero.symm

lemma projected_product_eq_of_maps (Ptarget Pmiddle Psource A B : Module.End ℂ V)
    (hB : Pmiddle*B*Psource = B*Psource) :
    Ptarget*A*B*Psource = Ptarget*A*Pmiddle*B*Psource := by
  calc
    Ptarget*A*B*Psource = Ptarget*A*(B*Psource) := by simp only [mul_assoc]
    _ = Ptarget*A*(Pmiddle*B*Psource) := by rw [hB]
    _ = _ := by simp only [mul_assoc]

end Restricted

/-- Prefixes are listed in application order, beginning with the zero shift. -/
def prefixShifts (ds : List ℤ) : List ℤ := ds.scanl (· + ·) 0

def upwardExcursion (ds : List ℤ) : ℤ := (prefixShifts ds).foldl max 0

def positiveExcursion (ds : List ℤ) : ℤ := (ds.map (fun d => max d 0)).sum

def uniformCutoff (h M K Nmax : ℕ) : Prop := 2*M+K+Nmax ≤ h

def wordCutoff (h M K Nmax : ℕ) (ds : List ℤ) : Prop :=
  2*M+K+(upwardExcursion ds).toNat+Nmax ≤ h

lemma excursion_nonneg (ds : List ℤ) : 0 ≤ upwardExcursion ds := by
  have bound (xs : List ℤ) (a : ℤ) : a ≤ xs.foldl max a := by
    induction xs generalizing a with
    | nil => exact le_rfl
    | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))
  exact bound _ 0

lemma prefix_le_excursion (ds : List ℤ) (d : ℤ) (hd : d ∈ prefixShifts ds) :
    d ≤ upwardExcursion ds := by
  have bound (xs : List ℤ) (a : ℤ) : a ≤ xs.foldl max a := by
    induction xs generalizing a with
    | nil => exact le_rfl
    | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))
  have member (xs : List ℤ) (a d : ℤ) (hd : d ∈ xs) : d ≤ xs.foldl max a := by
    induction xs generalizing a with
    | nil => simp at hd
    | cons x xs ih =>
      rcases List.mem_cons.mp hd with rfl | hd
      · exact (le_max_right a d).trans (bound xs _)
      · exact ih _ hd
  exact member _ 0 d hd

lemma excursion_le_positive (ds : List ℤ) : upwardExcursion ds ≤ positiveExcursion ds := by
  have positive (xs : List ℤ) : 0 ≤ (xs.map (fun d => max d 0)).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons]; have := le_max_right x 0; omega
  have scanBound (xs : List ℤ) (a d : ℤ) (hd : d ∈ xs.scanl (· + ·) a) :
      d ≤ a+(xs.map (fun x => max x 0)).sum := by
    induction xs generalizing a with
    | nil =>
      have he : d = a := by simpa using hd
      simpa using he.le
    | cons x xs ih =>
      rw [List.scanl_cons] at hd
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hd with rfl | hd
      · have := positive xs; have := le_max_right x 0; omega
      · have hb := ih (a+x) hd; have := le_max_left x 0; omega
  have fold (xs : List ℤ) (a b : ℤ) (hab : a ≤ b) (hx : ∀ x ∈ xs, x ≤ b) : xs.foldl max a ≤ b := by
    induction xs generalizing a with
    | nil => exact hab
    | cons x xs ih =>
      apply ih (max a x) (max_le hab (hx x (by simp)))
      intro y hy
      exact hx y (by simp [hy])
  apply fold _ _ _ (positive ds)
  intro d hd
  simpa [positiveExcursion] using scanBound ds 0 d hd

lemma excursion_up_down : upwardExcursion [2,-2] = 2 := by
  norm_num [upwardExcursion, prefixShifts]

lemma excursion_down_up : upwardExcursion [-2,2] = 0 := by
  norm_num [upwardExcursion, prefixShifts]

lemma word_cutoff_prefix (h M K Nmax : ℕ) (ds : List ℤ) (hw : wordCutoff h M K Nmax ds)
    (d : ℤ) (hd : d ∈ prefixShifts ds) :
    (2*M : ℤ)+(K : ℤ)+d+(Nmax : ℤ) ≤ (h : ℤ) := by
  have hb := prefix_le_excursion ds d hd
  have hn := Int.toNat_of_nonneg (excursion_nonneg ds)
  unfold wordCutoff at hw
  omega

section Words
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma filtered_application_word (charge energy : A02.Occupation ι → ℤ)
    (word : List (Operators ι × (ℤ × ℤ)))
    (hw : ∀ step ∈ word, Filtered charge energy step.1 step.2.1 step.2.2) :
    Filtered charge energy (applicationWord (word.map Prod.fst))
      (word.map (fun step => step.2.1)).sum (word.map (fun step => step.2.2)).sum := by
  have maps : ∀ (xs : List (Operators ι × (ℤ × ℤ))),
      (∀ step ∈ xs, Filtered charge energy step.1 step.2.1 step.2.2) →
      ∀ (N K : ℤ) (v : A02.FockSpace ι), v ∈ budget charge energy N K →
      applicationWord (xs.map Prod.fst) v ∈ budget charge energy
        (N+(xs.map (fun x => x.2.1)).sum) (K+(xs.map (fun x => x.2.2)).sum) := by
    intro xs
    induction xs with
    | nil => intro _ N K v hv; simpa [applicationWord] using hv
    | cons x xs ih =>
      intro hx N K v hv
      have hs := filtered_budget_map (ι := ι) charge energy x.1 x.2.1 x.2.2 N K
        (hx x List.mem_cons_self) v hv
      have hr := ih (fun y hy => hx y (List.mem_cons_of_mem x hy))
        (N+x.2.1) (K+x.2.2) (x.1 v) hs
      simpa only [applicationWord, List.map_cons, List.reverse_cons, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply, List.sum_cons,
        add_assoc] using hr
  intro S
  exact maps word hw (charge S) (energy S) (A02.ket S)
    ((ket_mem_coordinate_space _ S).mpr ⟨rfl, le_rfl⟩)

lemma charge_preserving_word_prefix (charge energy : A02.Occupation ι → ℤ)
    (word : List (Operators ι × ℤ))
    (hw : ∀ step ∈ word, Filtered charge energy step.1 0 step.2)
    (N K : ℤ) (r : ℕ) :
    ∀ v ∈ budget charge energy N K,
      applicationWord ((word.take r).map Prod.fst) v ∈
        budget charge energy N (K+upwardExcursion (word.map Prod.snd)) := by
  have maps : ∀ (xs : List (Operators ι × ℤ)),
      (∀ step ∈ xs, Filtered charge energy step.1 0 step.2) →
      ∀ (N K : ℤ) (v : A02.FockSpace ι), v ∈ budget charge energy N K →
      applicationWord (xs.map Prod.fst) v ∈ budget charge energy N (K+(xs.map Prod.snd).sum) := by
    intro xs
    induction xs with
    | nil => intro _ N K v hv; simpa [applicationWord] using hv
    | cons x xs ih =>
      intro hx N K v hv
      have hs := filtered_budget_map (ι := ι) charge energy x.1 0 x.2 N K
        (hx x List.mem_cons_self) v hv
      rw [add_zero] at hs
      have hr := ih (fun y hy => hx y (List.mem_cons_of_mem x hy)) N (K+x.2) (x.1 v) hs
      simpa only [applicationWord, List.map_cons, List.reverse_cons, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply, List.sum_cons,
        add_assoc] using hr
  have scanMember (xs : List ℤ) (r : ℕ) (a : ℤ) :
      a+(xs.take r).sum ∈ xs.scanl (· + ·) a := by
    induction xs generalizing r a with
    | nil => simp
    | cons x xs ih =>
      cases r with
      | zero => simp [List.scanl_cons]
      | succ r =>
        simp only [List.take_succ_cons, List.sum_cons, List.scanl_cons, List.mem_cons]
        exact Or.inr (by simpa only [add_assoc] using ih r (a+x))
  have hm : ((word.take r).map Prod.snd).sum ∈ prefixShifts (word.map Prod.snd) := by
    simpa only [prefixShifts, List.map_take, zero_add] using scanMember (word.map Prod.snd) r 0
  have hb := prefix_le_excursion (word.map Prod.snd) _ hm
  intro v hv
  apply budget_mono charge energy N (K+((word.take r).map Prod.snd).sum) (K+upwardExcursion (word.map Prod.snd)) (by omega)
  exact maps (word.take r) (fun x hx => hw x (List.mem_of_mem_take hx)) N K v hv

end Words

end Bosonize.A03
```
