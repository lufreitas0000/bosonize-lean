# CH06 companion notebook — finite local CAR net

Status: **Phase B proof bodies complete; Phase C not started**. The approved interface is frozen at baseline `34150a5`. This file mirrors `BosonizeStubs/Ch06LocalNet.lean`: 26 complete definitions/abbreviations and 54 complete lemma proof bodies. The historical Phase A source reconciliation and proposed dependency inventory below are retained; the source snapshot is current. Fresh imported-dependency axiom evidence is recorded in the Phase B section.

## Source reconciliation and scope

The principal source is `notes/md/ch06_lattice_AQFT_net.md`, read with `notes/md/TOC.md`, the finite-CAR appendix `notes/appendices/a02_car_hilbert_and_normal_ordering.md`, the applicable source-contract and noncommutative sections of `.agents/skills/formalizer/references/proof_design.md`, and the dated review `note/proof_suggestions_revision_2026-10-09.md`. The completion ledger `note/notes_review_completion_2026-10-09.md` supplies review context, not Lean proofs. The TOC introductory claim that only CH01–CH02 are frozen is historical and superseded by the current Core and adaptive roadmap.

No `docs/stub_suggestion/` or `docs/proof_suggestion/` directory exists at this checkout snapshot. The source strategies are therefore adopted or adapted directly, subject to the contracts below. Source prose is not treated as proof.

| Historical Phase A input snapshot | SHA-256 |
| --- | --- |
| `notes/md/ch06_lattice_AQFT_net.md` | `2fc657d30296f423f1b4901442f9696053a445f5c2e5cc394bd7aea10c96ed39` |
| `notes/appendices/a02_car_hilbert_and_normal_ordering.md` | `1dfcf6960585d2871bfa92a305d299f94f5880d93775ae0e64d121ec46b55556` |
| `note/proof_suggestions_revision_2026-10-09.md` | `1db5f28b3e392d3b400ccc219ac640778fc5ceabc5cba17dfeb44b225a1b383c` |
| `note/notes_review_completion_2026-10-09.md` | `ee96609b0c32346be604041a99e3345c3420b71c830c88ef83ff8d93bd9c1dc1` |
| `BosonizeStubs/Ch05Fermions.lean` | `4433a21d4e418c9c745b213317e736425ccea1febbab527c34f429060d772446` |
| `Bosonize/Core/A02CARHilbert.lean` | `a683eaba06548c89167592302dc2e6b7f558a53e3acf50c5ff1cceffaeff16e3` |
| `Bosonize/Core/Ch04CARFock.lean` | `8be8dacb9212e7535e1fa7357398bb5b6a7cae6188d6d8643be6548d0ec422e0` |

The historical CH05 hash records the parallel Phase A draft used for elaboration. Both CH05 and CH06 interfaces were subsequently approved and locked at `34150a5` for the authorized Phase B work. CH06 depends on CH05 position operators, inverse Fourier, CAR, adjoints, and parity; the final audit must use freshly built CH05 proofs. Parallel Phase A elaboration alone was not proof evidence.

## Carriers and complete definitions

The carrier is exactly `Ch05.FockSpace L = A02.FockSpace (Ch01.Band L)`, with its existing Euclidean occupation basis. Operators are `Module.End ℂ` on this carrier. Regions are arbitrary `Set (Ch01.Lattice L)`; `[NeZero L]` guarantees a finite positive lattice for all position/local contracts. Nineteen purely momentum/parity/projection/matrix-unit contracts explicitly omit the unnecessary section instance before freezing; their complete definitions already work at every natural L. No positive-even assumption is needed for these net contracts. There are no energy budgets, sea shifts, infinite limits, extra physical AQFT axioms, or polynomial/Wick carriers in this module.

`localGenerators` contains both position annihilators and position creators in the region. `localAlgebra` is their genuine unital `Algebra.adjoin ℂ`. Actual `star` is provided by the installed finite-dimensional linear-map instance, whose `LinearMap.star_eq_adjoint` identifies it with `LinearMap.adjoint`. Star closure is an obligation, not an implicit extra assumption. Empty-region bottom means scalar multiples of the identity, not the zero algebra.

`parityOperator` uses the frozen momentum occupation parity of CH04. `parityMap` is a complete linear conjugation map built by composing installed `LinearMap.mulLeft` and `LinearMap.mulRight`. Its involution, multiplicativity, star compatibility, and ambient/local algebra automorphism upgrades are all lemma stubs. No definition fills an automorphism field with an unproved theorem.

The degree type is `Fin 2`, with sign `(-1 : ℂ)^σ.val`. `localPart I σ` intersects the local algebra's underlying submodule with `ker (parityMap - degreeSign σ • id)`. `evenPart` and `oddPart` are complete submodules; even and odd projections are `(id ± parityMap)/2`. The existence of a `Subalgebra` having the even submodule as its underlying module is an explicit target. An odd unital subalgebra is rejected: odd times odd is even. The nonempty-region proper-even statement has a proposed nonzero odd annihilator witness; the empty region has separate even-equals-full and odd-zero contracts.

Letters are pairs `(position, Bool)`, where `true` is a creator. `wordOperator` uses `List.prod`, so the rightmost factor acts first. `supportedWord` checks every letter position belongs to the specified region. `homogeneousWordSpan` is the span of supported words whose length modulo 2 equals the degree. An empty word represents the identity and belongs only to the even degree. This construction keeps arbitrary homogeneous sums available for locality; ordinary adjoin induction alone would lose that invariant.

## Ordered momentum matrix units and signs

Global fullness is based on the original **momentum** occupation basis. The module first asks that inverse Fourier recover every momentum annihilator and creator inside the position-generated global algebra. Position labels are never substituted for momentum occupation labels without that bridge.

`creatorWord S` is the **descending written product** of momentum creators; its ascending sequence of actions on the vacuum accumulates preceding counts `0,1,…,|S|−1`. Therefore `creatorSign S = (-1)^(|S|(|S|−1)/2)`. The annihilator word is the ascending written product, exactly the adjoint of the creator word. For two ordered occupied modes, descending creators have coefficient `−1`; ascending written creators instead have coefficient `+1`. A draft order/sign mismatch was corrected during Phase A review, before delivery. No constant-sign guess or commutative endomorphism product was adopted.

The vacuum projector is the fixed ascending ordered product of `1 - Ch04.number k` over every momentum mode. Its basis action, idempotence, and global membership remain unproved obligations.

`matrixUnit S T` is independently defined by genuine basis extension, sending ket `T` to ket `S` and all other basis vectors to zero. `orderedMatrixUnit S T` is the sign-corrected creator/projector/annihilator product. The correction multiplies by `creatorSign S * creatorSign T`; both signs square to one, so no unproved nonzero denominator is hidden. The equality between these two complete constructions is a theorem target. The expansion of an arbitrary operator uses its actual occupation coordinates, providing a direct span route to global fullness without guessing a dimension equality.

## Proposed lemma inventory and dependency order

All exact signatures appear in the source snapshot below. The 54 unproved contracts are grouped here to make their obligations reviewable.

| Group | Lemmas | Planned dependencies and unresolved obligations |
| --- | --- | --- |
| Local generation | `annihilation_mem_local`, `creation_mem_local`, `local_algebra_mono`, `local_algebra_union`, `local_algebra_empty`, `local_algebra_empty_scalar`, `local_algebra_star_closed`, `operator_star_eq_adjoint` | Installed adjoin Galois connection, scalar-image bottom, CH05 actual adjoints, and reversed-product star induction. |
| Parity action | `parity_map_apply`, `parity_map_involutive`, `parity_map_mul`, `parity_map_one`, `parity_map_star`, `parity_automorphism_exists`, `parity_annihilation`, `parity_creation`, `parity_preserves_local`, `local_parity_automorphism_exists` | CH04 parity square/adjoint; CH05 generator anticommutation with parity; local induction and restricted bijectivity. |
| Grading | `mem_local_part`, `even_subalgebra_exists`, `local_grading_sup`, `local_grading_disjoint`, `even_projection_mem`, `odd_projection_mem`, `projection_decomposition`, `even_projection_idempotent`, `odd_projection_idempotent`, `mixed_projections_zero`, `graded_mul`, `graded_star`, `even_part_empty`, `odd_part_empty` | Linear eigenspace identities, division by two over ℂ, involution, multiplication/star preservation. Establish the even algebra structure; never call the odd submodule an algebra. |
| Non-vacuity | `annihilation_nonzero`, `local_even_proper`, `local_odd_witness` | Position mixed CAR or adjoint/nonzero creation evidence from CH05; show the proposed witness is both odd and nonzero. |
| Words and locality | `word_mem_local`, `word_homogeneous`, `local_part_eq_word_span`, `disjoint_word_swap`, `twisted_locality`, `even_locality` | First identify the entire adjoin with word spans; use parity projections to extract homogeneous spans. Distinct generators from disjoint supports anticommute by all CH05 CAR cases; swap words with exact length-product sign, then extend bilinearly. |
| Global fullness | `momentum_annihilation_mem_global`, `momentum_creation_mem_global`, `creator_sign_square`, `creator_word_vacuum`, `annihilator_word_adjoint`, `vacuum_projector_ket`, `vacuum_projector_idempotent`, `vacuum_projector_mem_global`, `matrix_unit_ket`, `ordered_matrix_unit_eq`, `matrix_unit_mem_global`, `matrix_unit_expansion`, `global_algebra_eq_top` | Inverse Fourier before momentum generators; CH04 basis action and sorted products; exact CAR signs; Euclidean basis coordinates and finite double sums. |

Disjointness is the exact locality hypothesis; there are no budget margins or hidden AQFT assumptions. Full global CAR algebra is a target, not a property assumed by a structure. The local net is not replaced by `⊤`, and its even/odd objects are not defined as trivial zero spaces to force statements.

## Historical Phase A validation evidence — 2026-10-09

- `lake build BosonizeStubs.Ch06LocalNet` completed successfully against the parallel CH05 draft. The CH06 source has exactly **54 expected `sorry` warnings**, with no errors or linter warnings.
- Native Lean MCP `lean_diagnostic_messages` on the final source completed with `success: true`, `partial: false`, and exactly 54 diagnostics, all category `sorry`. This establishes diagnostic/LSP access and source elaboration, not proof completion.
- Fresh `#print axioms` on **all 26 complete definitions/abbreviations** reports only subsets of `propext`, `Classical.choice`, and `Quot.sound`; **none depends on `sorryAx`**. The complete audit output is preserved below; the transient command log was `/tmp/ch06-definition-audit.log`.
- Fresh `#print axioms` on all **54 lemma stubs** reports `sorryAx` in each, as expected for Phase A. Recorded output: `/tmp/ch06-stub-audit.log`. Those declarations are proposed contracts, not proved results.
- Joint parent validation passed both library builds and all 69 guard tests. Non-strict interface verification preserved all 182 approved statements and 152 commands, and the Core guard preserved all six existing source hashes. Strict verification rejected exactly the two new unreviewed CH05/CH06 files, as required in Phase A.
- No lock manifest, Core source, server configuration, source note, or unrelated deleted documentation was changed by this chapter drafting task. The parent task records combined aggregator, guard, and Git evidence separately.
- The Phase A mirror was exact at its recorded checkpoint. The current block below now contains the Phase B proof bodies, with its current hash recorded below.

### Complete definition/abbreviation axiom audit

```text
'Bosonize.Ch06.FockSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.Operators' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.Region' does not depend on any axioms
'Bosonize.Ch06.Occupation' depends on axioms: [propext, Quot.sound]
'Bosonize.Ch06.Degree' does not depend on any axioms
'Bosonize.Ch06.Letter' does not depend on any axioms
'Bosonize.Ch06.localGenerators' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.localAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parityOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parityMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.degreeSign' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.localPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.evenPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.oddPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.evenProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.oddProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.letterOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.wordOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.supportedWord' does not depend on any axioms
'Bosonize.Ch06.homogeneousWordSpan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.creatorWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.annihilatorWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.creatorSign' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.vacuumProjector' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.matrixUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.orderedMatrixUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Phase B implementation and validation — 2026-10-09

The user approved Phase B for both CH05 and CH06. All 54 CH06 lemma bodies are complete; definitions, imports, scoped `omit` prefixes, theorem headers, namespaces, and lock records remain exactly as approved at `34150a5`. The locked source module comment still describes its historical Phase A draft; it was preserved as a frozen non-lemma command.

The homogeneous-span proof first uses `Algebra.adjoin_eq_span` and `Submonoid.closure_induction` to construct supported word witnesses. A genuine linear parity projection extracts each fixed degree. Word swapping then proves the exact length-product sign from all four disjoint CAR generator cases and extends bilinearly to homogeneous spans. This supplies actual locality rather than treating partial adjoin sums as homogeneous.

Global fullness first recovers momentum generators through the proved CH05 inverse Fourier expressions. A descending-word induction computes creator action with the triangular sign using `Nat.choose_succ_succ`; the annihilator word is its actual Hilbert adjoint. The projector basis action gives the vacuum rank-one map. Its action on the adjoint annihilator string then supplies the exact sign-corrected matrix-unit identity, and the actual occupation-coordinate expansion spans every endomorphism. The nonzero annihilator and proper-even witnesses are proved without assuming those operators exist by an axiom.

Finite occupation kernels required explicit conversion between the inferred subtype `DecidableEq` and the ordered-mode instance used by the frozen CH04 basis laws. Basis unfolding plus finite-set extensionality closed those transports; no carrier, basis, operator, or frozen Core definition was changed.

- Fresh `lake env lean -DwarningAsError=true BosonizeStubs/Ch06LocalNet.lean` exited 0 with empty output: zero compiler/linter warnings and zero proof placeholders.
- Final native MCP diagnostics completed with `success: true`, `partial: false`, and `items: []` for CH06.
- Strict interface verification against committed `34150a5` passed all 271 statements and 225 frozen commands after the proof edits.
- Joint CI passed all 69 guard tests, strict verification of 271 statements and 225 commands against `34150a5`, the six-source Core guard, and both library builds.
- The fresh combined audit `/tmp/ch0506b-axioms.log` inspected 131 declarations: all 89 CH05/CH06 lemmas and all 42 complete data declarations. Only subsets of `propext`, `Classical.choice`, and `Quot.sound` occur; four data declarations need no axioms. No declaration depends on `sorryAx`. This includes all 54 CH06 lemmas and its 26 data declarations after freshly building the completed CH05 dependency.
- Current exact source SHA-256: `47300577a84b8895760d32da1ca8fd25696850360bf393e3cc529aac9464f367`.

The complete fresh CH06 axiom audit is preserved here:

```text
'Bosonize.Ch06.FockSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.Operators' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.Region' does not depend on any axioms
'Bosonize.Ch06.Occupation' depends on axioms: [propext, Quot.sound]
'Bosonize.Ch06.Degree' does not depend on any axioms
'Bosonize.Ch06.Letter' does not depend on any axioms
'Bosonize.Ch06.localGenerators' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.localAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parityOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parityMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.degreeSign' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.localPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.evenPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.oddPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.evenProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.oddProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.letterOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.wordOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.supportedWord' does not depend on any axioms
'Bosonize.Ch06.homogeneousWordSpan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.creatorWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.annihilatorWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.creatorSign' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.vacuumProjector' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.matrixUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.orderedMatrixUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.annihilation_mem_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.creation_mem_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.local_algebra_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.local_algebra_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.local_algebra_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.local_algebra_empty_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.local_algebra_star_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.operator_star_eq_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parity_map_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parity_map_involutive' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parity_map_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parity_map_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parity_map_star' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parity_automorphism_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parity_annihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parity_creation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.parity_preserves_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.local_parity_automorphism_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.mem_local_part' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.even_subalgebra_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.local_grading_sup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.local_grading_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.even_projection_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.odd_projection_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.projection_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.even_projection_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.odd_projection_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.mixed_projections_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.graded_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.graded_star' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.even_part_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.odd_part_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.annihilation_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.local_even_proper' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.local_odd_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.word_mem_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.word_homogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.local_part_eq_word_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.disjoint_word_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.twisted_locality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.even_locality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.momentum_annihilation_mem_global' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.momentum_creation_mem_global' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.creator_sign_square' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.creator_word_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.annihilator_word_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.vacuum_projector_ket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.vacuum_projector_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.vacuum_projector_mem_global' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.matrix_unit_ket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.ordered_matrix_unit_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.matrix_unit_mem_global' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.matrix_unit_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch06.global_algebra_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Phase C promotion and complete-source freezing remain separately authorized steps.

## Exact Lean source snapshot

```lean
module

public import BosonizeStubs.Ch05Fermions
public import Bosonize.Core.Ch04CARFock
public import Mathlib.Algebra.Algebra.Operations

/-!
# CH06: finite local CAR net
Phase A review draft: complete data and one-sorry theorem contracts.
The grading is constructed linearly; no definition uses an unproved contract.
-/

@[expose] public section

namespace Bosonize.Ch06

open scoped BigOperators

abbrev FockSpace (L : ℕ) := Ch05.FockSpace L
abbrev Operators (L : ℕ) := Ch05.Operators L
abbrev Region (L : ℕ) := Set (Ch01.Lattice L)
abbrev Occupation (L : ℕ) := A02.Occupation (Ch01.Band L)
abbrev Degree := Fin 2
abbrev Letter (L : ℕ) := Ch01.Lattice L × Bool

variable (L : ℕ) [NeZero L]

/-- Both annihilation and creation are included before star closure is proved. -/
def localGenerators (I : Region L) : Set (Operators L) :=
  {A | ∃ x ∈ I, A = Ch05.positionAnnihilation L x ∨ A = Ch05.positionCreation L x}

noncomputable def localAlgebra (I : Region L) : Subalgebra ℂ (Operators L) :=
  Algebra.adjoin ℂ (localGenerators L I)

noncomputable def parityOperator : Operators L := Ch04.parity (ι := Ch01.Band L)

/-- Multiplication is composition, with the rightmost factor acting first. -/
noncomputable def parityMap : Operators L →ₗ[ℂ] Operators L :=
  (LinearMap.mulRight ℂ (parityOperator L)).comp (LinearMap.mulLeft ℂ (parityOperator L))

def degreeSign (σ : Degree) : ℂ := (-1 : ℂ) ^ σ.val

/-- Concrete eigenspaces; intersection keeps local membership explicit. -/
noncomputable def localPart (I : Region L) (σ : Degree) : Submodule ℂ (Operators L) :=
  (localAlgebra L I).toSubmodule ⊓
    LinearMap.ker (parityMap L - degreeSign σ • LinearMap.id)

noncomputable abbrev evenPart (I : Region L) : Submodule ℂ (Operators L) :=
  localPart L I 0

noncomputable abbrev oddPart (I : Region L) : Submodule ℂ (Operators L) :=
  localPart L I 1

noncomputable def evenProjection : Operators L →ₗ[ℂ] Operators L :=
  (2 : ℂ)⁻¹ • (LinearMap.id + parityMap L)

noncomputable def oddProjection : Operators L →ₗ[ℂ] Operators L :=
  (2 : ℂ)⁻¹ • (LinearMap.id - parityMap L)

/-- `true` denotes a creator and `false` an annihilator. -/
noncomputable def letterOperator (a : Letter L) : Operators L :=
  if a.2 then Ch05.positionCreation L a.1 else Ch05.positionAnnihilation L a.1

noncomputable def wordOperator (w : List (Letter L)) : Operators L :=
  (w.map (letterOperator L)).prod

def supportedWord (I : Region L) (w : List (Letter L)) : Prop :=
  ∀ a ∈ w, a.1 ∈ I

noncomputable def homogeneousWordSpan (I : Region L) (σ : Degree) :
    Submodule ℂ (Operators L) :=
  Submodule.span ℂ {A | ∃ w : List (Letter L), supportedWord L I w ∧
    w.length % 2 = σ.val ∧ A = wordOperator L w}

/-- Ordered products use the momentum occupation order, not spatial labels. -/
noncomputable def creatorWord (S : Occupation L) : Operators L :=
  (((S.sort (· ≤ ·)).reverse).map (Ch05.momentumCreation L)).prod

noncomputable def annihilatorWord (S : Occupation L) : Operators L :=
  ((S.sort (· ≤ ·)).map (Ch05.momentumAnnihilation L)).prod

/-- Descending creators act in ascending order, accumulating the triangular sign. -/
def creatorSign (S : Occupation L) : ℂ :=
  (-1 : ℂ) ^ (S.card * (S.card - 1) / 2)

noncomputable def vacuumProjector : Operators L :=
  (((Finset.univ : Finset (Ch01.Band L)).sort (· ≤ ·)).map
    (fun k => 1 - Ch04.number k)).prod

noncomputable def matrixUnit (S T : Occupation L) : Operators L :=
  A02.extendBasis fun U => if U = T then A02.ket S else 0

noncomputable def orderedMatrixUnit (S T : Occupation L) : Operators L :=
  (creatorSign L S * creatorSign L T) •
    (creatorWord L S * vacuumProjector L * annihilatorWord L T)

lemma annihilation_mem_local (I : Region L) (x : Ch01.Lattice L) (hx : x ∈ I) :
    Ch05.positionAnnihilation L x ∈ localAlgebra L I := by
  exact Algebra.subset_adjoin ⟨x, hx, Or.inl rfl⟩

lemma creation_mem_local (I : Region L) (x : Ch01.Lattice L) (hx : x ∈ I) :
    Ch05.positionCreation L x ∈ localAlgebra L I := by
  exact Algebra.subset_adjoin ⟨x, hx, Or.inr rfl⟩

lemma local_algebra_mono (I J : Region L) (hIJ : I ⊆ J) :
    localAlgebra L I ≤ localAlgebra L J := by
  apply Algebra.adjoin_mono
  rintro A ⟨x, hx, hA⟩
  exact ⟨x, hIJ hx, hA⟩

lemma local_algebra_union (I J : Region L) :
    localAlgebra L (I ∪ J) = localAlgebra L I ⊔ localAlgebra L J := by
  unfold localAlgebra
  rw [← Algebra.adjoin_union]
  congr 1
  ext A
  simp only [localGenerators, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨x, hx | hx, hA⟩
    · exact Or.inl ⟨x, hx, hA⟩
    · exact Or.inr ⟨x, hx, hA⟩
  · rintro (⟨x, hx, hA⟩ | ⟨x, hx, hA⟩)
    · exact ⟨x, Or.inl hx, hA⟩
    · exact ⟨x, Or.inr hx, hA⟩

lemma local_algebra_empty : localAlgebra L ∅ = ⊥ := by
  have he : localGenerators L ∅ = ∅ := by ext A; simp [localGenerators]
  rw [localAlgebra, he, Algebra.adjoin_empty]

lemma local_algebra_empty_scalar (A : Operators L) :
    A ∈ localAlgebra L ∅ ↔ ∃ z : ℂ, A = z • (1 : Operators L) := by
  rw [local_algebra_empty, Algebra.mem_bot]
  simp only [Set.mem_range, Algebra.algebraMap_eq_smul_one]
  exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩

lemma local_algebra_star_closed (I : Region L) (A : Operators L)
    (hA : A ∈ localAlgebra L I) : star A ∈ localAlgebra L I := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hA
  · rintro A ⟨x, hx, rfl | rfl⟩
    · rw [LinearMap.star_eq_adjoint, ← Ch05.position_creation_eq_adjoint]; exact creation_mem_local L I x hx
    · rw [LinearMap.star_eq_adjoint, ← Ch05.position_annihilation_eq_adjoint]; exact annihilation_mem_local L I x hx
  · intro z
    rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one]
    exact (localAlgebra L I).smul_mem (localAlgebra L I).one_mem _
  · intro A B _ _ hA hB
    rw [star_add]; exact (localAlgebra L I).add_mem hA hB
  · intro A B _ _ hA hB
    rw [star_mul]; exact (localAlgebra L I).mul_mem hB hA

omit [NeZero L] in
lemma operator_star_eq_adjoint (A : Operators L) :
    star A = LinearMap.adjoint A := by
  exact LinearMap.star_eq_adjoint A

omit [NeZero L] in
lemma parity_map_apply (A : Operators L) :
    parityMap L A = parityOperator L * A * parityOperator L := by
  rfl

omit [NeZero L] in
lemma parity_map_involutive (A : Operators L) :
    parityMap L (parityMap L A) = A := by
  have hp : parityOperator L * parityOperator L = 1 := Ch04.parity_square
  simp only [parity_map_apply]
  calc
    parityOperator L * (parityOperator L * A * parityOperator L) * parityOperator L = (parityOperator L * parityOperator L) * A * (parityOperator L * parityOperator L) := by noncomm_ring
    _ = A := by rw [hp]; simp

omit [NeZero L] in
lemma parity_map_mul (A B : Operators L) :
    parityMap L (A * B) = parityMap L A * parityMap L B := by
  have hp : parityOperator L * parityOperator L = 1 := Ch04.parity_square
  simp only [parity_map_apply]
  calc
    parityOperator L * (A * B) * parityOperator L = parityOperator L * A * (parityOperator L * parityOperator L) * B * parityOperator L := by rw [hp]; noncomm_ring
    _ = (parityOperator L * A * parityOperator L) * (parityOperator L * B * parityOperator L) := by noncomm_ring

omit [NeZero L] in
lemma parity_map_one : parityMap L 1 = 1 := by
  simpa [parity_map_apply, parityOperator] using (Ch04.parity_square (ι := Ch01.Band L))

omit [NeZero L] in
lemma parity_map_star (A : Operators L) :
    parityMap L (star A) = star (parityMap L A) := by
  have hp : star (parityOperator L) = parityOperator L := by rw [operator_star_eq_adjoint]; exact Ch04.parity_adjoint
  simp only [parity_map_apply, star_mul, hp]
  noncomm_ring

omit [NeZero L] in
/-- Automorphism structure is an obligation, not an assumed definition field. -/
lemma parity_automorphism_exists : ∃ α : Operators L ≃ₐ[ℂ] Operators L,
    (∀ A, α A = parityMap L A) ∧ ∀ A, α (star A) = star (α A) := by
  let α := AlgEquiv.ofLinearEquiv (LinearEquiv.ofInvolutive (parityMap L) (parity_map_involutive L)) (parity_map_one L) (parity_map_mul L)
  exact ⟨α, fun _ => rfl, parity_map_star L⟩

lemma parity_annihilation (x : Ch01.Lattice L) :
    parityMap L (Ch05.positionAnnihilation L x) = -Ch05.positionAnnihilation L x := by
  rw [parity_map_apply]
  have hp : parityOperator L * parityOperator L = 1 := Ch04.parity_square
  have ha : parityOperator L * Ch05.positionAnnihilation L x = -(Ch05.positionAnnihilation L x * parityOperator L) := Ch05.parity_position_annihilation L x
  rw [ha, neg_mul, mul_assoc, hp, mul_one]

lemma parity_creation (x : Ch01.Lattice L) :
    parityMap L (Ch05.positionCreation L x) = -Ch05.positionCreation L x := by
  rw [parity_map_apply]
  have hp : parityOperator L * parityOperator L = 1 := Ch04.parity_square
  have ha : parityOperator L * Ch05.positionCreation L x = -(Ch05.positionCreation L x * parityOperator L) := Ch05.parity_position_creation L x
  rw [ha, neg_mul, mul_assoc, hp, mul_one]

lemma parity_preserves_local (I : Region L) (A : Operators L)
    (hA : A ∈ localAlgebra L I) : parityMap L A ∈ localAlgebra L I := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hA
  · rintro A ⟨x, hx, rfl | rfl⟩
    · rw [parity_annihilation]; exact (localAlgebra L I).neg_mem (annihilation_mem_local L I x hx)
    · rw [parity_creation]; exact (localAlgebra L I).neg_mem (creation_mem_local L I x hx)
  · intro z
    rw [Algebra.algebraMap_eq_smul_one, map_smul, parity_map_one]
    exact (localAlgebra L I).smul_mem (localAlgebra L I).one_mem _
  · intro A B _ _ hA hB
    rw [map_add]; exact (localAlgebra L I).add_mem hA hB
  · intro A B _ _ hA hB
    rw [parity_map_mul]; exact (localAlgebra L I).mul_mem hA hB

lemma local_parity_automorphism_exists (I : Region L) :
    ∃ α : localAlgebra L I ≃ₐ[ℂ] localAlgebra L I,
      ∀ A, (α A : Operators L) = parityMap L (A : Operators L) := by
  let f : localAlgebra L I →ₗ[ℂ] localAlgebra L I :=
    { toFun := fun A => ⟨parityMap L A, parity_preserves_local L I A A.property⟩
      map_add' := fun A B => Subtype.ext (map_add (parityMap L) (A : Operators L) (B : Operators L))
      map_smul' := fun z A => Subtype.ext (map_smul (parityMap L) z (A : Operators L)) }
  have hi : Function.Involutive f := fun A => Subtype.ext (parity_map_involutive L A)
  let α := AlgEquiv.ofLinearEquiv (LinearEquiv.ofInvolutive f hi)
    (Subtype.ext (parity_map_one L)) (fun A B => Subtype.ext (parity_map_mul L A B))
  exact ⟨α, fun A => rfl⟩

lemma mem_local_part (I : Region L) (σ : Degree) (A : Operators L) :
    A ∈ localPart L I σ ↔ A ∈ localAlgebra L I ∧
      parityMap L A = degreeSign σ • A := by
  simp only [localPart, Submodule.mem_inf, Subalgebra.mem_toSubmodule, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

lemma even_subalgebra_exists (I : Region L) :
    ∃ E : Subalgebra ℂ (Operators L), E.toSubmodule = evenPart L I := by
  refine ⟨{ carrier := evenPart L I
            zero_mem' := (evenPart L I).zero_mem
            add_mem' := fun ha hb => (evenPart L I).add_mem ha hb
            one_mem' := by
              change 1 ∈ localPart L I 0
              rw [mem_local_part]
              exact ⟨(localAlgebra L I).one_mem, by simpa [degreeSign] using parity_map_one L⟩
            mul_mem' := by
              intro A B hA hB
              change A ∈ localPart L I 0 at hA
              change B ∈ localPart L I 0 at hB
              change A * B ∈ localPart L I 0
              rw [mem_local_part] at hA hB ⊢
              simp [degreeSign] at hA hB ⊢
              exact ⟨(localAlgebra L I).mul_mem hA.1 hB.1, by rw [parity_map_mul, hA.2, hB.2]⟩
            algebraMap_mem' := by
              intro z
              change (algebraMap ℂ (Operators L)) z ∈ localPart L I 0
              rw [mem_local_part, Algebra.algebraMap_eq_smul_one]
              exact ⟨(localAlgebra L I).smul_mem (localAlgebra L I).one_mem z, by simp [map_smul, parity_map_one, degreeSign]⟩ }, rfl⟩

lemma local_grading_sup (I : Region L) :
    evenPart L I ⊔ oddPart L I = (localAlgebra L I).toSubmodule := by
  have hE : ∀ A ∈ localAlgebra L I, evenProjection L A ∈ evenPart L I := by
    intro A hA
    rw [mem_local_part]
    constructor
    · exact (localAlgebra L I).smul_mem ((localAlgebra L I).add_mem hA (parity_preserves_local L I A hA)) _
    · simp only [evenProjection, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, map_smul, map_add, parity_map_involutive, degreeSign]
      simp
      module
  have hO : ∀ A ∈ localAlgebra L I, oddProjection L A ∈ oddPart L I := by
    intro A hA
    rw [mem_local_part]
    constructor
    · exact (localAlgebra L I).smul_mem ((localAlgebra L I).sub_mem hA (parity_preserves_local L I A hA)) _
    · simp only [oddProjection, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_sub, parity_map_involutive, degreeSign]
      norm_num
      module
  apply le_antisymm
  · exact sup_le inf_le_left inf_le_left
  · intro A hA
    apply Submodule.mem_sup.mpr
    refine ⟨evenProjection L A, hE A hA, oddProjection L A, hO A hA, ?_⟩
    simp only [evenProjection, oddProjection, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply]
    module

lemma local_grading_disjoint (I : Region L) :
    Disjoint (evenPart L I) (oddPart L I) := by
  rw [Submodule.disjoint_def]
  intro A hA hB
  have ha := (mem_local_part L I 0 A).mp hA
  have hb := (mem_local_part L I 1 A).mp hB
  simp [degreeSign] at ha hb
  have he : A = -A := ha.2.symm.trans hb.2
  have hz := congrArg (fun X : Operators L => (2 : ℂ)⁻¹ • X) (eq_neg_iff_add_eq_zero.mp he)
  simpa [← two_smul ℂ A, smul_smul] using hz

lemma even_projection_mem (I : Region L) (A : Operators L)
    (hA : A ∈ localAlgebra L I) : evenProjection L A ∈ evenPart L I := by
  rw [mem_local_part]
  constructor
  · exact (localAlgebra L I).smul_mem ((localAlgebra L I).add_mem hA (parity_preserves_local L I A hA)) _
  · simp only [evenProjection, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, map_smul, map_add, parity_map_involutive, degreeSign]
    simp
    module

lemma odd_projection_mem (I : Region L) (A : Operators L)
    (hA : A ∈ localAlgebra L I) : oddProjection L A ∈ oddPart L I := by
  rw [mem_local_part]
  constructor
  · exact (localAlgebra L I).smul_mem ((localAlgebra L I).sub_mem hA (parity_preserves_local L I A hA)) _
  · simp only [oddProjection, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_sub, parity_map_involutive, degreeSign]
    norm_num
    module

omit [NeZero L] in
lemma projection_decomposition (A : Operators L) :
    evenProjection L A + oddProjection L A = A := by
  simp only [evenProjection, oddProjection, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply]
  module

omit [NeZero L] in
lemma even_projection_idempotent (A : Operators L) :
    evenProjection L (evenProjection L A) = evenProjection L A := by
  simp only [evenProjection, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, map_smul, map_add, parity_map_involutive]
  module

omit [NeZero L] in
lemma odd_projection_idempotent (A : Operators L) :
    oddProjection L (oddProjection L A) = oddProjection L A := by
  simp only [oddProjection, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_sub, parity_map_involutive]
  module

omit [NeZero L] in
lemma mixed_projections_zero (A : Operators L) :
    evenProjection L (oddProjection L A) = 0 ∧ oddProjection L (evenProjection L A) = 0 := by
  simp only [evenProjection, oddProjection, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_add, map_sub, parity_map_involutive]
  constructor <;> module

lemma graded_mul (I : Region L) (σ τ : Degree) (A B : Operators L)
    (hA : A ∈ localPart L I σ) (hB : B ∈ localPart L I τ) :
    A * B ∈ localPart L I (σ + τ) := by
  rw [mem_local_part] at hA hB ⊢
  refine ⟨(localAlgebra L I).mul_mem hA.1 hB.1, ?_⟩
  rw [parity_map_mul, hA.2, hB.2, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  fin_cases σ <;> fin_cases τ <;> norm_num [degreeSign]

lemma graded_star (I : Region L) (σ : Degree) (A : Operators L)
    (hA : A ∈ localPart L I σ) : star A ∈ localPart L I σ := by
  rw [mem_local_part] at hA ⊢
  refine ⟨local_algebra_star_closed L I A hA.1, ?_⟩
  rw [parity_map_star, hA.2, star_smul]
  congr 1
  simp [degreeSign]

lemma even_part_empty : evenPart L ∅ = (localAlgebra L ∅).toSubmodule := by
  apply le_antisymm inf_le_left
  intro A hA
  change A ∈ localPart L ∅ 0
  rw [mem_local_part]
  refine ⟨hA, ?_⟩
  obtain ⟨z, rfl⟩ := (local_algebra_empty_scalar L A).mp hA
  simp [map_smul, parity_map_one, degreeSign]

lemma odd_part_empty : oddPart L ∅ = ⊥ := by
  apply eq_bot_iff.mpr
  intro A hA
  have ha := (mem_local_part L ∅ 1 A).mp hA
  have hE : A ∈ evenPart L ∅ := (even_part_empty L).symm ▸ ha.1
  have he := (mem_local_part L ∅ 0 A).mp hE
  simp [degreeSign] at ha he
  have hz := congrArg (fun X : Operators L => (2 : ℂ)⁻¹ • X) (eq_neg_iff_add_eq_zero.mp (he.2.symm.trans ha.2))
  simpa [← two_smul ℂ A, smul_smul] using hz

lemma annihilation_nonzero (x : Ch01.Lattice L) :
    Ch05.positionAnnihilation L x ≠ 0 := by
  intro h
  have hc := Ch05.position_mixed_car L x x
  simp [h, A02.anticommutator] at hc

lemma local_even_proper (I : Region L) (hI : I.Nonempty) :
    evenPart L I < (localAlgebra L I).toSubmodule := by
  apply lt_of_le_of_ne inf_le_left
  intro he
  obtain ⟨x, hx⟩ := hI
  have hA : Ch05.positionAnnihilation L x ∈ evenPart L I := by
    change Ch05.positionAnnihilation L x ∈ (localAlgebra L I).toSubmodule ⊓ LinearMap.ker (parityMap L - degreeSign 0 • LinearMap.id)
    rw [he]
    exact annihilation_mem_local L I x hx
  have hp := (mem_local_part L I 0 _).mp hA
  simp [degreeSign] at hp
  have hz := congrArg (fun X : Operators L => (2 : ℂ)⁻¹ • X) (eq_neg_iff_add_eq_zero.mp ((parity_annihilation L x).symm.trans hp.2).symm)
  have h0 : Ch05.positionAnnihilation L x = 0 := by simpa [← two_smul ℂ (Ch05.positionAnnihilation L x), smul_smul] using hz
  exact annihilation_nonzero L x h0

lemma local_odd_witness (I : Region L) (x : Ch01.Lattice L) (hx : x ∈ I) :
    Ch05.positionAnnihilation L x ∈ oddPart L I ∧
      Ch05.positionAnnihilation L x ≠ 0 := by
  refine ⟨?_, annihilation_nonzero L x⟩
  rw [mem_local_part]
  exact ⟨annihilation_mem_local L I x hx, by simpa [degreeSign] using parity_annihilation L x⟩

lemma word_mem_local (I : Region L) (w : List (Letter L))
    (hw : supportedWord L I w) : wordOperator L w ∈ localAlgebra L I := by
  unfold wordOperator
  apply Subalgebra.list_prod_mem
  intro A hA
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  have hx := hw a ha
  cases h : a.2
  · simpa [letterOperator, h] using annihilation_mem_local L I a.1 hx
  · simpa [letterOperator, h] using creation_mem_local L I a.1 hx

lemma word_homogeneous (w : List (Letter L)) :
    parityMap L (wordOperator L w) = (-1 : ℂ) ^ w.length • wordOperator L w := by
  induction w with
  | nil => simp [wordOperator, parity_map_one]
  | cons a w ih =>
    have ha : parityMap L (letterOperator L a) = -letterOperator L a := by
      cases h : a.2
      · simpa [letterOperator, h] using parity_annihilation L a.1
      · simpa [letterOperator, h] using parity_creation L a.1
    simp only [wordOperator, List.map_cons, List.prod_cons] at ih ⊢
    rw [parity_map_mul, ha, ih]
    simp [pow_succ, neg_smul, smul_neg]

/-- This contract supplies homogeneous sums; ordinary adjoin induction alone does not. -/
lemma local_part_eq_word_span (I : Region L) (σ : Degree) :
    localPart L I σ = homogeneousWordSpan L I σ := by
  classical
  let W : Set (Operators L) := {A | ∃ w : List (Letter L), supportedWord L I w ∧ A = wordOperator L w}
  have hcl : (Submonoid.closure (localGenerators L I) : Set (Operators L)) ⊆ W := by
    intro A hA
    refine Submonoid.closure_induction ?_ ?_ ?_ hA
    · rintro A ⟨x, hx, rfl | rfl⟩
      · exact ⟨[(x, false)], by simpa [supportedWord] using hx, by simp [wordOperator, letterOperator]⟩
      · exact ⟨[(x, true)], by simpa [supportedWord] using hx, by simp [wordOperator, letterOperator]⟩
    · exact ⟨[], by simp [supportedWord], by simp [wordOperator]⟩
    · intro A B _ _ hA hB
      obtain ⟨u, hu, rfl⟩ := hA
      obtain ⟨v, hv, rfl⟩ := hB
      refine ⟨u ++ v, ?_, ?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hu a ha
        · exact hv a ha
      · simp [wordOperator, List.map_append, List.prod_append]
  have htotal : (localAlgebra L I).toSubmodule ≤ Submodule.span ℂ W := by
    unfold localAlgebra
    rw [Algebra.adjoin_eq_span]
    exact Submodule.span_mono hcl
  let p : Operators L →ₗ[ℂ] Operators L := (2 : ℂ)⁻¹ • (LinearMap.id + degreeSign σ • parityMap L)
  have hpw : ∀ w : List (Letter L), p (wordOperator L w) = if w.length % 2 = σ.val then wordOperator L w else 0 := by
    intro w
    simp only [p, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, word_homogeneous]
    rw [neg_one_pow_eq_pow_mod_two]
    have hm : w.length % 2 = 0 ∨ w.length % 2 = 1 := by omega
    rcases hm with hm | hm <;> fin_cases σ <;> simp [hm, degreeSign] <;> module
  apply le_antisymm
  · intro A hA
    have ha := (mem_local_part L I σ A).mp hA
    have hpA : p A = A := by
      simp only [p, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, ha.2]
      fin_cases σ <;> norm_num [degreeSign] <;> module
    rw [← hpA]
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (htotal ha.1)
    · rintro B ⟨w, hw, rfl⟩
      rw [hpw]
      split_ifs with h
      · exact Submodule.subset_span ⟨w, hw, h, rfl⟩
      · exact Submodule.zero_mem _
    · simp
    · intro B C _ _ hB hC
      rw [map_add]; exact Submodule.add_mem _ hB hC
    · intro z B _ hB
      rw [map_smul]; exact Submodule.smul_mem _ z hB
  · apply Submodule.span_le.mpr
    rintro A ⟨w, hw, hσ, rfl⟩
    change wordOperator L w ∈ localPart L I σ
    rw [mem_local_part]
    refine ⟨word_mem_local L I w hw, ?_⟩
    rw [word_homogeneous, neg_one_pow_eq_pow_mod_two, hσ]
    rfl

lemma disjoint_word_swap (I J : Region L) (hIJ : Disjoint I J)
    (u v : List (Letter L)) (hu : supportedWord L I u) (hv : supportedWord L J v) :
    wordOperator L u * wordOperator L v =
      (-1 : ℂ) ^ (u.length * v.length) • (wordOperator L v * wordOperator L u) := by
  have hs : ∀ a b : Letter L, a.1 ∈ I → b.1 ∈ J → letterOperator L a * letterOperator L b = -(letterOperator L b * letterOperator L a) := by
    intro a b ha hb
    have hn : a.1 ≠ b.1 := by intro h; exact Set.disjoint_left.mp hIJ ha (h ▸ hb)
    have hc : letterOperator L a * letterOperator L b + letterOperator L b * letterOperator L a = 0 := by
      cases ha' : a.2 <;> cases hb' : b.2
      · simpa [letterOperator, ha', hb', A02.anticommutator] using Ch05.position_annihilation_car L a.1 b.1
      · simpa [letterOperator, ha', hb', A02.anticommutator, hn] using Ch05.position_mixed_car L a.1 b.1
      · simpa [letterOperator, ha', hb', A02.anticommutator, Ne.symm hn, add_comm] using Ch05.position_mixed_car L b.1 a.1
      · simpa [letterOperator, ha', hb', A02.anticommutator] using Ch05.position_creation_car L a.1 b.1
    exact eq_neg_of_add_eq_zero_left hc
  have hsingle : ∀ a : Letter L, a.1 ∈ I → ∀ v : List (Letter L), supportedWord L J v → letterOperator L a * wordOperator L v = (-1 : ℂ) ^ v.length • (wordOperator L v * letterOperator L a) := by
    intro a ha v
    induction v with
    | nil => intro _; simp [wordOperator]
    | cons b v ih =>
      intro hv
      have hb := hv b (List.mem_cons_self ..)
      have hvt : supportedWord L J v := fun c hc => hv c (List.mem_cons_of_mem _ hc)
      simp only [wordOperator, List.map_cons, List.prod_cons, List.length_cons]
      calc
        letterOperator L a * (letterOperator L b * wordOperator L v) = (letterOperator L a * letterOperator L b) * wordOperator L v := by rw [mul_assoc]
        _ = -(letterOperator L b * (letterOperator L a * wordOperator L v)) := by rw [hs a b ha hb]; noncomm_ring
        _ = -(letterOperator L b * ((-1 : ℂ) ^ v.length • (wordOperator L v * letterOperator L a))) := by rw [ih hvt]
        _ = (-1 : ℂ) ^ (v.length + 1) • ((letterOperator L b * wordOperator L v) * letterOperator L a) := by simp [pow_succ, mul_assoc, neg_smul]
  induction u with
  | nil => simp [wordOperator]
  | cons a u ih =>
    have ha := hu a (List.mem_cons_self ..)
    have hut : supportedWord L I u := fun c hc => hu c (List.mem_cons_of_mem _ hc)
    have hsw := hsingle a ha v hv
    have hi := ih hut
    simp only [wordOperator, List.map_cons, List.prod_cons, List.length_cons]
    calc
      (letterOperator L a * wordOperator L u) * wordOperator L v = letterOperator L a * (wordOperator L u * wordOperator L v) := by rw [mul_assoc]
      _ = letterOperator L a * ((-1 : ℂ) ^ (u.length * v.length) • (wordOperator L v * wordOperator L u)) := by rw [hi]
      _ = ((-1 : ℂ) ^ (u.length * v.length) * (-1 : ℂ) ^ v.length) • (wordOperator L v * (letterOperator L a * wordOperator L u)) := by rw [mul_smul_comm, ← mul_assoc, hsw, smul_mul_assoc, smul_smul, mul_assoc]
      _ = (-1 : ℂ) ^ ((u.length + 1) * v.length) • (wordOperator L v * (letterOperator L a * wordOperator L u)) := by rw [Nat.add_mul, one_mul, pow_add]

lemma twisted_locality (I J : Region L) (hIJ : Disjoint I J)
    (σ τ : Degree) (A B : Operators L)
    (hA : A ∈ localPart L I σ) (hB : B ∈ localPart L J τ) :
    A * B = (-1 : ℂ) ^ (σ.val * τ.val) • (B * A) := by
  rw [local_part_eq_word_span] at hA hB
  revert B
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro A ⟨u, hu, hσ, rfl⟩ B hB
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hB
    · rintro B ⟨v, hv, hτ, rfl⟩
      rw [disjoint_word_swap L I J hIJ u v hu hv]
      congr 1
      rw [neg_one_pow_eq_pow_mod_two, Nat.mul_mod, hσ, hτ]
      fin_cases σ <;> fin_cases τ <;> norm_num
    · simp
    · intro B C _ _ hB hC
      rw [mul_add, add_mul, smul_add, hB, hC]
    · intro z B _ hB
      simp only [mul_smul_comm, smul_mul_assoc]
      rw [hB, smul_smul, smul_smul, mul_comm]
  · intro B _; simp
  · intro A C _ _ hA hC B hB
    rw [add_mul, mul_add, smul_add, hA B hB, hC B hB]
  · intro z A _ hA B hB
    simp only [smul_mul_assoc, mul_smul_comm]
    rw [hA B hB, smul_smul, smul_smul, mul_comm]

lemma even_locality (I J : Region L) (hIJ : Disjoint I J) (A B : Operators L)
    (hA : A ∈ evenPart L I) (hB : B ∈ evenPart L J) :
    A02.commutator A B = 0 := by
  unfold A02.commutator
  rw [twisted_locality L I J hIJ 0 0 A B hA hB]
  simp

/-- The inverse Fourier bridge is required before momentum-basis matrix units. -/
lemma momentum_annihilation_mem_global (k : Ch01.Band L) :
    Ch05.momentumAnnihilation L k ∈ localAlgebra L Set.univ := by
  rw [Ch05.inverse_annihilation L k]
  apply Subalgebra.smul_mem
  apply Subalgebra.sum_mem
  intro x _
  exact (localAlgebra L Set.univ).smul_mem (annihilation_mem_local L Set.univ x (Set.mem_univ x)) _

lemma momentum_creation_mem_global (k : Ch01.Band L) :
    Ch05.momentumCreation L k ∈ localAlgebra L Set.univ := by
  rw [Ch05.inverse_creation L k]
  apply Subalgebra.smul_mem
  apply Subalgebra.sum_mem
  intro x _
  exact (localAlgebra L Set.univ).smul_mem (creation_mem_local L Set.univ x (Set.mem_univ x)) _

omit [NeZero L] in
lemma creator_sign_square (S : Occupation L) :
    creatorSign L S * creatorSign L S = 1 := by
  unfold creatorSign
  rw [← mul_pow]
  simp

omit [NeZero L] in
lemma creator_word_vacuum (S : Occupation L) :
    creatorWord L S (A02.ket ∅) = creatorSign L S • A02.ket S := by
  classical
  have hc : ∀ (i : Ch01.Band L) (T : Occupation L), Ch05.momentumCreation L i (A02.ket T) = if i ∈ T then 0 else Ch04.fermionSign i T • A02.ket (insert i T) := by
    intro i T
    convert Ch04.creation_ket i T using 1 <;> simp [Ch05.momentumCreation, Ch05.FockSpace, A02.ket, A02.occupationBasis, A02.occupationONB]
    all_goals split_ifs <;> congr 1
    all_goals ext U; simp
    all_goals congr 2; ext j; simp
  have hl : ∀ l : List (Ch01.Band L), l.Pairwise (· > ·) → (l.map (Ch05.momentumCreation L)).prod (A02.ket ∅) = (-1 : ℂ) ^ (l.length.choose 2) • A02.ket l.toFinset := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons i l ih =>
      intro h
      obtain ⟨hi, ht⟩ := List.pairwise_cons.mp h
      have hnot : i ∉ l.toFinset := by
        intro hx
        have hi' := hi i (List.mem_toFinset.mp hx)
        exact lt_irrefl i hi'
      have hn : Ch04.precedingCount i l.toFinset = l.length := by
        unfold Ch04.precedingCount
        rw [Finset.filter_eq_self.mpr (fun j hj => hi j (List.mem_toFinset.mp hj)), List.toFinset_card_of_nodup ht.nodup]
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [ih ht, map_smul, hc]
      simp only [hnot, ite_false, Ch04.fermionSign, hn, smul_smul, List.length_cons, List.toFinset_cons, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
      congr 1
      exact mul_comm _ _
  have hp : (S.sort (· ≤ ·)).reverse.Pairwise (· > ·) := List.pairwise_reverse.mpr S.sortedLT_sort.pairwise
  simpa [creatorWord, creatorSign, Nat.choose_two_right] using hl (S.sort (· ≤ ·)).reverse hp

omit [NeZero L] in
lemma annihilator_word_adjoint (S : Occupation L) :
    annihilatorWord L S = LinearMap.adjoint (creatorWord L S) := by
  have hc : ∀ k : Ch01.Band L, Ch05.momentumAnnihilation L k = star (Ch05.momentumCreation L k) := by
    intro k
    rw [LinearMap.star_eq_adjoint]
    exact Ch04.annihilation_eq_adjoint k
  have hh : ∀ l : List (Ch01.Band L), (l.map (Ch05.momentumAnnihilation L)).prod = star ((l.reverse.map (Ch05.momentumCreation L)).prod) := by
    intro l
    induction l with
    | nil => simp
    | cons k l ih => simp [List.reverse_cons, List.map_append, List.prod_append, star_mul, ih, hc]
  simpa only [creatorWord, annihilatorWord, LinearMap.star_eq_adjoint] using hh (S.sort (· ≤ ·))

omit [NeZero L] in
lemma vacuum_projector_ket (S : Occupation L) :
    vacuumProjector L (A02.ket S) = if S = ∅ then A02.ket ∅ else 0 := by
  classical
  have hn : ∀ i : Ch01.Band L, Ch05.momentumNumber L i (A02.ket S) = (if i ∈ S then (1 : ℂ) else 0) • A02.ket S := by
    intro i
    convert Ch04.number_ket i S using 1 <;> simp [Ch05.momentumNumber, Ch05.momentumCreation, Ch05.momentumAnnihilation, Ch04.number, Ch05.FockSpace, A02.ket, A02.occupationBasis, A02.occupationONB]
  have hl : ∀ l : List (Ch01.Band L), (l.map (fun i => (1 : Operators L) - Ch05.momentumNumber L i)).prod (A02.ket S) = (l.map (fun i => if i ∈ S then (0 : ℂ) else 1)).prod • A02.ket S := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, Module.End.one_apply, hn]
      by_cases hi : i ∈ S
      · simp [hi]
      · simp [hi]
  change (((Finset.univ : Finset (Ch01.Band L)).sort (· ≤ ·)).map (fun i => 1 - Ch05.momentumNumber L i)).prod (A02.ket S) = _
  rw [hl, ← List.prod_toFinset _ (Finset.sort_nodup _ _)]
  simp only [Finset.sort_toFinset]
  by_cases hS : S = ∅
  · subst S; simp
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have hz : (∏ j : Ch01.Band L, if j ∈ S then (0 : ℂ) else 1) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [hz]
    simp [hS]

omit [NeZero L] in
lemma vacuum_projector_idempotent :
    vacuumProjector L * vacuumProjector L = vacuumProjector L := by
  apply A02.end_ext_basis
  intro S
  simp only [Module.End.mul_apply, vacuum_projector_ket]
  by_cases hS : S = ∅
  · subst S; simp [vacuum_projector_ket]
  · simp [hS]

lemma vacuum_projector_mem_global :
    vacuumProjector L ∈ localAlgebra L Set.univ := by
  unfold vacuumProjector
  apply Subalgebra.list_prod_mem
  intro A hA
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hA
  apply (localAlgebra L Set.univ).sub_mem (localAlgebra L Set.univ).one_mem
  exact (localAlgebra L Set.univ).mul_mem (momentum_creation_mem_global L k) (momentum_annihilation_mem_global L k)

omit [NeZero L] in
lemma matrix_unit_ket (S T U : Occupation L) :
    matrixUnit L S T (A02.ket U) = if U = T then A02.ket S else 0 := by
  exact A02.extend_basis_ket _ U

omit [NeZero L] in
lemma ordered_matrix_unit_eq (S T : Occupation L) :
    orderedMatrixUnit L S T = matrixUnit L S T := by
  classical
  have hv : ∀ v : FockSpace L, vacuumProjector L v = inner ℂ (A02.ket (∅ : Occupation L)) v • A02.ket ∅ := by
    intro v
    rw [A02.occupation_expansion v]
    simp [map_sum, map_smul, vacuum_projector_ket, inner_sum, inner_smul_right, A02.ket_inner]
  have hreal : (starRingEnd ℂ) (creatorSign L T) = creatorSign L T := by simp [creatorSign]
  have hsign : (creatorSign L S * creatorSign L T) * (creatorSign L T * creatorSign L S) = 1 := by
    calc
      _ = (creatorSign L S * creatorSign L S) * (creatorSign L T * creatorSign L T) := by ring
      _ = 1 := by rw [creator_sign_square, creator_sign_square]; simp
  apply A02.end_ext_basis
  intro U
  simp only [orderedMatrixUnit, LinearMap.smul_apply, Module.End.mul_apply, matrix_unit_ket]
  rw [hv, annihilator_word_adjoint, LinearMap.adjoint_inner_right, creator_word_vacuum, inner_smul_left, hreal, A02.ket_inner]
  by_cases hU : U = T
  · subst U
    simp only [ite_true, mul_one, map_smul, creator_word_vacuum, smul_smul]
    rw [hsign, one_smul]
  · simp [hU, Ne.symm hU]

lemma matrix_unit_mem_global (S T : Occupation L) :
    matrixUnit L S T ∈ localAlgebra L Set.univ := by
  rw [← ordered_matrix_unit_eq]
  unfold orderedMatrixUnit
  apply Subalgebra.smul_mem
  apply Subalgebra.mul_mem
  · apply Subalgebra.mul_mem
    · unfold creatorWord
      apply Subalgebra.list_prod_mem
      intro A hA
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hA
      exact momentum_creation_mem_global L k
    · exact vacuum_projector_mem_global L
  · unfold annihilatorWord
    apply Subalgebra.list_prod_mem
    intro A hA
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hA
    exact momentum_annihilation_mem_global L k

omit [NeZero L] in
lemma matrix_unit_expansion (A : Operators L) :
    A = ∑ S : Occupation L, ∑ T : Occupation L,
      (A (A02.ket T)) S • matrixUnit L S T := by
  classical
  apply A02.end_ext_basis
  intro U
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, matrix_unit_ket]
  rw [Finset.sum_comm]
  symm
  calc
    (∑ T : Occupation L, ∑ S : Occupation L, (A (A02.ket T)) S • (if U = T then A02.ket S else 0)) = ∑ S : Occupation L, (A (A02.ket U)) S • A02.ket S := by
      rw [Finset.sum_eq_single U]
      · simp only [ite_true]
      · intro T _ hT
        apply Finset.sum_eq_zero
        intro S _
        simp [Ne.symm hT]
      · simp
    _ = A (A02.ket U) := (A02.occupation_expansion _).symm

lemma global_algebra_eq_top : localAlgebra L Set.univ = ⊤ := by
  apply eq_top_iff.mpr
  intro A _
  rw [matrix_unit_expansion L A]
  apply Subalgebra.sum_mem
  intro S _
  apply Subalgebra.sum_mem
  intro T _
  exact (localAlgebra L Set.univ).smul_mem (matrix_unit_mem_global L S T) _

end Bosonize.Ch06
```
