# Chapter 5 position and momentum fermions lab notebook

Status (2026-10-09): **Phase C complete; promoted and frozen in Core.** `Ch05Fermions` contains 35 proved lemmas. The historical Phase B checkpoint is `0abdb37` and its interface baseline is `34150a5`; use the committed Phase C promotion checkpoint for current baseline checks.

## Historical Phase A source reconciliation and review choices

Read [CH05](../../../../notes/md/ch05_fermions_lattice_band.md), [A01](../../../../notes/appendices/a01_fourier_scalars_and_characters.md), [A04](../../../../notes/appendices/a04_density_partitions_and_sugawara.md), [TOC](../../../../notes/md/TOC.md), [source audit](../../../../docs/audit/reference_notes_lean_audit.md) and [proof corrections](../../../../note/proof_suggestions_revision_2026-10-09.md). No CH05-specific suggestion is available: the current checkout has no remaining `docs/stub_suggestion/` or `docs/proof_suggestion/` directories. Inline proof sketches remain advisory. The TOC's claim that only CH01/CH02 are frozen is historical; current Core includes CH01–CH04, A01 and finite-CAR A02. Source notes are unchanged.

Adopt positive annihilation and negative creation character kernels, one real `A01.normalization` scalar cast into ℂ, the canonical primitive root, and the frozen positive-Nyquist band. Reuse A01's character/conjugation/orthogonality proofs rather than reimplementing them. Character negation is ordinary integer negation, so no negative-Nyquist membership is required. `LinearMap.adjoint` is the actual finite-dimensional Hilbert adjoint; its installed signature was verified by native MCP hover.

**Explicit proposed generalization:** the Fourier/CAR layer uses any positive `L` (`[NeZero L]`), since evenness is unnecessary there. This broadens the notes' physical convention and needs review. Half-filled sea cardinality and triangular-energy statements specialize to exactly `L=2*h`, `h>0`; no half-filling assertion is made for odd sizes. Momentum and signed-energy definitions do not require positive size.

## Carrier and definitions

Sixteen complete definitions/abbreviations. `FockSpace L` is exactly `A02.FockSpace (Ch01.Band L)`; `Operators L` is its complex-linear endomorphism algebra. Momentum operators reuse CH04. Position operators are finite sums with `1/sqrt(L)`, using the same occupation carrier. A position occupation basis is not silently identified with the momentum basis.

`occupationEnergy` is an integer sum of signed band labels. `bareHamiltonian` weights momentum numbers; `seaConfiguration` fills all `k.val≤0` in the actual band. `seaEnergy` is its integer sum and `seaKet` its basis ket. `shiftedHamiltonian` subtracts that scalar times identity. The triangular formula is a theorem stub, never an assumption used in a definition; negative energies are not clipped to naturals. At `h=1` the sea energy is zero, so nonzero bare-sea-action witnesses require `h≥2`, separately from the always-nonzero sea ket.

## Proposed obligations and proof order

All 35 lemmas have exactly one `:= by sorry` and remain unproved.

| Group | Obligations and future proof order |
| --- | --- |
| Fourier CAR | Prove adjoints using conjugate kernels, expand all three CAR sums, apply momentum CAR and orthogonality, cancel the single normalization law; only then construct position CAR. |
| Recovery and observables | Both inverse transforms precede total-number invariance; reuse A02 algebraic CAR for number idempotency, adjoints, commutation and number commutators. |
| Witnesses and parity | Empty-occupation annihilation, nonzero position creation and parity oddness use actual CH04 occupation/parity action. Nonzero witness statements are stubs, not established evidence. |
| Signed energies | Basis spectrum, self-adjointness, bare/shifted commutators follow diagonal number action, retaining integer-to-complex casts. |
| Sea | Count/sum `[-h+1,0]` for `h>0`; derive bare/shifted sea action, triangular energy, the `h=1` zero endpoint, and `h≥2` nonzero witness. |

No budgets, density/Sugawara layer, sector-ground proof, normal symbols, analytic limit or thermodynamic construction is implemented. A04 informs conventions and later dependencies only.

## Parallel CH06 interface and attribution

The primary formalizer drafts CH05; one delegated formalizer drafts CH06, both using the repository formalizer skill. CH06 consumes position generators, actual-adjoint, inverse-transform and parity contracts. Its algebra and word definitions can be drafted in parallel; future Phase B must first prove the CH05 contracts used by CH06. Combined elaboration is not proof of either chapter's statements.

## Historical Phase A validation and review boundary

Fresh direct compilation and the module build pass with exactly 35 expected declaration-uses-sorry warnings, no errors or extra linter warnings. Native MCP diagnostics are successful, complete and contain exactly these 35 warnings, with no timeout or failed dependencies. Hover checks the adjoint API. Native search fails because its server PATH lacks `rg`; shell sources and compiler inspection supply retrieval. Diagnostics and hover work, so this is a search-tool limitation.

Fresh axiom inspection verifies all 16 definitions/abbreviations with only standard axioms and no `sorryAx`; all 35 theorem stubs expose `sorryAx`. Definitions consume no unproved chapter lemma. Existing approved interfaces, six Core hashes and manifests remain unchanged. Full strict CI must reject these new unlocked modules until review; do not treat that expected rejection as a compiler failure or lock them prematurely.

Joint validation: both libraries build, all 69 guard regression tests pass, and all six existing Core hashes remain unchanged. Non-strict verification against `3c2cf5a` passes 182 approved statements and 152 commands while naming the two new drafts. Strict verification rejects exactly CH05 and CH06 as unlocked, as required before review. Active/legacy manifests, dependency manifest, toolchain and the Core aggregator remain byte-identical to the baseline.

Review the generic positive-size layer, kernel signs, integer shift and witness hypotheses together with CH06's grading/locality/matrix-unit interface. Approval precedes locking and Phase B. No proof work or promotion is performed in this draft.

## Phase A source provenance

| Source | SHA-256 |
| --- | --- |
| `notes/md/ch05_fermions_lattice_band.md` | `0a7a26d8890640541d39e918e3f3f87aeb8cb625914a34dc0709cfc73ff43051` |
| `notes/appendices/a01_fourier_scalars_and_characters.md` | `0b65cf6f5ed73a59ef5d25b2b502c34c4315cb5ce1df67cb690c3defba70b165` |
| `notes/appendices/a04_density_partitions_and_sugawara.md` | `32016e054e850c9796ae58d1493f1c552c71ab42607fc5f91b8b1878d37e6e9e` |
| `notes/md/TOC.md` | `5ea6b32bdecf8f9c65a345dc12356ff767b176c0b131e32acdb836778b054977` |
| `docs/audit/reference_notes_lean_audit.md` | `35245d3a8ed87e5ed1f31947132fb272848cfc8ff83236af49c9c45dc0bb4877` |
| `note/proof_suggestions_revision_2026-10-09.md` | `1db5f28b3e392d3b400ccc219ac640778fc5ceabc5cba17dfeb44b225a1b383c` |

## Definition axiom audit

```text
'Bosonize.Ch05.FockSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.Operators' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.momentumAnnihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.momentumCreation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.momentumNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.positionAnnihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.positionCreation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.positionNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.totalNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.occupationEnergy' depends on axioms: [propext, Quot.sound]
'Bosonize.Ch05.bareHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.seaConfiguration' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.seaEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.seaKet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.shiftedHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.parity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Historical Phase B implementation and validation

User authorization to proceed to Phase B approved the CH05/CH06 interface; the exact lock was committed as `34150a5`. Proof bodies alone changed. All 35 CH05 lemmas are complete.

Fourier CAR follows finite double-sum bilinearity, momentum CAR, dual-character orthogonality and the real normalization identity. Inversion uses ordinary integer-negated characters; creation inversion follows by adjoint. Total-number invariance reuses annihilation inversion. The occupation-basis laws explicitly transport the ordered-mode and subtype equality instances without altering the Fock carrier. Hamiltonian, parity and commutator proofs reuse frozen CH04 identities. The even sea is bijected with `range h`; its integer energy uses the exact triangular sum. Negative sea energy and nonzero Hamiltonian action supply nonvacuous witnesses.

Adopted the source's finite Fourier and occupation-basis arguments, adapting their instance transport and product order to the installed APIs. No new top-level helpers or assumptions were needed. Parallel attribution: the primary formalizer proved Fourier CAR, adjoints, basis/energy/parity laws and integrated results; scratch agents supplied sea arithmetic, inverses and total-number invariance. The delegated CH06 formalizer proved the dependent local-net module. All used the repository formalizer skill.

Validation against `34150a5`: strict guard verifies 271 statements and 225 ordered commands; all six complete Core hashes remain unchanged. All 69 guard regression tests, both libraries and direct warning-as-error compilation pass. Native Lean MCP CH05 diagnostics return a complete empty result with no failed dependencies. Fresh imported axiom inspection covers all 89 CH05/CH06 lemmas and 42 data declarations with only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. Source search remains unavailable through the MCP server PATH; shell retrieval and compiler/MCP goals were used.

Source-note edits that appeared concurrently in the worktree are outside this proof task and are preserved. The provenance table records Phase A inputs, rather than asserting the current edited notes have those historical hashes. At that checkpoint, Phase C promotion still required authorization; it was subsequently granted.

## Phase C promotion and freeze — 2026-10-09

User authorization covers promotion of CH05 and CH06. This module is now `Bosonize/Core/Ch05Fermions.lean`, imported by the root `Bosonize` aggregator; direct staging imports were removed. Its companion notebook moved to the matching Core path. Lean namespaces, all definitions, statements and proof bodies are preserved. CH05 moved byte-for-byte; CH06 changes only `public import BosonizeStubs.Ch05Fermions` to `public import Bosonize.Core.Ch05Fermions`.

The active v2 entries moved to their Core paths. CH05 retains every recorded hash and context; CH06 changes only the dependency-import command and the dependent context hashes. All 89 statement hashes are unchanged. The legacy manifest remains historical. Complete-source SHA-256 hashes were added for these two modules; all six previous Core hashes remain unchanged. This module's complete-source hash is `a19fed9d032daaa60df6bda4980b7470f10dd3e7333a63aec369a41e75c4dd81`.

Validation: `make ci` passes all 69 guard tests and both library builds; `make lock-check` verifies 271 statements, 225 commands and eight complete Core files. Both new Core modules pass direct compilation with warnings treated as errors and empty output. Native Lean MCP diagnostics on both Core paths return complete empty results with no failed dependencies. Goal retrieval on CH05's mixed CAR proof shows the final tactic closes its remaining branch. A fresh audit importing `Bosonize` verifies all 271 Core lemmas and the 42 CH05/CH06 data declarations using only permitted standard axioms, with no `sorryAx`. Exact notebook snapshots and source hashes are checked separately.

Use the committed promotion checkpoint (or a later approved reference containing the migrated manifests) as `STUB_LOCK_BASELINE_REF`. Historical staging references retain their old paths and cannot validate the new path baseline. Unrelated note edits and suggestion-file deletions are preserved outside this promotion. The primary formalizer performed this phase; no additional agents were dispatched. CH07/A03 drafting is the next proposed scope and has not started.

### Fresh Core axiom output for this module

```text
'Bosonize.Ch05.position_creation_eq_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.position_annihilation_eq_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.position_annihilation_car' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.position_creation_car' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.position_mixed_car' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.position_car_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.inverse_annihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.inverse_creation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.total_number_position' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.position_number_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.position_number_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.position_number_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.position_annihilation_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.position_creation_vacuum_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.parity_position_creation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.parity_position_annihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.total_number_position_creation_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.total_number_position_annihilation_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.total_number_ket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.bare_hamiltonian_ket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.shifted_hamiltonian_ket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.bare_hamiltonian_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.shifted_hamiltonian_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.bare_creation_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.bare_annihilation_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.shifted_creation_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.shifted_annihilation_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.sea_ket_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.bare_hamiltonian_sea' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.shifted_hamiltonian_sea' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.sea_card_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.sea_energy_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.sea_energy_negative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.bare_sea_action_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.sea_energy_half_size_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.FockSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.Operators' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.momentumAnnihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.momentumCreation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.momentumNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.positionAnnihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.positionCreation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.positionNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.totalNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.occupationEnergy' depends on axioms: [propext, Quot.sound]
'Bosonize.Ch05.bareHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.seaConfiguration' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.seaEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.seaKet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.shiftedHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch05.parity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Exact Lean source snapshot

Module SHA-256: `a19fed9d032daaa60df6bda4980b7470f10dd3e7333a63aec369a41e75c4dd81`. This block matches the frozen Core source byte-for-byte.

```lean
module

public import Bosonize.Core.A01FourierCharacters
public import Bosonize.Core.Ch03Fourier
public import Bosonize.Core.Ch04CARFock

/-!
# Chapter 5: position and momentum fermions
Phase A: complete definitions and one-sorry review stubs.
The Fourier layer works for positive L; physical sea formulas specialize to L = 2*h, h > 0.
-/

@[expose] public section

namespace Bosonize.Ch05

open scoped BigOperators

abbrev FockSpace (L : ℕ) := A02.FockSpace (Ch01.Band L)
abbrev Operators (L : ℕ) := Module.End ℂ (FockSpace L)

noncomputable def momentumAnnihilation (L : ℕ) (k : Ch01.Band L) : Operators L :=
  Ch04.annihilation k

noncomputable def momentumCreation (L : ℕ) (k : Ch01.Band L) : Operators L :=
  Ch04.creation k

noncomputable def momentumNumber (L : ℕ) (k : Ch01.Band L) : Operators L :=
  momentumCreation L k * momentumAnnihilation L k

/-- Positive character kernel for annihilators, with the real unitary normalization. -/
noncomputable def positionAnnihilation (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  (A01.normalization L : ℂ) • ∑ k : Ch01.Band L,
    A01.bandCharacter L (A01.canonicalRoot L) k x • momentumAnnihilation L k

/-- Ordinary integer negation in the character; no negative-band membership is assumed. -/
noncomputable def positionCreation (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  (A01.normalization L : ℂ) • ∑ k : Ch01.Band L,
    A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) • momentumCreation L k

noncomputable def positionNumber (L : ℕ) [NeZero L]
    (x : Ch01.Lattice L) : Operators L :=
  positionCreation L x * positionAnnihilation L x

noncomputable def totalNumber (L : ℕ) : Operators L :=
  ∑ k : Ch01.Band L, momentumNumber L k

/-- Integer spectrum, without clipping negative bare energies. -/
def occupationEnergy (L : ℕ) (S : A02.Occupation (Ch01.Band L)) : ℤ :=
  ∑ k ∈ S, k.val

noncomputable def bareHamiltonian (L : ℕ) : Operators L :=
  ∑ k : Ch01.Band L, (k.val : ℂ) • momentumNumber L k

/-- Fill all nonpositive labels in the actual positive-Nyquist band. -/
def seaConfiguration (L : ℕ) : A02.Occupation (Ch01.Band L) :=
  Finset.univ.filter (fun k => k.val ≤ 0)

def seaEnergy (L : ℕ) : ℤ := occupationEnergy L (seaConfiguration L)

noncomputable def seaKet (L : ℕ) : FockSpace L := A02.ket (seaConfiguration L)

noncomputable def shiftedHamiltonian (L : ℕ) : Operators L :=
  bareHamiltonian L - (seaEnergy L : ℂ) • (1 : Operators L)

noncomputable def parity (L : ℕ) : Operators L := Ch04.parity

section Fourier
variable (L : ℕ) [NeZero L]

lemma position_creation_eq_adjoint (x : Ch01.Lattice L) :
    positionCreation L x = LinearMap.adjoint (positionAnnihilation L x) := by
  simp only [positionCreation, positionAnnihilation, map_smulₛₗ, map_sum, starRingEnd_apply,
    A01.bandCharacter, A01.complex_character_conj L _ (A01.canonical_root_primitive L),
    A01.normalization_conj, momentumCreation, momentumAnnihilation, Ch04.creation_eq_adjoint]

lemma position_annihilation_eq_adjoint (x : Ch01.Lattice L) :
    positionAnnihilation L x = LinearMap.adjoint (positionCreation L x) := by
  rw [position_creation_eq_adjoint, LinearMap.adjoint_adjoint]

lemma position_annihilation_car (x y : Ch01.Lattice L) :
    A02.anticommutator (positionAnnihilation L x) (positionAnnihilation L y) = 0 := by
  have hsum (a b : Ch01.Band L → Operators L) (f g : Ch01.Band L → ℂ) :
      A02.anticommutator (∑ k, f k • a k) (∑ p, g p • b p) =
        ∑ k, ∑ p, (f k * g p) • A02.anticommutator (a k) (b p) := by
    simp only [A02.anticommutator, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
      mul_smul_comm, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro p hp
    rw [mul_comm (g p) (f k)]
  have hc (k p : Ch01.Band L) : A02.anticommutator (momentumAnnihilation L k) (momentumAnnihilation L p) = 0 := by
    convert Ch04.annihilation_car k p using 1
    all_goals simp [momentumAnnihilation, FockSpace]
  simp only [positionAnnihilation, Finset.smul_sum, smul_smul]
  rw [hsum]
  simp only [hc, smul_zero, Finset.sum_const_zero]

lemma position_creation_car (x y : Ch01.Lattice L) :
    A02.anticommutator (positionCreation L x) (positionCreation L y) = 0 := by
  have hsum (a b : Ch01.Band L → Operators L) (f g : Ch01.Band L → ℂ) :
      A02.anticommutator (∑ k, f k • a k) (∑ p, g p • b p) =
        ∑ k, ∑ p, (f k * g p) • A02.anticommutator (a k) (b p) := by
    simp only [A02.anticommutator, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
      mul_smul_comm, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro p hp
    rw [mul_comm (g p) (f k)]
  have hc (k p : Ch01.Band L) : A02.anticommutator (momentumCreation L k) (momentumCreation L p) = 0 := by
    convert Ch04.creation_car k p using 1
    all_goals simp [momentumCreation, FockSpace]
  simp only [positionCreation, Finset.smul_sum, smul_smul]
  rw [hsum]
  simp only [hc, smul_zero, Finset.sum_const_zero]

lemma position_mixed_car (x y : Ch01.Lattice L) :
    A02.anticommutator (positionAnnihilation L x) (positionCreation L y) =
      (if x = y then (1 : ℂ) else 0) • (1 : Operators L) := by
  have hsum (a b : Ch01.Band L → Operators L) (f g : Ch01.Band L → ℂ) :
      A02.anticommutator (∑ k, f k • a k) (∑ p, g p • b p) =
        ∑ k, ∑ p, (f k * g p) • A02.anticommutator (a k) (b p) := by
    simp only [A02.anticommutator, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
      mul_smul_comm, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro p hp
    rw [mul_comm (g p) (f k)]
  have hc (k p : Ch01.Band L) :
      A02.anticommutator (momentumAnnihilation L k) (momentumCreation L p) =
        (if k = p then (1 : ℂ) else 0) • (1 : Operators L) := by
    convert Ch04.mixed_car k p using 1
    all_goals simp [momentumAnnihilation, momentumCreation, FockSpace]
  simp only [positionAnnihilation, positionCreation, Finset.smul_sum, smul_smul]
  rw [hsum]
  simp_rw [hc]
  simp only [ite_smul, smul_ite, zero_smul, smul_zero, one_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hchar (k : Ch01.Band L) :
      A01.bandCharacter L (A01.canonicalRoot L) k x *
        A01.integerCharacter (A01.canonicalRoot L) (-k.val) (y.val : ℤ) =
      A01.integerCharacter (A01.canonicalRoot L) k.val ((x.val : ℤ) - (y.val : ℤ)) := by
    unfold A01.bandCharacter A01.integerCharacter
    rw [← zpow_add₀ (A01.root_ne_zero L _ (A01.canonical_root_primitive L))]
    congr 1
    ring
  have hcoeff (k : Ch01.Band L) :
      ((A01.normalization L : ℂ) * A01.bandCharacter L (A01.canonicalRoot L) k x) *
        ((A01.normalization L : ℂ) * A01.integerCharacter (A01.canonicalRoot L) (-k.val) (y.val : ℤ)) =
      (A01.normalization L : ℂ)^2 *
        A01.integerCharacter (A01.canonicalRoot L) k.val ((x.val : ℤ) - (y.val : ℤ)) := by
    rw [← hchar]
    ring
  simp_rw [hcoeff]
  rw [← Finset.sum_smul, ← Finset.mul_sum,
    A01.dual_character_orthogonality L _ (A01.canonical_root_primitive L)]
  by_cases hxy : x = y
  · simp only [hxy, ite_true]
    rw [mul_comm, A01.normalization_square_complex, one_smul]
  · simp [hxy]


lemma position_car_exists : ∃ R : A02.CAR (Ch01.Lattice L) (FockSpace L),
    R.annihilation = positionAnnihilation L ∧ R.creation = positionCreation L := by
  exact ⟨{ annihilation := positionAnnihilation L
           creation := positionCreation L
           annihilation_car := position_annihilation_car L
           creation_car := position_creation_car L
           mixed_car := position_mixed_car L
           adjoint_compat := position_creation_eq_adjoint L }, rfl, rfl⟩

lemma inverse_annihilation (k : Ch01.Band L) :
    momentumAnnihilation L k = (A01.normalization L : ℂ) •
      ∑ x : Ch01.Lattice L,
        A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) •
          positionAnnihilation L x := by
  classical
  have he (p : Ch01.Band L) (x : Ch01.Lattice L) :
      A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) *
        A01.bandCharacter L (A01.canonicalRoot L) p x =
      A01.integerCharacter (A01.canonicalRoot L) (p.val - k.val) (x.val : ℤ) := by
    simp only [A01.integerCharacter, A01.bandCharacter]
    rw [← zpow_add₀ (A01.root_ne_zero L _ (A01.canonical_root_primitive L))]
    congr 1
    ring
  symm
  simp only [positionAnnihilation]
  simp_rw [smul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hs (p : Ch01.Band L) :
      (∑ x : Ch01.Lattice L,
        ((A01.normalization L : ℂ) * (A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) *
          (A01.normalization L : ℂ) * A01.bandCharacter L (A01.canonicalRoot L) p x)) •
          momentumAnnihilation L p) =
      ((A01.normalization L : ℂ) * ((A01.normalization L : ℂ) * (if p = k then (L : ℂ) else 0))) • momentumAnnihilation L p := by
    rw [← Finset.sum_smul]
    congr 1
    have hx (x : Ch01.Lattice L) :
        (A01.normalization L : ℂ) * (A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) *
          (A01.normalization L : ℂ) * A01.bandCharacter L (A01.canonicalRoot L) p x) =
        ((A01.normalization L : ℂ) * (A01.normalization L : ℂ)) * A01.integerCharacter (A01.canonicalRoot L)
          (p.val - k.val) (x.val : ℤ) := by
      rw [← he p x]
      ring
    simp_rw [hx]
    rw [← Finset.mul_sum, A01.character_orthogonality L _ (A01.canonical_root_primitive L)]
    ring
  simp_rw [hs]
  simp only [mul_ite, mul_zero, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hn : (A01.normalization L : ℂ) * ((A01.normalization L : ℂ) * (L : ℂ)) = 1 := by
    calc
      _ = (L : ℂ) * (A01.normalization L : ℂ) ^ 2 := by ring
      _ = 1 := A01.normalization_square_complex L
  rw [hn, one_smul]

lemma inverse_creation (k : Ch01.Band L) :
    momentumCreation L k = (A01.normalization L : ℂ) •
      ∑ x : Ch01.Lattice L,
        A01.bandCharacter L (A01.canonicalRoot L) k x • positionCreation L x := by
  have ha := congrArg LinearMap.adjoint (inverse_annihilation L k)
  have hconj (x : Ch01.Lattice L) :
      star (A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ)) =
        A01.bandCharacter L (A01.canonicalRoot L) k x := by
    rw [A01.complex_character_conj L _ (A01.canonical_root_primitive L)]
    simp [A01.bandCharacter]
  simpa only [momentumAnnihilation, Ch04.creation_eq_adjoint, map_smulₛₗ,
    map_sum, starRingEnd_apply, A01.normalization_conj, hconj,
    ← position_creation_eq_adjoint, momentumCreation] using ha

lemma total_number_position :
    (∑ x : Ch01.Lattice L, positionNumber L x) = totalNumber L := by
  classical
  unfold totalNumber momentumNumber
  simp_rw [inverse_annihilation L]
  simp only [mul_smul_comm, Finset.mul_sum, ← smul_mul_assoc]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [positionNumber, positionCreation, smul_mul_assoc, Finset.sum_mul]
  rw [Finset.smul_sum]

lemma position_number_idempotent (x : Ch01.Lattice L) :
    positionNumber L x * positionNumber L x = positionNumber L x := by
  obtain ⟨R, ha, hc⟩ := position_car_exists L
  simpa [A02.AlgebraicCAR.number, ha, hc, positionNumber] using
    A02.car_number_idempotent R.toAlgebraicCAR x

lemma position_number_adjoint (x : Ch01.Lattice L) :
    LinearMap.adjoint (positionNumber L x) = positionNumber L x := by
  change LinearMap.adjoint ((positionCreation L x).comp (positionAnnihilation L x)) = _
  rw [LinearMap.adjoint_comp, ← position_creation_eq_adjoint, ← position_annihilation_eq_adjoint]
  rfl

lemma position_number_commute (x y : Ch01.Lattice L) :
    positionNumber L x * positionNumber L y = positionNumber L y * positionNumber L x := by
  obtain ⟨R, ha, hc⟩ := position_car_exists L
  simpa [A02.AlgebraicCAR.number, ha, hc, positionNumber] using
    A02.car_number_commute R.toAlgebraicCAR x y

lemma position_annihilation_vacuum (x : Ch01.Lattice L) :
    positionAnnihilation L x (A02.ket ∅) = 0 := by
  have hv (k : Ch01.Band L) : momentumAnnihilation L k (A02.ket ∅) = 0 := by
    convert Ch04.annihilation_vacuum k using 1
    all_goals simp [momentumAnnihilation, FockSpace, A02.ket, A02.occupationBasis, A02.occupationONB]
  simp only [positionAnnihilation, LinearMap.smul_apply, LinearMap.sum_apply, hv, smul_zero, Finset.sum_const_zero]

lemma position_creation_vacuum_ne_zero (x : Ch01.Lattice L) :
    positionCreation L x (A02.ket ∅) ≠ 0 := by
  intro h
  have H := congrArg (fun A : Operators L => A (A02.ket ∅)) (position_mixed_car L x x)
  have Hz : A02.ket (∅ : A02.Occupation (Ch01.Band L)) = 0 := by
    simpa [A02.anticommutator, Module.End.mul_apply, h, position_annihilation_vacuum] using H.symm
  exact A02.ket_ne_zero ∅ Hz

lemma parity_position_creation (x : Ch01.Lattice L) :
    parity L * positionCreation L x = -(positionCreation L x * parity L) := by
  simp only [positionCreation, parity, momentumCreation, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, Ch04.parity_creation, smul_neg, Finset.sum_neg_distrib]

lemma parity_position_annihilation (x : Ch01.Lattice L) :
    parity L * positionAnnihilation L x = -(positionAnnihilation L x * parity L) := by
  simp only [positionAnnihilation, parity, momentumAnnihilation, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, Ch04.parity_annihilation, smul_neg, Finset.sum_neg_distrib]

lemma total_number_position_creation_commutator (x : Ch01.Lattice L) :
    A02.commutator (totalNumber L) (positionCreation L x) = positionCreation L x := by
  have hc (k : Ch01.Band L) : A02.commutator (totalNumber L) (momentumCreation L k) = momentumCreation L k := by
    convert Ch04.total_number_creation_commutator k using 1
    all_goals simp [totalNumber, momentumNumber, momentumCreation, momentumAnnihilation, Ch04.totalNumber, Ch04.number, FockSpace]
  simp only [positionCreation, A02.commutator, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← smul_sub]
  change (A01.normalization L : ℂ) • (∑ k : Ch01.Band L, _ • A02.commutator (totalNumber L) (momentumCreation L k)) = _
  simp_rw [hc]

lemma total_number_position_annihilation_commutator (x : Ch01.Lattice L) :
    A02.commutator (totalNumber L) (positionAnnihilation L x) = -positionAnnihilation L x := by
  have hc (k : Ch01.Band L) : A02.commutator (totalNumber L) (momentumAnnihilation L k) = -momentumAnnihilation L k := by
    convert Ch04.total_number_annihilation_commutator k using 1
    all_goals simp [totalNumber, momentumNumber, momentumCreation, momentumAnnihilation, Ch04.totalNumber, Ch04.number, FockSpace]
  simp only [positionAnnihilation, A02.commutator, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← smul_sub]
  change (A01.normalization L : ℂ) • (∑ k : Ch01.Band L, _ • A02.commutator (totalNumber L) (momentumAnnihilation L k)) = _
  simp_rw [hc]
  simp only [smul_neg, Finset.sum_neg_distrib]

end Fourier

section Energy
variable (L : ℕ)

lemma total_number_ket (S : A02.Occupation (Ch01.Band L)) :
    totalNumber L (A02.ket S) = (S.card : ℂ) • A02.ket S := by
  convert Ch04.total_number_ket S using 1
  all_goals simp [totalNumber, momentumNumber, momentumCreation, momentumAnnihilation,
    Ch04.totalNumber, Ch04.number, FockSpace, A02.ket, A02.occupationBasis, A02.occupationONB]

lemma bare_hamiltonian_ket (S : A02.Occupation (Ch01.Band L)) :
    bareHamiltonian L (A02.ket S) = (occupationEnergy L S : ℂ) • A02.ket S := by
  classical
  have hn (k : Ch01.Band L) : momentumNumber L k (A02.ket S) =
      (if k ∈ S then (1 : ℂ) else 0) • A02.ket S := by
    convert Ch04.number_ket k S using 1
    all_goals simp [momentumNumber, momentumCreation, momentumAnnihilation,
      Ch04.number, FockSpace, A02.ket, A02.occupationBasis, A02.occupationONB]
  simp only [bareHamiltonian, LinearMap.sum_apply, LinearMap.smul_apply, hn, smul_smul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_smul]
  congr 1
  simp [occupationEnergy]

lemma shifted_hamiltonian_ket (S : A02.Occupation (Ch01.Band L)) :
    shiftedHamiltonian L (A02.ket S) =
      ((occupationEnergy L S - seaEnergy L : ℤ) : ℂ) • A02.ket S := by
  simp [shiftedHamiltonian, bare_hamiltonian_ket, ← sub_smul]

lemma bare_hamiltonian_adjoint :
    LinearMap.adjoint (bareHamiltonian L) = bareHamiltonian L := by
  have hn (k : Ch01.Band L) : LinearMap.adjoint (momentumNumber L k) = momentumNumber L k := by
    convert Ch04.number_adjoint k using 1
    all_goals simp [momentumNumber, momentumCreation, momentumAnnihilation, Ch04.number, FockSpace]
  simp only [bareHamiltonian, map_sum, map_smulₛₗ, hn, starRingEnd_apply]
  simp

lemma shifted_hamiltonian_adjoint :
    LinearMap.adjoint (shiftedHamiltonian L) = shiftedHamiltonian L := by
  simp only [shiftedHamiltonian, map_sub, bare_hamiltonian_adjoint, map_smulₛₗ]
  simp

lemma bare_creation_commutator (k : Ch01.Band L) :
    A02.commutator (bareHamiltonian L) (momentumCreation L k) =
      (k.val : ℂ) • momentumCreation L k := by
  classical
  have hc (i : Ch01.Band L) : A02.commutator (momentumNumber L i) (momentumCreation L k) =
      (if i = k then (1 : ℂ) else 0) • momentumCreation L k := by
    convert Ch04.number_creation_commutator i k using 1
    all_goals simp [momentumNumber, momentumCreation, momentumAnnihilation, Ch04.number, FockSpace]
  simp only [bareHamiltonian, A02.commutator, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, ← Finset.sum_sub_distrib, ← smul_sub]
  change (∑ i : Ch01.Band L, (i.val : ℂ) • A02.commutator (momentumNumber L i) (momentumCreation L k)) = _
  simp_rw [hc]
  simp

lemma bare_annihilation_commutator (k : Ch01.Band L) :
    A02.commutator (bareHamiltonian L) (momentumAnnihilation L k) =
      (-k.val : ℂ) • momentumAnnihilation L k := by
  classical
  have hc (i : Ch01.Band L) : A02.commutator (momentumNumber L i) (momentumAnnihilation L k) =
      -(if i = k then (1 : ℂ) else 0) • momentumAnnihilation L k := by
    convert Ch04.number_annihilation_commutator i k using 1
    all_goals simp [momentumNumber, momentumCreation, momentumAnnihilation, Ch04.number, FockSpace]
  simp only [bareHamiltonian, A02.commutator, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, ← Finset.sum_sub_distrib, ← smul_sub]
  change (∑ i : Ch01.Band L, (i.val : ℂ) • A02.commutator (momentumNumber L i) (momentumAnnihilation L k)) = _
  simp_rw [hc]
  simp

lemma shifted_creation_commutator (k : Ch01.Band L) :
    A02.commutator (shiftedHamiltonian L) (momentumCreation L k) =
      (k.val : ℂ) • momentumCreation L k := by
  have hs : A02.commutator (shiftedHamiltonian L) (momentumCreation L k) =
      A02.commutator (bareHamiltonian L) (momentumCreation L k) := by
    simp only [shiftedHamiltonian, A02.commutator, sub_mul, mul_sub, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one]
    abel
  rw [hs, bare_creation_commutator]

lemma shifted_annihilation_commutator (k : Ch01.Band L) :
    A02.commutator (shiftedHamiltonian L) (momentumAnnihilation L k) =
      (-k.val : ℂ) • momentumAnnihilation L k := by
  have hs : A02.commutator (shiftedHamiltonian L) (momentumAnnihilation L k) =
      A02.commutator (bareHamiltonian L) (momentumAnnihilation L k) := by
    simp only [shiftedHamiltonian, A02.commutator, sub_mul, mul_sub, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one]
    abel
  rw [hs, bare_annihilation_commutator]

lemma sea_ket_ne_zero : seaKet L ≠ 0 := by
  exact A02.ket_ne_zero _

lemma bare_hamiltonian_sea :
    bareHamiltonian L (seaKet L) = (seaEnergy L : ℂ) • seaKet L := by
  exact bare_hamiltonian_ket L (seaConfiguration L)

lemma shifted_hamiltonian_sea : shiftedHamiltonian L (seaKet L) = 0 := by
  simp [seaKet, shifted_hamiltonian_ket, seaEnergy]

end Energy

/-- These physical contracts use exactly the notes' positive-even lattice. -/
lemma sea_card_even (h : ℕ) (hh : 0 < h) : (seaConfiguration (2*h)).card = h := by
  have hmem (k : Ch01.Band (2*h)) : k ∈ seaConfiguration (2*h) ↔ k.val ≤ 0 := by
    simp [seaConfiguration]
  have hin (k : Ch01.Band (2*h)) (hk : k ∈ seaConfiguration (2*h)) :
      (-k.val).toNat ∈ Finset.range h := by
    have hk0 := (hmem k).mp hk
    have hkb := k.property
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hkb
    simp only [Finset.mem_range]
    omega
  have hinj (k l : Ch01.Band (2*h)) (hk : k ∈ seaConfiguration (2*h))
      (hl : l ∈ seaConfiguration (2*h)) (he : (-k.val).toNat = (-l.val).toNat) : k = l := by
    have hk0 := (hmem k).mp hk
    have hl0 := (hmem l).mp hl
    apply Subtype.ext
    omega
  have hsurj (n : ℕ) (hn : n ∈ Finset.range h) :
      ∃ k, ∃ hk : k ∈ seaConfiguration (2*h), (-k.val).toNat = n := by
    simp only [Finset.mem_range] at hn
    have hb : Ch01.inBandPredicate (2*h) (-(n : ℤ)) := by
      simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]
      omega
    refine ⟨⟨-(n : ℤ), hb⟩, ?_, ?_⟩
    · apply (hmem _).mpr
      simp
    · simp
  simpa using Finset.card_bij (fun (k : Ch01.Band (2*h)) _ => (-k.val).toNat) hin (fun k hk l hl => hinj k l hk hl) hsurj

lemma sea_energy_even (h : ℕ) (hh : 0 < h) :
    seaEnergy (2*h) = -((h : ℤ) * ((h : ℤ) - 1) / 2) := by
  have hmem (k : Ch01.Band (2*h)) : k ∈ seaConfiguration (2*h) ↔ k.val ≤ 0 := by
    simp [seaConfiguration]
  have hin (k : Ch01.Band (2*h)) (hk : k ∈ seaConfiguration (2*h)) :
      (-k.val).toNat ∈ Finset.range h := by
    have hk0 := (hmem k).mp hk
    have hkb := k.property
    simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat] at hkb
    simp only [Finset.mem_range]
    omega
  have hinj (k l : Ch01.Band (2*h)) (hk : k ∈ seaConfiguration (2*h))
      (hl : l ∈ seaConfiguration (2*h)) (he : (-k.val).toNat = (-l.val).toNat) : k = l := by
    have hk0 := (hmem k).mp hk
    have hl0 := (hmem l).mp hl
    apply Subtype.ext
    omega
  have hsurj (n : ℕ) (hn : n ∈ Finset.range h) :
      ∃ k, ∃ hk : k ∈ seaConfiguration (2*h), (-k.val).toNat = n := by
    simp only [Finset.mem_range] at hn
    have hb : Ch01.inBandPredicate (2*h) (-(n : ℤ)) := by
      simp only [Ch01.inBandPredicate, Nat.cast_mul, Nat.cast_ofNat]
      omega
    refine ⟨⟨-(n : ℤ), hb⟩, ?_, ?_⟩
    · apply (hmem _).mpr
      simp
    · simp
  have hsum : seaEnergy (2*h) = ∑ n ∈ Finset.range h, -(n : ℤ) := by
    unfold seaEnergy occupationEnergy
    apply Finset.sum_bij (fun (k : Ch01.Band (2*h)) _ => (-k.val).toNat)
      hin (fun k hk l hl => hinj k l hk hl) hsurj
    intro k hk
    have hk0 := (hmem k).mp hk
    omega
  rw [hsum, Finset.sum_neg_distrib, ← Nat.cast_sum, Finset.sum_range_id,
    Int.natCast_ediv, Nat.cast_mul, Nat.cast_sub hh, Nat.cast_one]
  norm_num

lemma sea_energy_negative (h : ℕ) (hh : 2 ≤ h) : seaEnergy (2*h) < 0 := by
  rw [sea_energy_even h (by omega)]
  have hz : (2 : ℤ) ≤ h := by exact_mod_cast hh
  have hp : 2 ≤ (h : ℤ) * ((h : ℤ) - 1) := by nlinarith
  omega

lemma bare_sea_action_ne_zero (h : ℕ) (hh : 2 ≤ h) :
    bareHamiltonian (2*h) (seaKet (2*h)) ≠ 0 := by
  rw [bare_hamiltonian_sea]
  apply smul_ne_zero
  · exact Int.cast_ne_zero.mpr (ne_of_lt (sea_energy_negative h hh))
  · exact sea_ket_ne_zero _

lemma sea_energy_half_size_one : seaEnergy 2 = 0 := by
  norm_num [seaEnergy, occupationEnergy, seaConfiguration, Ch01.Band,
    Ch01.inBandPredicate, Finset.sum_filter]
  decide

end Bosonize.Ch05
```
