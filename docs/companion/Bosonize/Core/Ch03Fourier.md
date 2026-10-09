# Chapter 3 lab notebook: Finite Fourier transform

Status (2026-10-09): **Phase C complete: proved, audited, promoted, and frozen in Core.** Twelve complete definitions/abbreviations and 31 proved lemmas. Namespace: `Bosonize.Ch03`. Source: [Chapter 3](../../../../notes/md/ch03_fourier.md), with [A01](../../../../notes/appendices/a01_fourier_scalars_and_characters.md). Lean module: `Bosonize/Core/Ch03Fourier.lean`.

## Complete definitions and typed directions

| Object | Source → target / meaning |
| --- | --- |
| `analysis L ζ` (S) | `(Ch01.Lattice L → K) →ₗ[K] (Ch01.Band L → K)`; negative-sign finite-sum kernel. |
| `synthesis L ζ` (T) | `(Ch01.Band L → K) →ₗ[K] (Ch01.Lattice L → K)`; positive-sign kernel. |
| `inverseAnalysis L ζ` | Same direction as T, scaled by `(L:K)⁻¹`; its inverse claims require nonzero scalar L. |
| `PositionSpace`, `MomentumSpace` | Euclidean spaces over ℂ on the frozen position and signed-band index types. |
| `positionFunctions`, `momentumFunctions` | `WithLp.linearEquiv` from each Euclidean carrier to ordinary functions. |
| `analysisEuclidean`, `synthesisEuclidean` | Canonical-root S/T conjugated by the two distinct function equivalences. |
| `unitaryFourier`, `inverseUnitaryFourier` | `(normalization L : ℂ)` times the transported S/T, in their respective directions. Their inverse, adjoint and isometry contracts are now proved. |
| `transportPositionOperator` | Conjugation of an existing Chapter 2 function operator onto the spatial Euclidean carrier. |

S/T are constructed from the displayed finite sums. Structural additivity and scalar-linearity fields are complete elementary proofs; no theorem stub is used to manufacture a definition. The two inverse statements now prove that `inverseAnalysis` is the inverse under the approved hypotheses. All generic kernel claims require a primitive root, and inverse/bijectivity additionally require `(L:K) ≠ 0`.

The complex transform remains the locked linear map. Its properties are proved; the isometry proof uses Mathlib's `LinearMap.isometryOfInner` locally. A new public equivalence bundle would be a separately reviewed declaration addition; none was added.

## Mathlib reuse and sign orientation

The installed `ZMod.dft` is an unscaled negative-sign linear equivalence and its `.symm` has a positive-sign kernel multiplied by 1/L. `analysis_eq_dft` is the exact forward bridge at `bandProjection k`; `inverse_analysis_eq_inv_dft` specifies the inverse bridge after reindexing a band function through `A01.bandEquiv.symm`. Both bridges are proved. The generic inversion proof uses finite-sum exchange and A01 orthogonality; the bridges additionally establish agreement with Mathlib's canonical DFT and inverse. The explicit generic finite-sum maps remain useful for arbitrary primitive roots; trigonometric dispersion is asserted only for the selected canonical complex root.

`WithLp.linearEquiv 2 ℂ (I → ℂ)` runs from `EuclideanSpace ℂ I` to functions. Transport uses e_target.symm ∘ map ∘ e_source. No isometry assertion is made for the default ordinary-function norm. The counting inner products and finite-dimensional `LinearMap.adjoint` are applied on the Euclidean carriers.

## Completed proof dependency order

1. A01 supplies the proved root, representative, character, sum-transport and orthogonality contracts.
2. The generic S/T composition proofs exchange finite sums, combine integer powers with exact exponent algebra, and apply both orthogonality identities. Nonzero scalar L permits inverse cancellation and bijectivity. The delta-at-zero transform is exactly the constant one.
3. Shift eigenvectors follow from the residue character laws and the ±1 evaluation formulas. Linearity gives the difference and Laplacian eigenvectors. The transformed differences reindex a periodic finite sum using translation equivalences; their composition gives the transformed Laplacian.
4. Euclidean S/T compositions are transported through the actual function equivalences. The adjoint proof expands both counting inner products, conjugates the synthesis kernel, exchanges sums and applies A01 conjugation.
5. The normalization square law proves both normalized inverse identities. Semilinearity gives the normalized adjoint; the left inverse proves inner-product preservation and the right inverse proves surjectivity. Mathlib's proof-local isometry construction gives `Isometry` without adding a new public bundle.
6. The normalized Laplacian is obtained by transporting the generic transformed identity. The canonical sine formula rewrites integer powers as exponentials, expands the two opposite exponential phases, and uses the double-angle cosine identity and scalar casts.
7. The singleton transform and even-Nyquist character contracts are proved. No coprimality of every nonzero frequency is assumed.

The delta-at-zero result is a proved nonzero-image witness. L=1 is handled by a subsingleton sum, without a nontrivial-frequency premise. The existing positive Nyquist representative and frozen Chapter 2 operators remain unchanged. No physical half-filling, analytic limit or budget hypothesis was added.

## Review choices and future obligations

Adopt the source's separate algebraic and Hilbert layers, frozen Chapter 2 operators, exact kernel signs and normalization. Adapt reuse to explicit bridge lemmas instead of silently identifying Band with ZMod. Reject T as an unscaled inverse, 1/L normalization on both physical kernels, the retired fractional-power dispersion expression and suppressed warnings.

The Chapter 3-specific proof suggestions directory has no matching file; the [revised stub guide](../../../../docs/stub_suggestion/chapter_3_fourier_stub_draft.md), A01 and current inline strategies are advisory. All bridge, inverse, adjoint, eigenvalue and dispersion statements in this module are now proved. If proof development discovers a shared mathematical/interface failure, checkpoint it and follow the adaptive issue-sprint procedure; do not change existing Core.

The reviewed interface is locked: generic field assumptions, names, inverse scalar hypothesis and all definitions/statements are preserved. Any future public bundling or interface revision needs separate review; existing Core remains immutable.

## Phase B validation (historical checkpoint)

The user approved both interfaces, supplied the updated strict lock, and authorized Phase B. Before proof edits, the supplied lock was compared structurally with the previous committed lock: it added only these two modules and preserved every existing entry. The reviewed lock was committed as `73add9042f2247fcbb1048d3b39f44f844f5e4b1`. It was not regenerated during proof development.

- `STUB_LOCK_BASELINE_REF=73add90 make ci` passes: 69 guard tests, 113 frozen lemma statements, 102 frozen commands, two complete Core source hashes, and both Lean library builds.
- Fresh `lake env lean -DwarningAsError=true BosonizeStubs/A01FourierCharacters.lean` and the corresponding Chapter 3 command exit 0 with empty diagnostics. No warning or lint suppression was introduced.
- All 30 A01 and 31 Chapter 3 lemmas have complete proofs. Structural inspection finds zero `sorry`, `admit` or `axiom` commands in either module; all 18 definitions/abbreviations and all approved headers remain unchanged.
- Fresh `#print axioms` over all 61 theorem names finds only subsets of `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. The module-specific output is recorded below.
- The notebook source block exactly matches the current Lean file. Core, imports, namespaces, toolchain and dependency manifest are unchanged; the strict committed-baseline guard verifies all frozen definitions and statements.
- Native Lean MCP tools are not exposed in this chat. Compiler and local-library checks supply the evidence above; native MCP/LSP transport was not tested.

Phase B completed against `73add90`. The user subsequently authorized Phase C for both modules; the current promotion evidence follows. No new top-level helper, equivalence bundle or assumption was added.

## Theorem axiom audit

```text
'Bosonize.Ch03.analysis_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.synthesis_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.synthesis_analysis' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.analysis_synthesis' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.inverse_analysis_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.inverse_analysis_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.analysis_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.analysis_delta_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.shift_character' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.inverse_shift_character' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.forward_diff_character' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.backward_diff_character' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.laplacian_eigenvalue_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.laplacian_character' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.analysis_forward_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.analysis_backward_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.analysis_laplacian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.analysis_eq_dft' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.inverse_analysis_eq_inv_dft' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.synthesisEuclidean_analysisEuclidean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.analysisEuclidean_synthesisEuclidean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.analysisEuclidean_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.unitary_inverse_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.unitary_inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.unitary_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.unitary_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.unitary_isometry' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.unitary_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.unitary_laplacian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.canonical_laplacian_dispersion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Bosonize.Ch03.singleton_analysis' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Provenance

Source baseline before this draft: `6ec5df254fb130a1a1483ceddffdaf22ee3e0d06`. The following hashes identify the exact source material consulted. These are source snapshots, not mathematical certification. Existing dated reviews may describe earlier revisions; the current notes and completion ledger control this draft.

| Source | SHA-256 |
| --- | --- |
| `notes/md/ch03_fourier.md` | `d4da4a800d18e68580fb793a3c8c9ba55d54836cf06253dd69e26ac86b89370e` |
| `notes/appendices/a01_fourier_scalars_and_characters.md` | `0b65cf6f5ed73a59ef5d25b2b502c34c4315cb5ce1df67cb690c3defba70b165` |
| `docs/stub_suggestion/chapter_3_fourier_stub_draft.md` | `793284489dbe77f76ca1a781fea878e2080445aba9375f72ae529c28d4dbe9a1` |
| `note/proof_suggestions_revision_2026-10-09.md` | `1db5f28b3e392d3b400ccc219ac640778fc5ceabc5cba17dfeb44b225a1b383c` |
| `note/notes_review_completion_2026-10-09.md` | `ee96609b0c32346be604041a99e3345c3420b71c830c88ef83ff8d93bd9c1dc1` |
| `Bosonize/Core/Ch01LatticeBand.lean` | `a88cd251573aa8a5416afa583b0a97b1e575ab09d4742b13a5b0be0e8a16b132` |
| `Bosonize/Core/Ch02UmbralCalculus.lean` | `d8d70d75372733aefda49e50baa033aaa5b363a57c0ec67a5a91368ac2d6f425` |
| `lean-toolchain` | `8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7` |
| `lake-manifest.json` | `237acfc7835876d993b4025c88431d8d39f76db83cab94c9f9a640395f9c61f4` |


## Phase C promotion and complete-source freeze

The user authorized promotion of A01 and CH03 on 2026-10-09. Before migration, strict interface verification against `bfaa0e9` passed (113 statements, 102 commands), both existing Core source hashes matched, both staging modules freshly compiled without diagnostics, and all 61 Fourier lemmas passed a standard-axiom audit.

CH03's A01 import changes from `BosonizeStubs.A01FourierCharacters` to `Bosonize.Core.A01FourierCharacters`. Exactly that import command/hash and the mechanically dependent theorem context hashes change. All 31 theorem header hashes and all other command records remain identical. This narrowly scoped dependency-path migration is part of the authorized joint promotion; the whole baseline was not regenerated.

Both source modules and their companion notebooks move to Core. `Bosonize.lean` imports them in dependency order; staging imports Core. Definitions, theorem statements, namespaces, and proof bodies are preserved. Only the CH03 dependency import and historical module status comments change. Existing CH01/CH02 sources and lock entries remain unchanged. The legacy v1 manifest is retained.

- `make ci` passes all 69 guard tests, 113 statements, 102 commands, four complete Core source hashes, and both library builds. Core treats warnings as errors.
- Fresh `lake env lean -DwarningAsError=true` on each promoted source returns exit 0 with empty diagnostics.
- A fresh audit via `import Bosonize` checks all 113 Core lemmas, including all 61 promoted lemmas: only `propext`, `Classical.choice`, and `Quot.sound` occur. No placeholders or extra axioms occur. The module-specific axiom output above is unchanged from the freshly repeated audit.
- Native Lean MCP is now attached to this chat: diagnostics on both promoted files return success with empty items, no failed dependencies, no partial result, and no timeout. Goal retrieval on A01 `root_pow_size` reports the expected context and target before `exact hζ.pow_eq_one`, and no goals afterward.
- `make lock-check` passes. The promotion commit becomes the new path-aware baseline; both guards are checked against that committed reference after the checkpoint is created.
- Next implementation is planned in [the roadmap](../../../../adaptative_roadmap.md): CH04 with finite-CAR A02 support. Its Phase A remains subject to authorization.

Complete source SHA-256: `6d0ba9cd4751c7cb321bc8cc786f355b768ee84a28ea6251628e495972160fed`. `core_locks.json` freezes every byte, including the proofs and comments.

## Exact Lean source snapshot

The complete source below is byte-for-byte identical to the promoted module, including its final newline.

Module SHA-256: `6d0ba9cd4751c7cb321bc8cc786f355b768ee84a28ea6251628e495972160fed`.

```lean
module

public import Bosonize.Core.Ch02UmbralCalculus
public import Bosonize.Core.A01FourierCharacters
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Chapter 3: finite Fourier transform

Phase C: proved, audited, and frozen. S is negative-sign analysis; T is positive-sign synthesis.
The generic algebraic inverse is L⁻¹ T. Complex counting-space normalization is separate.
The normalized map has proved inverse, adjoint, inner-product, isometry, and surjectivity laws.
-/

@[expose] public section

namespace Bosonize.Ch03

open scoped BigOperators

variable {K : Type*} [Field K]

/-- Unscaled negative-sign analysis on distinct position and band function carriers. -/
noncomputable def analysis (L : ℕ) [NeZero L] (ζ : K) :
    (Ch01.Lattice L → K) →ₗ[K] (Ch01.Band L → K) where
  toFun f k := ∑ x : Ch01.Lattice L, f x * A01.integerCharacter ζ (-k.val) (x.val : ℤ)
  map_add' f g := by
    funext k
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

/-- Unscaled positive-sign synthesis, before division by L. -/
noncomputable def synthesis (L : ℕ) [NeZero L] (ζ : K) :
    (Ch01.Band L → K) →ₗ[K] (Ch01.Lattice L → K) where
  toFun g x := ∑ k : Ch01.Band L, g k * A01.bandCharacter L ζ k x
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

/-- Candidate algebraic inverse; inverse claims explicitly require nonzero scalar L. -/
noncomputable def inverseAnalysis (L : ℕ) [NeZero L] (ζ : K) :
    (Ch01.Band L → K) →ₗ[K] (Ch01.Lattice L → K) := (L : K)⁻¹ • synthesis L ζ

lemma analysis_apply (L : ℕ) [NeZero L] (ζ : K) (f : Ch01.Lattice L → K)
    (k : Ch01.Band L) : analysis L ζ f k =
      ∑ x : Ch01.Lattice L, f x * A01.integerCharacter ζ (-k.val) (x.val : ℤ) := by
  rfl

lemma synthesis_apply (L : ℕ) [NeZero L] (ζ : K) (g : Ch01.Band L → K)
    (x : Ch01.Lattice L) : synthesis L ζ g x =
      ∑ k : Ch01.Band L, g k * A01.bandCharacter L ζ k x := by
  rfl

lemma synthesis_analysis (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    (synthesis L ζ).comp (analysis L ζ) = (L : K) • LinearMap.id := by
  classical
  apply LinearMap.ext
  intro f
  funext x
  change (∑ k : Ch01.Band L, (∑ y : Ch01.Lattice L,
    f y * A01.integerCharacter ζ (-k.val) (y.val : ℤ)) * A01.bandCharacter L ζ k x) =
      (L : K) * f x
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (y : Ch01.Lattice L) :
      (∑ k : Ch01.Band L, (f y * A01.integerCharacter ζ (-k.val) (y.val : ℤ)) *
        A01.bandCharacter L ζ k x) =
      f y * (∑ k : Ch01.Band L, A01.integerCharacter ζ k.val ((x.val : ℤ) - (y.val : ℤ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [A01.integerCharacter, A01.bandCharacter]
    rw [mul_assoc, ← zpow_add₀ (A01.root_ne_zero L ζ hζ)]
    congr 2
    ring
  simp_rw [he, A01.dual_character_orthogonality L ζ hζ]
  simp [mul_comm]

lemma analysis_synthesis (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    (analysis L ζ).comp (synthesis L ζ) = (L : K) • LinearMap.id := by
  classical
  apply LinearMap.ext
  intro g
  funext k
  change (∑ x : Ch01.Lattice L, (∑ p : Ch01.Band L,
    g p * A01.bandCharacter L ζ p x) * A01.integerCharacter ζ (-k.val) (x.val : ℤ)) =
      (L : K) * g k
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (p : Ch01.Band L) :
      (∑ x : Ch01.Lattice L, (g p * A01.bandCharacter L ζ p x) *
        A01.integerCharacter ζ (-k.val) (x.val : ℤ)) =
      g p * (∑ x : Ch01.Lattice L, A01.integerCharacter ζ (p.val - k.val) (x.val : ℤ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [A01.integerCharacter, A01.bandCharacter]
    rw [mul_assoc, ← zpow_add₀ (A01.root_ne_zero L ζ hζ)]
    congr 2
    ring
  simp_rw [he, A01.character_orthogonality L ζ hζ]
  simp [mul_comm]

lemma inverse_analysis_left (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (hLK : (L : K) ≠ 0) :
    (inverseAnalysis L ζ).comp (analysis L ζ) = LinearMap.id := by
  rw [inverseAnalysis, LinearMap.smul_comp, synthesis_analysis L ζ hζ, smul_smul,
    inv_mul_cancel₀ hLK, one_smul]

lemma inverse_analysis_right (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (hLK : (L : K) ≠ 0) :
    (analysis L ζ).comp (inverseAnalysis L ζ) = LinearMap.id := by
  rw [inverseAnalysis, LinearMap.comp_smul, analysis_synthesis L ζ hζ, smul_smul,
    inv_mul_cancel₀ hLK, one_smul]

lemma analysis_bijective (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (hLK : (L : K) ≠ 0) :
    Function.Bijective (analysis L ζ) := by
  have hl : Function.LeftInverse (inverseAnalysis L ζ) (analysis L ζ) := by
    intro f
    exact congrArg (fun A : Module.End K (Ch01.Lattice L → K) ↦ A f)
      (inverse_analysis_left L ζ hζ hLK)
  have hr : Function.RightInverse (inverseAnalysis L ζ) (analysis L ζ) := by
    intro g
    exact congrArg (fun A : Module.End K (Ch01.Band L → K) ↦ A g)
      (inverse_analysis_right L ζ hζ hLK)
  exact ⟨hl.injective, hr.surjective⟩

/-- A nonzero image witness: the position delta at zero analyzes to the constant one. -/
lemma analysis_delta_zero (L : ℕ) [NeZero L] (ζ : K) (hζ : IsPrimitiveRoot ζ L) :
    analysis L ζ (Pi.single (0 : Ch01.Lattice L) 1) = fun _ ↦ 1 := by
  classical
  cases hζ
  funext k
  simp [analysis, Pi.single_apply, A01.integerCharacter]

lemma shift_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.shift (A01.bandCharacter L ζ k) = (ζ ^ k.val) • A01.bandCharacter L ζ k := by
  funext x
  change A01.bandCharacter L ζ k (x + 1) = ζ ^ k.val * A01.bandCharacter L ζ k x
  have he : A01.residueCharacter L ζ (Ch01.bandProjection L k) 1 = ζ ^ k.val := by
    simpa only [Int.cast_one, A01.integerCharacter, mul_one, Ch01.bandProjection, Ch01.quotientMap] using
      A01.residue_character_int_cast L ζ hζ k.val 1
  rw [A01.band_character_projection L ζ hζ, A01.residue_character_add_right L ζ hζ,
    he, A01.band_character_projection L ζ hζ]
  ring

lemma inverse_shift_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.inverseShift (A01.bandCharacter L ζ k) =
      (ζ ^ (-k.val)) • A01.bandCharacter L ζ k := by
  funext x
  change A01.bandCharacter L ζ k (x - 1) = ζ ^ (-k.val) * A01.bandCharacter L ζ k x
  have he : A01.residueCharacter L ζ (Ch01.bandProjection L k) (-1) = ζ ^ (-k.val) := by
    simpa only [Int.cast_neg, Int.cast_one, A01.integerCharacter, mul_neg, mul_one, Ch01.bandProjection, Ch01.quotientMap] using
      A01.residue_character_int_cast L ζ hζ k.val (-1)
  rw [A01.band_character_projection L ζ hζ, sub_eq_add_neg,
    A01.residue_character_add_right L ζ hζ, he, A01.band_character_projection L ζ hζ]
  ring

lemma forward_diff_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.forwardDiff (A01.bandCharacter L ζ k) =
      (ζ ^ k.val - 1) • A01.bandCharacter L ζ k := by
  funext x
  have hs := congrFun (shift_character L ζ hζ k) x
  rw [Ch02.shift_apply, Pi.smul_apply, smul_eq_mul] at hs
  simp only [Ch02.forward_diff_apply, Pi.smul_apply, smul_eq_mul]
  rw [hs]
  ring

lemma backward_diff_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.backwardDiff (A01.bandCharacter L ζ k) =
      (1 - ζ ^ (-k.val)) • A01.bandCharacter L ζ k := by
  funext x
  have hs := congrFun (inverse_shift_character L ζ hζ k) x
  rw [Ch02.inverse_shift_apply, Pi.smul_apply, smul_eq_mul] at hs
  simp only [Ch02.backward_diff_apply, Pi.smul_apply, smul_eq_mul]
  rw [hs]
  ring

lemma laplacian_eigenvalue_factor (ζ : K) (hζ : ζ ≠ 0) (k : ℤ) :
    (ζ ^ k - 1) * (1 - ζ ^ (-k)) = ζ ^ k + ζ ^ (-k) - 2 := by
  have he : ζ ^ k * ζ ^ (-k) = 1 := by rw [← zpow_add₀ hζ]; simp
  linear_combination -he

lemma laplacian_character (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (k : Ch01.Band L) :
    Ch02.laplacian (A01.bandCharacter L ζ k) =
      (ζ ^ k.val + ζ ^ (-k.val) - 2) • A01.bandCharacter L ζ k := by
  rw [Ch02.laplacian, LinearMap.comp_apply, backward_diff_character L ζ hζ,
    map_smul, forward_diff_character L ζ hζ, smul_smul,
    mul_comm (1 - ζ ^ (-k.val)), laplacian_eigenvalue_factor ζ (A01.root_ne_zero L ζ hζ)]

lemma analysis_forward_diff (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (f : Ch01.Lattice L → K) (k : Ch01.Band L) :
    analysis L ζ (Ch02.forwardDiff f) k = (ζ ^ k.val - 1) * analysis L ζ f k := by
  classical
  let q : Ch01.Lattice L → K := fun x ↦ A01.integerCharacter ζ (-k.val) (x.val : ℤ)
  have hc (x : Ch01.Lattice L) : q x = A01.residueCharacter L ζ (-(Ch01.bandProjection L k)) x := by
    have hx : ((x.val : ℤ) : Ch01.Lattice L) = x := by simp
    simpa only [q, Int.cast_neg, hx, Ch01.bandProjection, Ch01.quotientMap] using
      (A01.residue_character_int_cast L ζ hζ (-k.val) (x.val : ℤ)).symm
  have he : A01.residueCharacter L ζ (-(Ch01.bandProjection L k)) (-1) = ζ ^ k.val := by
    simpa only [Int.cast_neg, Int.cast_one, Ch01.bandProjection, Ch01.quotientMap,
      A01.integerCharacter, neg_mul_neg, mul_one] using
      A01.residue_character_int_cast L ζ hζ (-k.val) (-1)
  have hq (x : Ch01.Lattice L) : q (x - 1) = q x * ζ ^ k.val := by
    rw [hc, sub_eq_add_neg, A01.residue_character_add_right L ζ hζ, he, ← hc]
  let e : Ch01.Lattice L ≃ Ch01.Lattice L :=
    { toFun := fun x ↦ x + 1
      invFun := fun x ↦ x - 1
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  have hs : (∑ x : Ch01.Lattice L, f (x + 1) * q x) =
      ∑ x : Ch01.Lattice L, f x * q (x - 1) := by
    simpa [e] using e.sum_comp (fun x ↦ f x * q (x - 1))
  change (∑ x : Ch01.Lattice L, (f (x + 1) - f x) * q x) =
    (ζ ^ k.val - 1) * ∑ x : Ch01.Lattice L, f x * q x
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, hs]
  simp_rw [hq, ← mul_assoc]
  rw [← Finset.sum_mul]
  ring

lemma analysis_backward_diff (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (f : Ch01.Lattice L → K) (k : Ch01.Band L) :
    analysis L ζ (Ch02.backwardDiff f) k = (1 - ζ ^ (-k.val)) * analysis L ζ f k := by
  classical
  let q : Ch01.Lattice L → K := fun x ↦ A01.integerCharacter ζ (-k.val) (x.val : ℤ)
  have hc (x : Ch01.Lattice L) : q x = A01.residueCharacter L ζ (-(Ch01.bandProjection L k)) x := by
    have hx : ((x.val : ℤ) : Ch01.Lattice L) = x := by simp
    simpa only [q, Int.cast_neg, hx, Ch01.bandProjection, Ch01.quotientMap] using
      (A01.residue_character_int_cast L ζ hζ (-k.val) (x.val : ℤ)).symm
  have he : A01.residueCharacter L ζ (-(Ch01.bandProjection L k)) 1 = ζ ^ (-k.val) := by
    simpa only [Int.cast_neg, Int.cast_one, Ch01.bandProjection, Ch01.quotientMap,
      A01.integerCharacter, mul_one] using
      A01.residue_character_int_cast L ζ hζ (-k.val) 1
  have hq (x : Ch01.Lattice L) : q (x + 1) = q x * ζ ^ (-k.val) := by
    rw [hc, A01.residue_character_add_right L ζ hζ, he, ← hc]
  let e : Ch01.Lattice L ≃ Ch01.Lattice L :=
    { toFun := fun x ↦ x - 1
      invFun := fun x ↦ x + 1
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  have hs : (∑ x : Ch01.Lattice L, f (x - 1) * q x) =
      ∑ x : Ch01.Lattice L, f x * q (x + 1) := by
    simpa [e] using e.sum_comp (fun x ↦ f x * q (x + 1))
  change (∑ x : Ch01.Lattice L, (f x - f (x - 1)) * q x) =
    (1 - ζ ^ (-k.val)) * ∑ x : Ch01.Lattice L, f x * q x
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, hs]
  simp_rw [hq, ← mul_assoc]
  rw [← Finset.sum_mul]
  ring

lemma analysis_laplacian (L : ℕ) [NeZero L] (ζ : K)
    (hζ : IsPrimitiveRoot ζ L) (f : Ch01.Lattice L → K) (k : Ch01.Band L) :
    analysis L ζ (Ch02.laplacian f) k =
      (ζ ^ k.val + ζ ^ (-k.val) - 2) * analysis L ζ f k := by
  rw [Ch02.laplacian, LinearMap.comp_apply, analysis_forward_diff L ζ hζ,
    analysis_backward_diff L ζ hζ, ← mul_assoc,
    laplacian_eigenvalue_factor ζ (A01.root_ne_zero L ζ hζ)]

/-- Counting-inner-product spatial carrier. -/
abbrev PositionSpace (L : ℕ) := EuclideanSpace ℂ (Ch01.Lattice L)

/-- Counting-inner-product signed momentum carrier. -/
abbrev MomentumSpace (L : ℕ) := EuclideanSpace ℂ (Ch01.Band L)

/-- Euclidean-to-function transport; this does not assert a function-norm isometry. -/
noncomputable def positionFunctions (L : ℕ) : PositionSpace L ≃ₗ[ℂ] (Ch01.Lattice L → ℂ) :=
  WithLp.linearEquiv 2 ℂ (Ch01.Lattice L → ℂ)

noncomputable def momentumFunctions (L : ℕ) : MomentumSpace L ≃ₗ[ℂ] (Ch01.Band L → ℂ) :=
  WithLp.linearEquiv 2 ℂ (Ch01.Band L → ℂ)

/-- Canonical unscaled analysis transported to the counting-space carriers. -/
noncomputable def analysisEuclidean (L : ℕ) [NeZero L] : PositionSpace L →ₗ[ℂ] MomentumSpace L :=
  (momentumFunctions L).symm.toLinearMap.comp
    ((analysis L (A01.canonicalRoot L)).comp (positionFunctions L).toLinearMap)

noncomputable def synthesisEuclidean (L : ℕ) [NeZero L] : MomentumSpace L →ₗ[ℂ] PositionSpace L :=
  (positionFunctions L).symm.toLinearMap.comp
    ((synthesis L (A01.canonicalRoot L)).comp (momentumFunctions L).toLinearMap)

/-- Normalized U remains a linear map in Phase A. -/
noncomputable def unitaryFourier (L : ℕ) [NeZero L] : PositionSpace L →ₗ[ℂ] MomentumSpace L :=
  (A01.normalization L : ℂ) • analysisEuclidean L

/-- Positive-sign candidate normalized inverse. -/
noncomputable def inverseUnitaryFourier (L : ℕ) [NeZero L] : MomentumSpace L →ₗ[ℂ] PositionSpace L :=
  (A01.normalization L : ℂ) • synthesisEuclidean L

/-- Transport a frozen Chapter 2 operator without redefining it. -/
noncomputable def transportPositionOperator (L : ℕ)
    (A : Module.End ℂ (Ch01.Lattice L → ℂ)) : Module.End ℂ (PositionSpace L) :=
  (positionFunctions L).symm.toLinearMap.comp (A.comp (positionFunctions L).toLinearMap)

lemma analysis_eq_dft (L : ℕ) [NeZero L] (f : Ch01.Lattice L → ℂ) (k : Ch01.Band L) :
    analysis L (A01.canonicalRoot L) f k =
      ZMod.dft f (Ch01.bandProjection L k) := by
  rw [analysis_apply, ZMod.dft_apply]
  apply Finset.sum_congr rfl
  intro x _
  have hc : ((x.val : ℤ) : Ch01.Lattice L) = x := by simp
  have h := A01.residue_character_int_cast L (A01.canonicalRoot L)
    (A01.canonical_root_primitive L) (-k.val) (x.val : ℤ)
  rw [← h, A01.canonical_character_std]
  simp only [Int.cast_neg, hc, Ch01.bandProjection, Ch01.quotientMap,
    mul_comm, mul_neg, smul_eq_mul]

lemma inverse_analysis_eq_inv_dft (L : ℕ) [NeZero L] (g : Ch01.Band L → ℂ)
    (x : Ch01.Lattice L) :
    inverseAnalysis L (A01.canonicalRoot L) g x =
      (ZMod.dft.symm (fun r ↦ g ((A01.bandEquiv L).symm r))) x := by
  rw [ZMod.invDFT_apply]
  change (L : ℂ)⁻¹ * synthesis L (A01.canonicalRoot L) g x = _
  congr 1
  rw [synthesis_apply]
  simp only [smul_eq_mul]
  have he := (A01.bandEquiv L).sum_comp
    (fun r : Ch01.Lattice L ↦ ZMod.stdAddChar (r * x) * g ((A01.bandEquiv L).symm r))
  rw [← he]
  apply Finset.sum_congr rfl
  intro k _
  rw [A01.band_character_projection L (A01.canonicalRoot L) (A01.canonical_root_primitive L),
    A01.canonical_character_std]
  change g k * ZMod.stdAddChar (Ch01.bandProjection L k * x) =
    ZMod.stdAddChar (Ch01.bandProjection L k * x) * g ((A01.bandEquiv L).symm ((A01.bandEquiv L) k))
  rw [Equiv.symm_apply_apply, mul_comm]

lemma synthesisEuclidean_analysisEuclidean (L : ℕ) [NeZero L] :
    (synthesisEuclidean L).comp (analysisEuclidean L) = (L : ℂ) • LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply (WithLp.ofLp_injective 2)
  funext x
  exact congrArg (fun A : Module.End ℂ (Ch01.Lattice L → ℂ) ↦ A (positionFunctions L f) x)
    (synthesis_analysis L (A01.canonicalRoot L) (A01.canonical_root_primitive L))

lemma analysisEuclidean_synthesisEuclidean (L : ℕ) [NeZero L] :
    (analysisEuclidean L).comp (synthesisEuclidean L) = (L : ℂ) • LinearMap.id := by
  apply LinearMap.ext
  intro g
  apply (WithLp.ofLp_injective 2)
  funext k
  exact congrArg (fun A : Module.End ℂ (Ch01.Band L → ℂ) ↦ A (momentumFunctions L g) k)
    (analysis_synthesis L (A01.canonicalRoot L) (A01.canonical_root_primitive L))

lemma analysisEuclidean_adjoint (L : ℕ) [NeZero L] :
    (analysisEuclidean L).adjoint = synthesisEuclidean L := by
  apply Eq.symm
  apply (LinearMap.eq_adjoint_iff (synthesisEuclidean L) (analysisEuclidean L)).mpr
  intro g f
  change (∑ x : Ch01.Lattice L, f x * star (∑ k : Ch01.Band L,
      g k * A01.bandCharacter L (A01.canonicalRoot L) k x)) =
    ∑ k : Ch01.Band L, (∑ x : Ch01.Lattice L,
      f x * A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ)) * star (g k)
  simp_rw [star_sum, star_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro x _
  have he : star (A01.bandCharacter L (A01.canonicalRoot L) k x) =
      A01.integerCharacter (A01.canonicalRoot L) (-k.val) (x.val : ℤ) :=
    A01.complex_character_conj L (A01.canonicalRoot L) (A01.canonical_root_primitive L) k.val (x.val : ℤ)
  rw [he]
  ring

lemma unitary_inverse_left (L : ℕ) [NeZero L] :
    (inverseUnitaryFourier L).comp (unitaryFourier L) = LinearMap.id := by
  rw [inverseUnitaryFourier, unitaryFourier, LinearMap.smul_comp, LinearMap.comp_smul,
    synthesisEuclidean_analysisEuclidean, smul_smul, smul_smul]
  have he : (A01.normalization L : ℂ) * (A01.normalization L : ℂ) * (L : ℂ) = 1 := by
    linear_combination A01.normalization_square_complex L
  rw [he, one_smul]

lemma unitary_inverse_right (L : ℕ) [NeZero L] :
    (unitaryFourier L).comp (inverseUnitaryFourier L) = LinearMap.id := by
  rw [inverseUnitaryFourier, unitaryFourier, LinearMap.smul_comp, LinearMap.comp_smul,
    analysisEuclidean_synthesisEuclidean, smul_smul, smul_smul]
  have he : (A01.normalization L : ℂ) * (A01.normalization L : ℂ) * (L : ℂ) = 1 := by
    linear_combination A01.normalization_square_complex L
  rw [he, one_smul]

lemma unitary_adjoint (L : ℕ) [NeZero L] :
    (unitaryFourier L).adjoint = inverseUnitaryFourier L := by
  unfold unitaryFourier inverseUnitaryFourier
  rw [map_smulₛₗ, analysisEuclidean_adjoint]
  simp only [starRingEnd_apply, A01.normalization_conj]

lemma unitary_inner (L : ℕ) [NeZero L] (f g : PositionSpace L) :
    inner ℂ (unitaryFourier L f) (unitaryFourier L g) = inner ℂ f g := by
  rw [← LinearMap.adjoint_inner_right, unitary_adjoint]
  have he := congrArg (fun A : Module.End ℂ (PositionSpace L) ↦ A g) (unitary_inverse_left L)
  change inverseUnitaryFourier L (unitaryFourier L g) = g at he
  rw [he]

lemma unitary_isometry (L : ℕ) [NeZero L] : Isometry (unitaryFourier L) := by
  exact ((unitaryFourier L).isometryOfInner (unitary_inner L)).isometry

lemma unitary_surjective (L : ℕ) [NeZero L] :
    Function.Surjective (unitaryFourier L) := by
  intro g
  refine ⟨inverseUnitaryFourier L g, ?_⟩
  exact congrArg (fun A : Module.End ℂ (MomentumSpace L) ↦ A g) (unitary_inverse_right L)

lemma unitary_laplacian (L : ℕ) [NeZero L] (f : PositionSpace L) (k : Ch01.Band L) :
    momentumFunctions L
      (unitaryFourier L (transportPositionOperator L Ch02.laplacian f)) k =
      (A01.canonicalRoot L ^ k.val + A01.canonicalRoot L ^ (-k.val) - 2) *
        momentumFunctions L (unitaryFourier L f) k := by
  change (A01.normalization L : ℂ) *
      analysis L (A01.canonicalRoot L) (Ch02.laplacian (positionFunctions L f)) k = _
  rw [analysis_laplacian L (A01.canonicalRoot L) (A01.canonical_root_primitive L)]
  change (A01.normalization L : ℂ) *
      ((A01.canonicalRoot L ^ k.val + A01.canonicalRoot L ^ (-k.val) - 2) *
        analysis L (A01.canonicalRoot L) (positionFunctions L f) k) =
    (A01.canonicalRoot L ^ k.val + A01.canonicalRoot L ^ (-k.val) - 2) *
      ((A01.normalization L : ℂ) * analysis L (A01.canonicalRoot L) (positionFunctions L f) k)
  ring

lemma canonical_laplacian_dispersion (L : ℕ) [NeZero L] (k : ℤ) :
    A01.canonicalRoot L ^ k + A01.canonicalRoot L ^ (-k) - 2 =
      ((-4 * Real.sin (Real.pi * (k : ℝ) / (L : ℝ)) ^ 2 : ℝ) : ℂ) := by
  have he (n : ℤ) : A01.canonicalRoot L ^ n =
      Complex.exp ((2 * (Real.pi : ℂ) * (n : ℂ) / (L : ℂ)) * Complex.I) := by
    unfold A01.canonicalRoot
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  rw [he k, he (-k), Int.cast_neg]
  have hp : (2 * (Real.pi : ℂ) * -(k : ℂ) / (L : ℂ)) * Complex.I =
      -((2 * (Real.pi : ℂ) * (k : ℂ) / (L : ℂ)) * Complex.I) := by ring
  rw [hp, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  have ht : 2 * (Real.pi : ℂ) * (k : ℂ) / (L : ℂ) =
      2 * ((Real.pi : ℂ) * (k : ℂ) / (L : ℂ)) := by ring
  rw [ht, Complex.cos_two_mul_eq_one_sub]
  push_cast
  ring

lemma singleton_analysis (f : Ch01.Lattice 1 → ℂ) (k : Ch01.Band 1) :
    analysis 1 (A01.canonicalRoot 1) f k = f 0 := by
  classical
  simp only [analysis_apply, Ch01.singleton_band k, neg_zero, A01.integerCharacter,
    zero_mul, zpow_zero, mul_one]
  exact Fintype.sum_subsingleton (f := f) 0

end Bosonize.Ch03
```
