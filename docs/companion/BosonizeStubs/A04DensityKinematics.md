# A04DensityKinematics: formal companion

Historical Phase A draft record, 2026-10-10. All **22** theorem targets remain one-sorry review stubs. The **7** data declarations contain no placeholders. Compilation establishes elaboration only; it does not establish the mathematical conclusions or standard-axiom completeness of theorem dependencies.

Source: [`notes/appendices/a04_density_partitions_and_sugawara.md`](../../../notes/appendices/a04_density_partitions_and_sugawara.md), [chapter TOC](../../../notes/md/TOC.md), [appendix index](../../../notes/appendices/README.md), [proof revision P06/P07](../../../note/proof_suggestions_revision_2026-10-09.md), and the frozen Core source modules imported below. Source SHA-256: `816d55d8032642f74003593bb75154a4d1752182d2d2c6ea79c344454810ede3`. The model tiers named in the skill were unavailable; drafting used the inherited available Codex model. Independent review passes; the reviewed interface lock is being committed for Phase B.

The first A04 slice isolates finite density kinematics. Partition bijections, Gram/completeness, restricted scalar CCR and Sugawara are deliberately deferred to their dependent chapters. The existing source theory is preserved rather than silently recast as a proved result.

`ShiftMatrix L` uses the frozen signed band `−L<2k≤L`, with the positive Nyquist representative at even length. `validPairs` compares integer values. Neither residue addition nor a zero-based enumeration defines the physical transfer. Generic matrix statements accommodate the empty band at L=0 and odd lengths; no unnecessary even-length hypothesis is introduced.

`compositionCoefficient` retains the intermediate-in-band condition. Same-sign compositions simplify because an interval contains every intermediate between two endpoints. Mixed compositions cannot simplify this way. `edgeMatrix` explicitly stores the two indicator difference. For `[T_{−m},T_n]`, the even-band formula is bottom minus top, and the support theorem records both source and target near the corresponding boundary. Subsequent budget proofs need both endpoints to establish Pauli blocking.

`dGamma` uses the concrete CH04 hopping operators on A02's occupation Hilbert space, and `dGammaLinear` constructs actual complex linearity without using theorem stubs. The Lie identity follows from CH04's CAR bilinear commutator. It is not an associative algebra morphism: the one-particle identity lifts to particle number, not the ambient Fock identity.

Adopted from P06: integer labels, exact intermediate indicators, CAR Lie lift, independent first-norm evidence. Adapted: use `Matrix.conjTranspose` for one-particle adjoints and `LinearMap.adjoint` on actual Fock operators. Rejected: unrestricted mixed-sign composition, any global finite scalar CCR, and a multiplicative/unital second-quantization claim.

Planned proofs: entrywise interval arithmetic and unique intermediate mode for matrix products; expand finite sums and use `Ch04.bilinear_commutator` for the Lie lift; reindex sums and use actual hopping adjoints for the star bridge. The concrete `shift_nonzero` pair is an explicit proposed witness, not yet proved evidence.

Validation: `lake build BosonizeStubs.A04DensityKinematics BosonizeStubs.Ch09DensityModes` completed successfully (3392 jobs). The two modules emit exactly 60 expected one-sorry warnings, with no other warnings or errors. A fresh `#print axioms` audit of all 21 data declarations returned only `propext`, `Classical.choice`, and `Quot.sound` (or no axioms); no data construction depends on `sorryAx`. This is data/elaboration evidence, not proof completion. Phase A review must check signs, intermediate indicators, both edge endpoints, Fourier normalization, cyclic remainder, nonzero witnesses, and proof feasibility. Phase B completion and Phase C promotion remain outstanding.

The exact source snapshot follows. Lemma bodies are intentionally unproved; data are fully elaborated constructions.

## Independent Phase A gate and Phase B baseline — 2026-10-10

Reviewer `/root/ch09_source_review`: **PASS**, with no blocking findings.
The reviewed source SHA-256 is the exact hash stated above. The independent reviewer
checked all 60 theorem targets and all 21 data declarations across the two modules;
compiler checks show exactly 22/38 expected stub warnings and no other diagnostics.
Fresh independent data axiom inspection excludes `sorryAx` and any nonstandard axiom.
Native Lean diagnostics report success, no failed dependencies and only the same
22/38 placeholder warnings. Companions mirror the source byte-for-byte.

The review checks nonwrapping integer transfers, mixed composition indicators,
both endpoints of edge support, bottom-minus-top sign, cyclic Fourier aliases,
transport phase, positive sea norm, arbitrary-charge grading, ground admissibility,
and h=0 behavior. The h=1 band {0,1} screens the alias distinction explicitly:
the full Fourier density at transfer 1 is rho_1 + rho_-1, rather than rho_1 alone.
This finite screen is evidence against the false identification, not a Lean proof.
Existing twelve Core files and unrelated user edits remain untouched.

The initial lock adds only these two independently reviewed module records.
Proof bodies are the Phase B edit boundary. Source and theorem claims remain
unproved until their individual proofs and fresh transitive audits are complete.

## Phase B complete — 2026-10-10

All **22 theorem proofs and 7 data declarations** are complete. The
current source snapshot below supersedes the historical unproved Phase A status.
Reviewed interface baseline: `e78c2d9`. Proof synthesis was partitioned across
`/root`, `/root/ch09_a04_draft`, `/root/ch09_source_review`, and
`/root/ch09_hop_probe`; unavailable Flash/Pro tiers were explicitly reported and
the inherited available Codex model was used. Concrete DecidableEq conversion
issues were independently troubleshot without changing any reviewed interface.

The integrated two-target build and both library builds pass (3401 jobs).
Direct compilation of each module with `-DwarningAsError=true` produces empty
logs. Fresh native Lean MCP diagnostics have success=true, partial=false, zero
items and no failed dependencies. All 60 theorem and 21 data axiom outputs have
only `propext`, `Classical.choice`, `Quot.sound`, or no axioms; there is no
`sorryAx` or custom axiom. Strict guard against `e78c2d9` passes 579 statements
and 456 commands, and all twelve existing Core source hashes are unchanged.

Matrix proofs use entrywise integer interval arithmetic and the unique allowed
intermediate mode. The CAR Lie lift expands actual bilinear commutators and
reindexes finite sums; adjoint compatibility uses actual Hilbert adjoints.
The CH09 dictionary uses twisted Fourier inversion and a character-sum proof
retaining the cyclic wrap remainder. Concrete CAR hops establish exact charge
and excitation shifts; nonnegative excitation gives lowering annihilation.
The sea norm is a count of distinct orthogonal signed occupation hops, followed
by self-adjoint energy orthogonality and evaluation at the sea for independence.
No later scalar CCR, partition theorem or Sugawara identity enters these proofs.

Phase B source SHA-256: `743595319b26ba93b593c5ea34c93c87b1a8cc6c88dac7e5a95b7aba6f389fd5`.
Phase C migration has an independent scoped PASS from `/root/ch09_hop_probe`:
only CH09's A04 import changes semantically, with the matching lock contexts;
all namespaces, theorem headers, proof bodies and prior Core hashes are retained.
Promotion and independently reviewed pedagogical synchronization are next.

```lean
module

public import Bosonize.Core.Ch05Fermions
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# A04 finite density kinematics
Phase A: complete concrete data and unproved one-sorry targets.
Integer partial shifts do not wrap. Second quantization preserves Lie brackets,
not products. Partitions, scalar budget CCR and Sugawara remain later work.
-/
@[expose] public section
namespace Bosonize.A04
open scoped BigOperators Classical

/-- Matrices on the frozen signed integer band, retaining the positive Nyquist representative. -/
abbrev ShiftMatrix (L : ℕ) := Matrix (Ch01.Band L) (Ch01.Band L) ℂ

/-- Valid source/target pairs for transfer m; equality is in ℤ, never residue addition. -/
def validPairs (L : ℕ) (m : ℤ) : Finset (Ch01.Band L × Ch01.Band L) :=
  Finset.univ.filter (fun z => z.1.val = z.2.val + m)

/-- The partial one-particle shift has unit matrix coefficient precisely for an unwrapped transfer. -/
def shift (L : ℕ) (m : ℤ) : ShiftMatrix L :=
  fun p k => if p.val = k.val + m then 1 else 0

/-- The exact intermediate-band coefficient in T_m T_n. Its indicator is indispensable for mixed signs. -/
def compositionCoefficient (L : ℕ) (m n : ℤ) (p k : Ch01.Band L) : ℂ :=
  if p.val = k.val + (m+n) ∧ Ch01.inBandPredicate L (k.val+n) then 1 else 0

/-- Difference of the two possible intermediate indicators, retaining finite edge hopping contributions. -/
def edgeMatrix (L : ℕ) (m n : ℤ) : ShiftMatrix L :=
  fun p k => compositionCoefficient L m n p k - compositionCoefficient L n m p k

/-- Weighted CAR bilinears on an arbitrary ordered finite mode set, acting on the existing occupation Hilbert space. -/
noncomputable def dGamma {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) : Module.End ℂ (A02.FockSpace ι) :=
  ∑ p, ∑ k, A p k • Ch04.hopping p k

/-- Complex linear second quantization. The following Lie theorem does not imply multiplicativity or unitality. -/
noncomputable def dGammaLinear (ι : Type*) [Fintype ι] [LinearOrder ι] :
    Matrix ι ι ℂ →ₗ[ℂ] Module.End ℂ (A02.FockSpace ι) where
  toFun := dGamma
  map_add' A B := by
    classical
    simp only [dGamma, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a A := by
    classical
    simp only [dGamma, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- Unpack the integer valid-pair predicate without changing carriers. -/
lemma mem_valid_pairs (L : ℕ) (m : ℤ) (p k : Ch01.Band L) :
    (p,k) ∈ validPairs L m ↔ p.val = k.val+m := by
  simp [validPairs]

/-- Zero transfer is the one-particle identity, including the empty-band case. -/
lemma shift_zero (L : ℕ) :
    shift L 0 = 1 := by
  classical
  ext p k
  simp [shift, Matrix.one_apply, Subtype.ext_iff]

/-- Band diameter is at most L−1, so transfers at least L vanish. -/
lemma shift_vanish (L : ℕ) (m : ℤ) (hm : (L : ℤ) ≤ |m|) :
    shift L m = 0 := by
  classical
  ext p k
  have he : p.val ≠ k.val+m := by
    have hp := p.property
    have hk := k.property
    unfold Ch01.inBandPredicate at hp hk
    by_cases h : 0 ≤ m
    · rw [abs_of_nonneg h] at hm
      omega
    · rw [abs_of_neg (by omega)] at hm
      omega
  simp [shift, he]

/-- The vanishing statement also applies directly to finite filtered sums. -/
lemma valid_pairs_empty (L : ℕ) (m : ℤ) (hm : (L : ℤ) ≤ |m|) :
    validPairs L m = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have he := (mem_valid_pairs L m z.1 z.2).mp hz
  have hs := congrArg (fun A : ShiftMatrix L => A z.1 z.2) (shift_vanish L m hm)
  simp [shift, he] at hs


/-- Matrix adjoint exchanges source and target and reverses the integer transfer. -/
lemma shift_adjoint (L : ℕ) (m : ℤ) :
    (shift L m).conjTranspose = shift L (-m) := by
  classical
  ext p k
  have he : k.val = p.val+m ↔ p.val=k.val+(-m) := by omega
  simp [shift, Matrix.conjTranspose_apply, he]


/-- Exact matrix multiplication includes the intermediate-in-band indicator. -/
lemma shift_mul_entry (L : ℕ) (m n : ℤ) (p k : Ch01.Band L) :
    (shift L m * shift L n) p k = compositionCoefficient L m n p k := by
  unfold compositionCoefficient
  classical
  by_cases hb : Ch01.inBandPredicate L (k.val+n)
  · let q : Ch01.Band L := ⟨k.val+n, hb⟩
    have he (r : Ch01.Band L) : r.val = k.val+n ↔ r=q := by
      constructor
      · intro h; exact Subtype.ext h
      · intro h; subst r; rfl
    simp [shift, Matrix.mul_apply, he, hb, q, add_assoc, add_comm n m]
  · have he (r : Ch01.Band L) : r.val ≠ k.val+n := by
      intro h; exact hb (h ▸ r.property)
    simp [shift, Matrix.mul_apply, he, hb]

/-- Monotone positive transport keeps the intermediate inside the interval whenever both endpoints are inside. -/
lemma shift_mul_nonnegative (L : ℕ) (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n) :
    shift L m * shift L n = shift L (m+n) := by
  classical
  ext p k
  rw [shift_mul_entry]
  unfold compositionCoefficient
  by_cases he : p.val = k.val+(m+n)
  · have hb : Ch01.inBandPredicate L (k.val+n) := by
      have hp := p.property
      have hk := k.property
      unfold Ch01.inBandPredicate at *
      omega
    simp [shift, he, hb]
  · simp [shift, he]

/-- Negative monotone transport has the same exact interval-composition law. -/
lemma shift_mul_nonpositive (L : ℕ) (m n : ℤ) (hm : m ≤ 0) (hn : n ≤ 0) :
    shift L m * shift L n = shift L (m+n) := by
  classical
  ext p k
  rw [shift_mul_entry]
  unfold compositionCoefficient
  by_cases he : p.val = k.val+(m+n)
  · have hb : Ch01.inBandPredicate L (k.val+n) := by
      have hp := p.property
      have hk := k.property
      unfold Ch01.inBandPredicate at *
      omega
    simp [shift, he, hb]
  · simp [shift, he]

/-- All finite commutator contributions are explicit differences of intermediate-band indicators. -/
lemma shift_commutator_edge (L : ℕ) (m n : ℤ) :
    shift L m * shift L n - shift L n * shift L m = edgeMatrix L m n := by
  ext p k
  simp only [Matrix.sub_apply, shift_mul_entry, edgeMatrix]


/-- A nonzero edge hopping has the expected transfer and exactly one admissible intermediate. -/
lemma edge_support (L : ℕ) (m n : ℤ) (p k : Ch01.Band L) (he : edgeMatrix L m n p k ≠ 0) :
    p.val = k.val+(m+n) ∧ (Ch01.inBandPredicate L (k.val+n) ↔ ¬ Ch01.inBandPredicate L (k.val+m)) := by
  unfold edgeMatrix compositionCoefficient at he
  by_cases hp : p.val=k.val+(m+n)
  · refine ⟨hp, ?_⟩
    by_cases hn : Ch01.inBandPredicate L (k.val+n) <;>
      by_cases hm : Ch01.inBandPredicate L (k.val+m) <;> simp_all [add_comm m n]
  · simp [hp, add_comm n m] at he


/-- The lowering-raising commutator is diagonal, with the bottom-minus-top orientation. -/
lemma opposite_shift_entry (L : ℕ) (m : ℤ) (p k : Ch01.Band L) :
    edgeMatrix L (-m) m p k = if p = k then (if Ch01.inBandPredicate L (k.val+m) then (1:ℂ) else 0) - (if Ch01.inBandPredicate L (k.val-m) then (1:ℂ) else 0) else 0 := by
  classical
  unfold edgeMatrix compositionCoefficient
  by_cases hp : p=k
  · subst p
    simp [sub_eq_add_neg]
  · have hval : p.val ≠ k.val := fun h => hp (Subtype.ext h)
    simp [hp, hval]


/-- A concrete allowed pair witnesses non-vacuity of the partial shift. -/
lemma shift_nonzero (L : ℕ) (m : ℤ) (p k : Ch01.Band L) (hp : p.val = k.val+m) :
    shift L m ≠ 0 := by
  intro hz
  have he := congrArg (fun A : ShiftMatrix L => A p k) hz
  simp [shift, hp] at he


/-- For nonnegative lowering/raising magnitudes the mixed commutator is explicitly
bottom minus top. Both tests use the original signed interval endpoints. -/
lemma mixed_edge_even (h : ℕ) (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (p k : Ch01.Band (2*h)) :
    edgeMatrix (2*h) (-m) n p k =
      if p.val = k.val+n-m then
        (if k.val < -(h : ℤ)+1+m then (1 : ℂ) else 0) -
        (if (h : ℤ)-n < k.val then (1 : ℂ) else 0)
      else 0 := by
  have hk := k.property
  unfold Ch01.inBandPredicate at hk
  have htop : Ch01.inBandPredicate (2*h) (k.val+n) ↔ k.val ≤ (h : ℤ)-n := by
    unfold Ch01.inBandPredicate
    push_cast at *
    omega
  have hbottom : Ch01.inBandPredicate (2*h) (k.val+(-m)) ↔ -(h : ℤ)+1+m ≤ k.val := by
    unfold Ch01.inBandPredicate
    push_cast at *
    omega
  have he1 : p.val = k.val+(-m+n) ↔ p.val=k.val+n-m := by omega
  have he2 : p.val = k.val+(n+(-m)) ↔ p.val=k.val+n-m := by omega
  simp only [edgeMatrix, compositionCoefficient, he1, he2, htop, hbottom]
  simp only [← not_lt]
  by_cases he : p.val=k.val+n-m <;>
    by_cases hb : k.val < -(h : ℤ)+1+m <;>
    by_cases ht : (h : ℤ)-n < k.val <;> simp_all <;> split_ifs <;> simp_all <;> omega


/-- A nonzero mixed edge hopping has both source and target in the matching boundary
regions. The two-endpoint information is needed for subsequent Pauli blocking proofs. -/
lemma mixed_edge_support_even (h : ℕ) (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (p k : Ch01.Band (2*h)) (he : edgeMatrix (2*h) (-m) n p k ≠ 0) :
    p.val = k.val+n-m ∧
      ((k.val < -(h : ℤ)+1+m ∧ p.val < -(h : ℤ)+1+n) ∨
       ((h : ℤ)-n < k.val ∧ (h : ℤ)-m < p.val)) := by
  rw [mixed_edge_even h m n hm hn p k] at he
  by_cases hp : p.val=k.val+n-m
  · refine ⟨hp, ?_⟩
    by_cases hb : k.val < -(h : ℤ)+1+m
    · left; constructor
      · exact hb
      · omega
    · have ht : (h : ℤ)-n < k.val := by
        by_contra hn
        simp [hp, hb, hn] at he
      right; constructor
      · exact ht
      · omega
  · simp [hp] at he


section SecondQuantization
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Zero coefficients yield the zero operator by linearity. -/
lemma dGamma_zero  :
    dGamma (0 : Matrix ι ι ℂ) = 0 := by
 simp [dGamma]

/-- Second quantization preserves sums of one-particle coefficients. -/
lemma dGamma_add (A B : Matrix ι ι ℂ) :
    dGamma (A+B) = dGamma A+dGamma B := by
 exact (dGammaLinear ι).map_add A B

/-- The coefficient dependence is complex linear. -/
lemma dGamma_smul (a : ℂ) (A : Matrix ι ι ℂ) :
    dGamma (a • A) = a • dGamma A := by
 exact (dGammaLinear ι).map_smul a A

/-- Subtraction is preserved, as needed when lifting edge matrices. -/
lemma dGamma_sub (A B : Matrix ι ι ℂ) :
    dGamma (A-B) = dGamma A-dGamma B := by
 exact (dGammaLinear ι).map_sub A B

/-- Adjoint conjugates coefficients and reverses each CAR bilinear. -/
lemma dGamma_adjoint (A : Matrix ι ι ℂ) :
    LinearMap.adjoint (dGamma A) = dGamma A.conjTranspose := by
 simp only [dGamma, map_sum, map_smulₛₗ, starRingEnd_apply, Ch04.hopping_adjoint,
   Matrix.conjTranspose_apply]
 rw [Finset.sum_comm]

/-- The CAR bilinear identity makes second quantization a linear Lie map. -/
lemma dGamma_commutator (A B : Matrix ι ι ℂ) :
    A02.commutator (dGamma A) (dGamma B) = dGamma (A*B-B*A) := by
 classical
 have hl (f : ι → Module.End ℂ (A02.FockSpace ι)) (X) :
   A02.commutator (∑ i, f i) X = ∑ i, A02.commutator (f i) X := by
   simp [A02.commutator, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
 have hr (f : ι → Module.End ℂ (A02.FockSpace ι)) (X) :
   A02.commutator X (∑ i, f i) = ∑ i, A02.commutator X (f i) := by
   simp [A02.commutator, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
 have hs (a b : ℂ) (X Y : Module.End ℂ (A02.FockSpace ι)) :
   A02.commutator (a • X) (b • Y) = (a*b) • A02.commutator X Y := by
   simp [A02.commutator, smul_smul, smul_sub, mul_comm]
 simp only [dGamma, hl, hr, hs, Ch04.bilinear_commutator, smul_sub, smul_smul]
 simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
   Finset.sum_sub_distrib]
 have hf (p k : ι) :
   (∑ q, ∑ l, if k=q then (A p k * B q l) • Ch04.hopping p l else 0) =
   ∑ l, (A p k * B k l) • Ch04.hopping p l := by
   rw [Finset.sum_comm]
   simp
 have hg (p k : ι) :
   (∑ q, ∑ l, if p=l then (A p k * B q l) • Ch04.hopping q k else 0) =
   ∑ q, (A p k * B q p) • Ch04.hopping q k := by
   simp
 simp only [hf, hg, Matrix.sub_apply, Matrix.mul_apply, sub_smul,
   Finset.sum_smul, Finset.sum_sub_distrib]
 apply congrArg₂ (fun X Y : Module.End ℂ (A02.FockSpace ι) => X-Y)
 · apply Finset.sum_congr rfl
   intro p _
   exact Finset.sum_comm
 · calc
     _ = ∑ p, ∑ q, ∑ k, (A p k * B q p) • Ch04.hopping q k := by
       apply Finset.sum_congr rfl
       intro p _
       exact Finset.sum_comm
     _ = ∑ q, ∑ p, ∑ k, (A p k * B q p) • Ch04.hopping q k := Finset.sum_comm
     _ = ∑ q, ∑ k, ∑ p, (A p k * B q p) • Ch04.hopping q k := by
       apply Finset.sum_congr rfl
       intro q _
       exact Finset.sum_comm
     _ = _ := by simp_rw [mul_comm]

/-- The identity matrix lifts to particle number, rather than the Fock identity. -/
lemma dGamma_identity  :
    dGamma (1 : Matrix ι ι ℂ) = Ch04.totalNumber := by
 simp [dGamma, Matrix.one_apply, Ch04.hopping_diagonal, Ch04.totalNumber]

/-- Diagonal matrices lift to occupation-weighted observables. -/
lemma dGamma_diagonal (a : ι → ℂ) :
    dGamma (Matrix.diagonal a) = ∑ k, a k • Ch04.number k := by
 simp [dGamma, Matrix.diagonal_apply, Ch04.hopping_diagonal]

end SecondQuantization
end Bosonize.A04
```
