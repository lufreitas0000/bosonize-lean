# A06ChiralFields: Phase B complete

Status: Phase B complete; all 16 contracts proved and freshly audited.
Phase C has not started; the module remains in staging.
Current source SHA-256: `daffa052dbd46a919a001b086804af1cb8b2182c5322a20d4f8581c4a131d603`.

Local proof disposition, independent review, runner acceptance and final evidence:
[Phase B validation](../../../note/ch15_phase_b_validation_2026-10-13.md).
Only proof bodies changed; the reviewed interfaces, source notes and Core remain frozen.

## Historical Phase A snapshot

The following baseline and browser design record describes Phase A before these
proofs were completed. Its unproved-status statements are historical and are
superseded by the Phase B status and validation above.
Source: [A06ChiralFields.lean](../../../BosonizeStubs/A06ChiralFields.lean).
SHA-256: `f65574faa2ee8591476c1a9c9a9dba634aa4bd82397e0bd277c1d027f9aaafa1`.

Independent reviewer `/root/ch15_independent_review` approved the exact staged
source and its mathematical scope on October 13, 2026. The browser artifact
was accepted at commit 0d19c9d (response hash
`a991716358c7a3f3757678c7223370782c4bf6466842f380b1fb54779f897455`).
The original artifact is retained at docs/webllm/drafts/ch15_phase_a.md.

This module has 13 complete data declarations and 16 one-sorry stubs.
Fresh elaboration passes with only expected theorem-placeholder warnings. The
data audit uses freshly built staging imports and only standard axioms; no
data depends on sorryAx. Core's 23 existing complete-source hashes are unchanged.
The reviewed interface lock adds only A06/CH15 entries; prior records are unchanged.

See [independent review](../../../note/ch15_phase_a_independent_review_2026-10-13.md),
[data audit](../../../note/ch15_phase_a_data_axiom_audit_2026-10-13.json), and
[oracle report](../../../note/ch15_phase_a_oracle_2026-10-13.json). Numerical
CAR checks are sanity evidence, not general proofs. Witness statements remain
unproved until Phase B, as do every new theorem contract.

The A06 batch precedes CH15. The proof-only importer requires complete target
files and immutable headers/data/context. Real candidate staging sources are
compiled into a fresh temporary olean overlay; Core/cache inputs are reused only
from the matching primary baseline. No candidate proof is written to the primary
compiler cache. After A06 completes, prepare a fresh packet for the seven CH15
contracts using that actual proved support checkpoint.

## Browser design and review obligations

The following text preserves the browser proposal history. Its statement that
elaboration was not performed refers to the browser response, and is superseded
by the local compiler/data-audit evidence above. The 23 proof bodies remain unproved.


**Carriers and imports.** `import Bosonize` is the only import. `σ` has precisely the `Fintype` and `LinearOrder` instances required by multispecies A05; no new representation of currents, CAR, charge, or Fock states is postulated. `Branches σ` supplies concrete indices and a proof of inequality. The field and its exact difference expansion are ambient `Module.End ℂ (A05.FockSpace σ h)` values. `LinearMap.adjoint`, rather than an assumed `StarRing` operation on a hypothetical operator algebra, is the actual Core adjoint API. `ζ` is a complex scalar input; results requiring conjugation or Fourier orthogonality assume `IsPrimitiveRoot ζ (2*h)`. The actual phase dictionary is not identified with `Ch14.wPlus/wMinus`, which are compressed, integer-coordinate, species-specific constructions.

**Operator order, budgets and normalizations.** The rightmost current in `ρ_-m`/`ρ_m` expressions acts first. A product of two terms can raise an input from global cutoff `K` to `K+2M`, so the contracted central term uses the sufficient per-species condition `2M+K+|Ns ν|≤h`. In the same-species transport lemma, this is sharpened to `|m|+|n|+K+|Ns ν|≤h`, mirroring `Ch10.rho_signed_ccr`. The Core statement is originally on `Ch07.fixedBudget`, not on joint vectors, hence the joint lemma is a genuinely new obligation: use `A05.rho_tensor`, finite occupation/tensor decomposition and the actual definition of `Ch07.speciesBudget`. `A05.rho_cross_commute` proves the cross terms globally without a margin; `A05.rho_adjoint` and `A01.complex_character_conj` handle Hermiticity globally. No composition is compressed or silently projected onto the input budget.

For positive `m`, the `ρ_-m,ρ_m` term contributes `+m` while `ρ_m,ρ_-m` contributes `-m`. The two minus signs (from the expansion and `i²=-1`) yield exactly `(χ_{ηm}(x-y)-χ_{-ηm}(x-y))/m` for the same branch; there is **no** extra factor of `i`, `2` or `1/(2h)` in `S_M`. Summing the two opposite branches gives `2 S_M` in the mixed commutator, with a **zero** sum in each self-commutator. The `1/(2h)` occurs only in `δ_M`. The source's `2i C(x,y)` is consistent only when `ζ` is the canonical exponential root and `C=∑_{m=1}^M (2/m)sin(2πm(x-y)/(2h))`; it is not an arbitrary-root characterization.

**Periodicity and source/target signatures.** `latticeCharacter` uses residue representatives; root primitivity makes the representative-independent Fourier laws available. `integerLift` requires a proved period-`2h` lemma and is not the definition domain of fields. `opForwardDiff` needs only additive subtraction; its summation theorem additionally needs `[NeZero (2*h)]` for a finite spatial sum. It uses no commutative multiplication on endomorphisms. Its exact field formula multiplies each nonzero retained current by `ζ^(±ηm)-1`; no purported exact proportionality to a uniformly normalized charge density is present. The `dirichletKernel` diagonal is `(2M+1)/(2h)`; its spatial average is `1` when the only retained multiple of `2h` is `0`. The no-alias bound supplies this restriction and separates nonzero positive/negative modes.

**Non-vacuity.** A05 already supplies `ground_mem_budget` and `ground_ne_zero` under admissibility; the proposed `admissible_ground_nonzero` restates the existence in the actual joint carrier. `concrete_two_branch_parameters` asks for a genuine constructive example over the existing `Fin 2` species: candidate parameters are `h=4`, `M=1`, `K=0`, zero charges and the two distinct `Fin 2` indices, with `2≤4`, `2<8`; admissibility and the remaining predicates must be checked in Lean. The obstruction theorem applies to this nonzero ground witness, not merely to a possibly zero budget space. The zero-mode contradiction only rules out nonzero multiples of **unsubtracted** `δ_M`; a zero-average kernel or spectral derivative is not ruled out.

**Adopted/adapted/rejected.** Adopt the A06 orientation reversal, exact finite character sums, separate cutoff, bounded current actions, and exact periodic differences. Adapt the original abstract Hilbert-space and informal `star` proposals to `A05.Operators`, `LinearMap.adjoint`, actual species and `ZMod (2*h)`. Reject identical-chirality cancellation, an opposite-sign CCR for unmodified identical currents, a global scalar current commutator, arbitrary-root sine formulas, commutative `Ch02.forwardDiff` on endomorphisms, and the exact unmodified delta-gradient identity. The cited CH14 Phase C status is restricted to its conditional theorem; CH16 square/Hamiltonian/error statements are excluded entirely.

## Review obligations

1. **Elaboration (not performed here).** Run the packet's `scripts/webllm/verify_phase_a.py` locally on the candidate, under the pinned Lean toolchain; check namespace lookup, complex integer casts, `ZMod` coercions, `LinearMap.adjoint` inferred Hilbert structures, endomorphism scalar multiplication, `Finset.Icc` indexing, finite `ZMod` enumeration and `autoImplicit=false`. Confirm data-axiom audit and the exact one-sorry stub format. No successful build, test or axiom audit is asserted here.
2. **Current transport.** Prove `joint_signed_current_commutator` on all elements of the **actual** `jointBudget`, not just pure product kets; provide the finite spanning/decomposition bridge from the single-species `Ch10.rho_signed_ccr`. Show explicitly that the species and charge preserved by each current match the margin actually stated, and that zero vectors do not hide a failed theorem.
3. **Algebraic audit.** Independently expand both mixed current orderings with `schwingerCoefficient` (coefficient `-m` for `[ρ_m,ρ_-m]`) and verify the `i²` sign, `1/m` weight, opposite spatial orientations, field normalization and the direction `x-y`. Demonstrate the two self-commutators vanish **on the same input** with both branch margins. Give explicit small-sector calculations or an independent algebraic check, not a global CCR assumption.
4. **True adjoints.** Check `A05.rho_adjoint`, `A01.complex_character_conj` and the conjugation of `i/m` in the full ambient endomorphism, including negative orientation. Avoid translating Hilbert adjoints to `star` without an existing compatible instance.
5. **Finite witnesses and bounds.** Prove a concrete `Fin 2` pair, admissibility at `Ns=0`, actual membership/nonzeroness of `A05.groundKet`, and all margins for `h=4,M=1,K=0`; if any candidate fails, replace it with a proved explicit choice rather than retain a vacuous existential. Confirm `2M<2h` as sufficient for Fourier nonaliasing and note that the CCR margins are stronger.
6. **Character and delta sums.** Check representative independence, spatial translation `x+1`, roots of unity for negative integers, diagonal cardinality `2M+1`, finite orthogonality and `∑_y δ_M(x,y)=1` for **arbitrary** primitive `ζ`. The sine formula is a separate possible canonical-root theorem, not part of the present claims.
7. **Zero-mode contradiction.** Establish `∑_y Δθ(y)=0` in the ambient additive operator group; commute the finite sum past the commutator action in the stated order, and use `∑_y δ_M(x,y)=1`, `c≠0` and the proved nonzero ground ket. Explain why the result does not prohibit a zero-mode-subtracted target kernel. Check exact difference multipliers rather than replacing them by derivatives.
8. **Boundary of scope.** Review whether the choice of spatial orientation really represents the desired physics without modifying the already fixed current/sea convention. No unconditional CH14 physical-field/vertex identification, CH16 normal-ordering/Hamiltonian construction, infinite-volume limit, Fourier sawtooth, or RG estimate can follow from these declarations alone. Subsequent independent mathematical review and local Core-compatible elaboration must precede staging and locking.


Phase B finish evidence: `note/webllm/ch15/phaseB-ch15_cycle_b_ada86a7d.md`.
