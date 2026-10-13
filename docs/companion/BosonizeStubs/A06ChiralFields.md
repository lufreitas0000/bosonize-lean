# A06ChiralFields: Phase C promotion candidate

Status: Phase B complete; all 16 contracts proved and freshly audited.
Phase C promotion candidate prepared; promoted-source build, documentation review
and runner acceptance are pending.
Verified Phase B source SHA-256: `daffa052dbd46a919a001b086804af1cb8b2182c5322a20d4f8581c4a131d603`.

Local proof disposition, independent review, runner acceptance and final evidence:
[Phase B validation](../../../../note/ch15_phase_b_validation_2026-10-13.md).
Phase B changed only proof bodies and preserved reviewed interfaces, source notes
and prior Core. The separately authorized Phase C candidate is described below.

## Verified construction and declaration mapping

The mathematical explanation is in [Appendix A06's constructive realization](../../../../notes/appendices/a06_chiral_fields_and_lattice_kernels.md#constructive-realization-in-lean).
The carrier is A05's actual finite occupation Hilbert space and its ambient
endomorphisms. Spatial coordinates lie in `ZMod (2*h)`. The current identity
acts on the actual total-excitation budget; intermediate vectors need not lie
in that same input budget. All sixteen declarations below were proved in Phase B.

| Declaration in `Bosonize.A06` | Pedagogical topic | Checked proof mechanism |
| --- | --- | --- |
| `lattice_character_shift` | Periodic characters and exact difference | Bridge integer representatives to residue characters, apply the addition law, and normalize the integer cast of 1. |
| `lattice_character_conj` | Periodic characters and adjoints | Apply A01's complex integer-character conjugation at the representative. |
| `integer_lift_periodic` | Periodic spatial carrier | Integer casts into ZMod annihilate the modulus; no positivity hypothesis is required. |
| `forward_diff_add` | Exact additive difference | Expand subtraction and use additive-group identities. |
| `forward_diff_smul` | Exact additive difference | Distribute the complex scalar over subtraction. |
| `forward_diff_sum_zero` | Periodic zero-average obstruction | Reindex the finite sum by the bijection x ↦ x+1. |
| `chiral_adjoint` | Genuine Hermiticity | Use the conjugate-linear adjoint equivalence, A05 current adjoints, character conjugation, and conjugation of i/m. |
| `chiral_forward_diff` | Exact gradient multipliers | Distribute the finite difference and apply the proved character shift; retain each ζ^(±ηm)−1. |
| `joint_signed_current_commutator` | Total budget and tensor transport | Span-induct on occupation kets, bound each nonnegative species energy by total energy, and transport Ch10's signed CCR through a proved linear tensor insertion map. |
| `chiral_cross_commute` | Independent species | Expand all four current pairs and both finite sums; each pair commutes globally by A05. |
| `chiral_same_commutator_on_budget` | Oriented commutator kernel | Explicit four-pair bilinearity, signed CCR on the common input, diagonal collapse, and residue-character differences yield η S_M(x,y). |
| `dirichlet_diagonal` | Finite kernel normalization | Evaluate characters at zero and count the integer interval, yielding (2M+1)/(2h). |
| `dirichlet_spatial_sum` | Zero mode and no aliasing | Reindex y ↦ x−y, use character orthogonality, and use integer divisibility with the absolute-value bound to retain only mode 0. |
| `skew_kernel_diff_sum_zero` | Periodic zero-average obstruction | Apply the proved finite difference sum theorem to the skew kernel. |
| `admissible_ground_nonzero` | Genuine budget witness | Use A05's actual ground ket, budget membership under admissibility, and nonzeroness. |
| `concrete_two_branch_parameters` | Non-vacuous margins | Construct h=4, M=1, K=0, zero charges, and distinct species 0 and 1 in Fin 2; prove every bound and ground condition. |

The same-branch coefficient retains Ch10's −m for [ρ_m,ρ_−m], the
rightmost-first product order, the original margin and x−y kernel direction.
Only the Dirichlet kernel has the 1/(2h) normalization. No analytic limit,
sine characterization for an arbitrary primitive root, square/Hamiltonian
result from the reference appendix, or CH16 result is proved by this module.

## Promotion candidate and audit boundary

Future source: [Core A06](../../../../Bosonize/Core/A06ChiralFields.lean).
Predicted promoted-source SHA-256 after the reviewed import substitution:
`77c579ff06238d2801e9861fdf65c5c1efc66fc31d0161efd18a6a386d2fa768`. This is a pre-acceptance hash, to be checked against the actual promoted file.
The exact promotion substitution replaces A06's `import Bosonize` by the
23 prior Core imports from the reviewed aggregator, avoiding an aggregator
cycle after promotion. CH15's staging A06 import becomes
`import Bosonize.Core.A06ChiralFields`. The proposed migration preserves every
non-import source byte, including all definitions, theorem headers and proofs;
existing Core sources and their complete-source hashes remain unchanged.
The scoped interface-lock migration must preserve theorem-header and non-import
command hashes, with only reviewed import/context records updated.

The [Phase B validation](../../../../note/ch15_phase_b_validation_2026-10-13.md)
records 29 freshly audited A06 declarations, with no placeholders or target
warnings and only `propext`, `Classical.choice`, and `Quot.sound`; `integer_lift_periodic`
and `forward_diff_add` use only `propext` and `Quot.sound`.
Runner acceptance and push of Phase B are recorded there. Fresh compilation
and axiom auditing after the promotion substitutions, scoped lock migration,
independent pedagogical review and Phase C runner acceptance are pending.
This candidate notebook does not claim those Phase C gates have passed.

## Historical Phase A snapshot

The following baseline and browser design record describes Phase A before these
proofs were completed. Its unproved-status statements are historical and are
superseded by the Phase B status and validation above.
Current successor source: [A06ChiralFields.lean](../../../../Bosonize/Core/A06ChiralFields.lean).
The following SHA-256 belongs to the original staged Phase A snapshot.
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

See [independent review](../../../../note/ch15_phase_a_independent_review_2026-10-13.md),
[data audit](../../../../note/ch15_phase_a_data_axiom_audit_2026-10-13.json), and
[oracle report](../../../../note/ch15_phase_a_oracle_2026-10-13.json). Numerical
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
by the local compiler/data-audit evidence above. Its unproved-contract labels describe the historical Phase A snapshot; the
23 proof bodies are now verified by the Phase B evidence above.


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


[Phase B runner finish evidence](../../../../note/webllm/ch15/phaseB-ch15_cycle_b_ada86a7d.md).


## Independent Phase C candidate review

Reviewer `/root/characters` independently approved the exact source/import
migration and the complete five-file pedagogical/document candidate. The original
chapter and appendix are exact byte prefixes, preserving every reference paragraph
and formula. The added mathematical exposition, declaration maps, margins, signs,
nonzero-ground argument, future limitations, predicted source hashes and future
Core-depth links pass review with no findings requiring changes.

Root also checked the formulas with KaTeX 0.16.22 in strict mode: 195 fragments
in the two complete notes, zero errors. The current pre-C repeat compiler audit
of both staging modules passes all 38 declarations with standard axioms only.
These checks precede promotion; final promoted-source gates and acceptance are
recorded separately after the runner completes them.
