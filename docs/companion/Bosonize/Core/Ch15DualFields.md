# Ch15DualFields: Phase C complete and frozen

Status: Phase C complete; all 7 contracts are proved, audited, promoted and frozen.
Independent pedagogical review and runner acceptance passed; promotion commit `4f526ec`.
[Final Phase C validation](../../../../note/ch15_phase_c_validation_2026-10-13.md).
Verified Phase B source SHA-256: `e6863de5211ac488eaf35b3b1afec0168192d5dce585c04c9350fc15a006edf5`.

Local proof disposition, independent review, runner acceptance and final evidence:
[Phase B validation](../../../../note/ch15_phase_b_validation_2026-10-13.md).
Phase B changed only proof bodies and preserved reviewed interfaces, source notes
and prior Core. The separately authorized completed Phase C migration is described below.

## Verified construction and declaration mapping

The mathematical explanation is in [Chapter 15's constructive realization](../../../../notes/md/ch15_dual_fields.md#constructive-realization-in-lean).
`phiField` and `thetaField` are the ambient sum and difference of the two
oriented A06 fields on the actual A05 occupation Hilbert space. All seven
declarations below were proved in Phase B; their frozen hypotheses remain intact.

| Declaration in `Bosonize.Ch15` | Pedagogical topic | Checked proof mechanism |
| --- | --- | --- |
| `phi_adjoint` | 15.1 Hermiticity and 15.2 dual fields | Distribute the actual conjugate-linear adjoint over addition and use both A06 chiral adjoints. |
| `theta_adjoint` | 15.1 Hermiticity and 15.2 dual fields | Distribute the actual adjoint over subtraction and use both chiral adjoints. |
| `phi_self_commutator_on_budget` | 15.2 self-commutator cancellation | Expand four operator brackets; cross-species brackets vanish globally and opposite oriented kernels cancel on the same budget input. |
| `theta_self_commutator_on_budget` | 15.2 self-commutator cancellation | Use the signed four-term subtraction expansion and both branch margins on the same input. |
| `mixed_commutator_on_budget` | 15.2 mixed kernel | Four-term bilinearity and the opposite branch kernels give exactly 2 S_M(x,y). |
| `mixed_forward_diff_on_budget` | 15.3 exact gradient | Subtract mixed identities at y+1 and y; linearity gives exactly 2 Δ_y S_M. |
| `zero_mode_obstruction_on_ground` | 15.3 periodic zero-mode obstruction | Sum the action-valued commutator difference to zero, sum the assumed Dirichlet identity to c times the actual ground ket, and contradict c≠0 and ground nonzeroness. |

The two self and mixed budget identities retain both species margins,
`2M+K+|Ns ν|≤h`, and the same input vector throughout. Their frozen contracts
also retain hM and no-alias hypotheses although their proofs need fewer
assumptions. The zero-mode proof uses A06's periodic additive difference and
Dirichlet normalization directly; it does not require the mixed CCR theorem.
It excludes nonzero multiples of the unsubtracted kernel, leaving a zero-average
replacement outside that contradiction. The finite algebraic claims provide
no unconditional physical-vertex identification, analytic continuum limit,
CH16 Hamiltonian or normal-ordering identity.

## Completed promotion and audit boundary

Promoted source: [Core CH15](../../../../Bosonize/Core/Ch15DualFields.lean).
Verified promoted-source SHA-256 after the reviewed import substitution:
`30880501f9f71594b9e1cc0af6784428cbc0d48c6e70c8930c5d2c27caa9ff85`. This matches the actual promoted source and complete-source lock.
The exact accepted import substitution is
`import BosonizeStubs.A06ChiralFields` → `import Bosonize.Core.A06ChiralFields`.
A06's `import Bosonize` is expanded to the 23 prior Core imports to avoid a
cycle through the promoted aggregator. Every non-import source byte is preserved,
including both field definitions and all seven proof bodies. The scoped interface
migration preserves theorem-header and non-import command hashes and updates
only the reviewed import/context records; all prior Core hashes remain intact.

The [Phase B validation](../../../../note/ch15_phase_b_validation_2026-10-13.md)
records nine freshly audited CH15 declarations and 29 in its A06 dependency,
all with only `propext`, `Classical.choice`, and `Quot.sound`, zero placeholders
and zero target warnings. It also records the independent proof review and
runner acceptance/push. Fresh promoted compilation and axioms, scoped lock migration, independent
pedagogical review and Phase C runner acceptance all passed. The final validation
records actual outputs, the exporter CI repair and unchanged prior Core hashes.

## Historical Phase A snapshot

The following baseline and browser design record describes Phase A before these
proofs were completed. Its unproved-status statements are historical and are
superseded by the Phase B status and validation above.
Current successor source: [Ch15DualFields.lean](../../../../Bosonize/Core/Ch15DualFields.lean).
The following SHA-256 belongs to the original staged Phase A snapshot.
SHA-256: `778a972ff2cd909c25e83f4f6e266af2ddacfee2d71d150391549a3c0e38d903`.

Independent reviewer `/root/ch15_independent_review` approved the exact staged
source and its mathematical scope on October 13, 2026. The browser artifact
was accepted at commit 0d19c9d (response hash
`a991716358c7a3f3757678c7223370782c4bf6466842f380b1fb54779f897455`).
The original artifact is retained at docs/webllm/drafts/ch15_phase_a.md.

This module has 2 complete data declarations and 7 one-sorry stubs.
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


[Phase B runner finish evidence](../../../../note/webllm/ch15/phaseB-ch15_cycle_b_ea374fc9.md).


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


Phase C finish evidence: `note/webllm/ch15/phaseC-ch15_cycle_c_463e5816.md`.


Final promoted-source and workflow evidence: [Phase C validation](../../../../note/ch15_phase_c_validation_2026-10-13.md).
