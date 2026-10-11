# Independent CH11 Phase A interface review — 2026-10-11

Verdict: approved for Phase A interface locking and subsequent Phase B proof work. No unresolved mathematical/interface objection was found in the reviewed final snapshot. This verdict concerns contracts and complete data definitions; all 61 theorem/lemma targets remain unproved single-sorry staging declarations.

Reviewed final source SHA-256:

| File | SHA-256 |
| --- | --- |
| `BosonizeStubs/A04PartitionCombinatorics.lean` | `e946bfcb008176ab178e1959085a42d8f0fd3094a6e7120432b242d6e886c535` |
| `BosonizeStubs/Ch11HaldaneCompleteness.lean` | `dc47b114e7e53dade84084fbca1ad500c6b70b7fc1f785fc42ec6ceff86693fd` |
| `docs/companion/BosonizeStubs/A04PartitionCombinatorics.md` | `1f01badbeadff17cd74f3f25a1667dd347a28a426433b583b2269c7e97ab8d62` |
| `docs/companion/BosonizeStubs/Ch11HaldaneCompleteness.md` | `8a838389c5d8f9e745f7f607b81027070d5e2d3802e03c4d70b163143b836225` |

The reviewer independently read every complete data declaration and all 25 A04 + 36 CH11 target headers against `notes/md/ch11_Haldane_completeness.md`, the partitions/completeness portion of `notes/appendices/a04_density_partitions_and_sugawara.md`, the TOC, formalizer source-contract/proof-design instructions, installed partition/sort APIs, and the relevant completed CH07/CH09/CH10/A03 contracts. Historical proof-suggestion review entries remain advisory. Suggested stub/proof directories do not exist in this checkout.

## Carrier and constructive counting audit

`EnergyConfigurations` is the actual fixed-charge/fixed-excitation occupation subtype on the frozen signed momentum band. `displacementParts` preserves multiplicity and removes only zero natural displacements. CH07 establishes nonnegativity, monotonicity and the excitation sum of the integer displacements. The separately defined intrinsic partition weight avoids importing an unproved energy equality into complete data.

`FitsRectangle` correctly bounds the number of positive rows and every column length. The upper displacement target agrees with the finite rectangle width `2*h-S.card`; the empty occupation has no displacement index. Zero-padding occurs before the ascending part list. Padding monotonicity and sum are unconditional identities; length requires the row certificate. `padded_displacement_recovery` explicitly restores every omitted zero row and states equality of the full ascending lists.

The inverse is actual occupied band labels `-h+1+i+d_i`, selected from the real band. The in-band, strict-monotonicity, cardinality, charge, sorted-label, energy and both inverse contracts are explicit. `rectangle_equiv` and `unrestricted_equiv_r1` characterize both forward parts and inverse occupations, so an unrelated equivalence or a bare cardinality certificate cannot satisfy the stated target. `energy_space_finrank_coordinates` addresses the genuine coordinate span; the R1 count subsequently requires the actual equivalence.

R1 is exactly `K <= min(h+N,h-N)`. Admissibility legitimizes both natural rectangle dimensions. Positive parts establish part count <= K and each part <= K. At `N=-h` or `N=h`, R1 forces K=0: the inverse then gives the empty or full occupation, respectively. For arbitrary admissible N, the unique zero partition gives the real sector ground. These cases include zero occupied rows and do not require a positive row count.

A separate scratch feasibility probe compiler-checked positivity/cardinality, sorted padded displacements, strict integer labels, in-band reconstruction, exact inverse cardinality/charge, and sorted recovery using installed `Finset.orderEmbOfFin_unique`, with permitted standard axioms only. It does not establish the final staging inverse/energy targets or the full equivalence.

## Density states, Gram and basis audit

`creatorWord` is a written-order product of CH09's actual density endomorphisms, applied to CH07's actual admissible ground ket. The rightmost factor acts first. Descending sorted partition parts merely fix a representative; permutation invariance comes from global commutativity of nonnegative current shifts. The permutation/erase targets allowing zero natural parts remain valid, since zero shifts also commute; Gram targets correctly require positive parts.

Exact energy membership follows from actual current grading, not a surrogate coordinate-state definition. `hallFactor` is precisely the product of `m^(multiplicity) * multiplicity!`; the recurrence and strict positivity contracts are correct, including empty parts with factor one.

The actual pull-through invariant uses the right remainder `parts.sum`: `n+parts.sum <= K`, `m <= K`, and R2 give `m+n+parts.sum+|N| <= 2K+|N| <= h`. `remainder_ccr` applies the commutator to that remainder state. `lowering_cons` uses `[rho(-m),rho(n)]`, giving positive `m` on the diagonal. No condition is imposed on the already traversed left prefix. Occurrence-index contraction retains multiplicity, and the erased-list formula consolidates the same matching occurrences. Ground annihilation is independently available in CH09.

The left-creator transfer matches the actual Hilbert adjoint `rho(m)^dagger=rho(-m)`. Ground normalization/nonzero evidence is the real occupation ket: completed `A02.ket_inner` and `Ch07.ground_ket_ne_zero` apply, including h=0 for the normalization target. Gram/completeness statements require h>0. Positive-energy ground orthogonality is supported by exact coordinate energy grading.

R2 is exactly `2K+|N| <= h`; it implies the stated R1 bound and holds monotonically for all lower energies. Neither Gram, dimension, linear independence nor spanning is assumed as a hypothesis of the final claims. Both basis theorems are existential proof targets with vector equations identifying every basis vector with the actual density state. There is no basis-valued data definition resting on a sorry membership certificate.

`BudgetPartitions` is the dependent energy/partition index over energies 0 through K. This preserves energy compatibility; different-energy blocks are orthogonal, and the zero-energy block is the ground. The budget Gram, membership, independence and spanning contracts correctly target CH07's whole budget. No CH12/Sugawara work is included.

## Independent elaboration and data audit

An independent source/companion script counted 25 + 36 targets and 7 + 8 complete data/abbreviation declarations. Every final target has exactly one `by sorry`; all 61 exact signatures occur in the corresponding companion. Final source hashes agree with the companion snapshots.

The reviewer independently ran `lake env lean /tmp/Ch11IndependentDataAudit.lean` against the freshly built final modules, exit 0. All 15 complete data declarations were individually inspected with `#print axioms`; every dependency list contains only a subset of `propext`, `Classical.choice`, `Quot.sound`. None contains `sorryAx` or an added axiom.

The drafting agent's final `/tmp/Ch11PhaseABuild.log` was inspected: the targeted build completed successfully (3396 jobs) with expected staging sorry warnings. Native MCP diagnostics were reported by the drafting agent as complete empty CH11 error diagnostics; the independent reviewer did not repeat that MCP call. Build success and data audit do not prove any of the 61 target claims. Phase B still must supply all proofs; Phase C still requires zero placeholders, permitted theorem dependency axioms, warning-free verification and promotion checks.

No guarded Lean source, Core source, or lock manifest was edited by this reviewer. This report is the only repository file written by the independent review.
