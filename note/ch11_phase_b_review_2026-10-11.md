# Chapter 11 Phase B independent review — 2026-10-11

## Scope and status

Independent review of the actual-current Gram proof cluster, the ten downstream Chapter 11 completeness/basis proof bodies, and the proposed joint A04/CH11 Phase C migration. Review performed read-only in the repository; proof feasibility and compilation checks used `/tmp` scratch sources.

## Actual-current Gram cluster: PASS

The reviewed and compiler-checked chain uses the actual `Ch09.rho` operators and `Ch07.groundKet` on the finite fermionic Fock carrier. It does not assume a global scalar CCR, Gram orthogonality, or bosonic completeness.

The pull-through induction attaches the commutator margin to the actual right remainder: a head creator n and remaining word energy E satisfy n+E≤K; the lowering mode satisfies m≤K. Hence m+n+E+|N|≤2K+|N|≤h. Both occurrence-indexed contractions and the consolidated count/erase formula are proved. The latter feeds the actual Hilbert adjoint recursion. The Hall normalization is the exact finite product of mode powers and multiplicity factorials, and its positivity is proved.

Completed frozen declarations: `remainder_ccr`, `right_remainder_margin`, `lowering_cons`, `lowering_through_word`, `lowering_through_word_erase`, `word_inner_cons`, `ground_inner_word_zero`, `ground_inner_ground`, `hall_factor_positive`, `hall_factor_cons`, `word_gram`, and `partition_gram`.

`lake env lean /tmp/Ch11GramProofs.lean` exited 0 with no warnings in these twelve declarations; other unfinished targets generated their expected placeholder warnings. Combining the completed fourteen basic proofs with this cluster in `/tmp/Ch11GramAudit.lean` exited 0. Fresh `#print axioms` checks of both lowering formulas, `word_gram`, and `partition_gram` reported only `propext`, `Classical.choice`, and `Quot.sound`.

## Downstream Chapter 11 proofs: PASS

Reviewed `partition_state_ne_zero`, `partition_states_linear_independent`, `r2_implies_r1`, `fixed_energy_spanning`, `fixed_energy_basis`, `budget_partition_gram`, `budget_partition_mem`, `budget_partition_linear_independent`, `budget_partition_spanning`, and `budget_partition_basis`.

Nonzero states follow from the positive Hall normalization and the actual Gram formula. Fixed-energy spanning and basis construction use actual-state membership and linear independence together with the A04 configuration/partition dimension theorem; the required R1 margin follows explicitly from R2. Budget Gram equality of dependent partition labels derives equality of their energies from equality of part-multiset sums. Budget spanning assigns each occupation ket its actual nonnegative excitation energy E≤K, applies fixed-energy completeness at E, and embeds its partition labels into the total-budget indexing type.

No weakened conclusions, vacuous substitutions of carriers, circular assumptions, or unjustified global current identities were found. These checks do not waive the requirement that the A04 combinatorial dependencies finish without placeholders before Chapter 11 can be promoted.

## Joint Phase C migration plan: PASS

The reviewed plan moves both staging sources and their companions to Core. The A04 source is preserved byte-for-byte. The only CH11 source substitution changes its appendix import from `BosonizeStubs.A04PartitionCombinatorics` to `Bosonize.Core.A04PartitionCombinatorics`.

Move the corresponding v2 entries by path, preserving every theorem-header hash and every unaffected command hash. Recompute only the affected CH11 import command and dependent context hashes. Preserve all sixteen existing Core source hashes and lock entries; add the two new complete-source hashes. Update both aggregators and move the companions. Do not regenerate the complete baseline. The plan matches `.agents/workflows/freeze_chapter.md`.

Approval of this plan is conditional on complete source proofs, clean fresh builds, only permitted axioms, reviewed pedagogical synchronization, both guards/guard tests, CI, and a committed final checkpoint. At the independent downstream review checkpoint, strict freeze verification passed with 677 statements and 513 commands; this is interface evidence, not proof completion.

## Scoped A04 interface cleanup

**PASS**, following independent review of the concrete `/tmp/Ch11A04Cleanup.lean` diff against `/tmp/bosonize-ch11/A04-before-cleanup.lean`.

The exact delta consists of two lines: removal of `(hh : 0 < h)` from `inverse_displacement_parts`, and removal of its corresponding `hh` argument in `rectangle_equiv`. All other theorem headers, definitions, imports, proof bodies and mathematical conclusions are preserved.

The proof recovers displacements from the inverse configuration's sorted labels and cardinality, identifies its padded row list, and removes its zero rows. These are geometric identities under `rows≤2*h` and the existing rectangle fit; none needs positive h. At h=0 these hypotheses force rows=0 and an empty part multiset, so the strengthened statement includes the consistent empty-band case. Removing a redundant premise therefore preserves the intended inverse identity and eliminates the unused-variable warning without suppressing a linter.

The inverse agent supplied a complete compiler-checked integrated candidate and an all25-target axiom audit with only permitted standard axioms. The root candidate preserves the exact existing proof bodies. Independent compilation with `lake env lean -DwarningAsError=true /tmp/Ch11A04Cleanup.lean` exited 0 with no output, no warnings and no placeholders. Reviewed candidate SHA-256: `7ca50bf6373bef397268ebfe2117df9cf9f9e67eddd4b53ec73e0473deaba399`. Apply only this reviewed header/caller change and update only its affected v2 declaration hash after approval; do not alter other headers or existing Core sources.

## Follow-up Hall recurrence interface cleanup — 2026-10-11

**PASS for the concrete scoped cleanup**, reviewed independently after the cross-review identified an artificial multiply-and-cancel detour in `hall_factor_cons`.

The recurrence `hallFactor (m ::ₘ parts) = m*(parts.count m+1)*hallFactor parts` is a natural-number product identity for every m and every part multiset. Neither `0<m` nor positivity of the preexisting parts is needed. The prior proof consumed those frozen premises by deriving a positive factor and cancelling an unnecessary multiplication. Although logically valid, this obscured the weaker algebraic prerequisites. The reviewed cleanup removes both redundant premises and the detour, retaining the direct finite-product splitting, multiplicity-count and factorial recurrence proof.

The exact `/tmp/Ch11HallFactorCleanup.lean` diff removes only `(hm : 0 < m)` and `(hpos : ∀ n ∈ parts, 0 < n)` from this one header, deletes the detour in its proof, and removes these arguments from the sole `word_gram` caller. Other headers, definitions, imports and proof bodies are unchanged. Its zero-mode/zero-part cases remain valid as product identities; this does not broaden the positive-part hypotheses of actual-current Gram or remove the separate positivity assumptions of `hall_factor_positive`.

Candidate SHA-256: `32f6a628739a0d965300a357116fd059b094082da7d189baeb63b30a3f195014`. The inverse agent's warning-as-error compilation exited 0 with an empty log. Independent `lake env lean -DwarningAsError=true /tmp/Ch11HallFactorCleanup.lean` compilation also exited 0 with no output or warnings. Approval is limited to this exact declaration/caller cleanup and the corresponding one-header v2 lock amendment; mathematical conclusions and existing Core sources remain unchanged.

The cleanup candidate's all36-target fresh axiom audit log was inspected independently: every declaration uses a subset of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or warning appears.

## Actual Phase C source migration verification — PASS

The promoted `Bosonize/Core/A04PartitionCombinatorics.lean` is byte-identical to the approved A04 cleanup candidate, SHA-256 `7ca50bf6373bef397268ebfe2117df9cf9f9e67eddd4b53ec73e0473deaba399`. The promoted `Bosonize/Core/Ch11HaldaneCompleteness.lean` equals the approved Hall-cleanup candidate after exactly the reviewed appendix import substitution, SHA-256 `1d3b1f289ddb0f4dfd43abbe8767c031d30abf3aa17355cb657f4a877b295616`. This exact content comparison preserves every mathematical header, definition and proof body after the two separately reviewed interface cleanups.

All sixteen preexisting Core hashes from checkpoint `0ae13df` are unchanged in the final eighteen-entry Core lock manifest; both new hashes match the actual promoted source bytes. The fresh Core audit contains all 76 declarations with only permitted standard axioms. The final Core and staging builds succeed and the CI log ends `CI OK`.
