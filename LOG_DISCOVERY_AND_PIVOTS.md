# Journal of Discoveries, Proof Obstructions & Pivots

This journal preserves critical formalization insights for `bosonize-lean`. Whenever a proof strategy fails, a representation encounters a bottleneck, or a design pivots, document it here immediately before changing definitions.

---

## Log Entries

| Date | Context / Target Lemma | Obstruction / Bottleneck | Resolution / Architectural Pivot |
| :---: | :---: | :--- | :--- |
| 2026-10-11 | Strategy Alignment | Multi-agent orchestration failure modes | Adopted strategy v2: CI gates, locked statements, and independent Skeptic audit |
| 2026-10-11 | CH12 physical energy sectional proofs | Initial scratch elaboration could not cast folded relativeCharge; physical sea energy and seaEnergy remained syntactically different; sum grouping blocked add_smul rewrite. | Preserve all interfaces; explicitly unfold charge for the cast, normalize seaEnergy, and reassociate before combining scalar actions. |
| 2026-10-11 | CH12 `positive_word_weight`, word cluster | First compiler pass reduced the induction step to `parts.sum + n = n + parts.sum`; an explicit `Finset.sum_ite_eq'` simp argument was redundant. Arbitrary-natural-list pull-through, including zero entries, elaborated without errors. | Normalize the final scalar addition with `Nat.add_comm` and remove the redundant simp argument. No interface, data or Core change. |

| 2026-10-11 | CH12 energy action and witnesses | Exact Core API uses implicit partition energy; unfolding the vacuum leaves the sea-ket abbreviation | Remove the extra energy argument and close the definitional sea equality with `rfl`; preserve frozen contracts |

| 2026-10-11 | CH12 staging aggregator CI | Lean rejects the new import after the aggregator module documentation command | Move the import into the initial import block, then rerun full CI; chapter interface unchanged |
