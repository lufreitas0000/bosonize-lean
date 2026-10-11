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
| 2026-10-11 | CH13 joint occupation factorization scratch | Configuration union/fiber inverse proofs compile; the generic fiber-membership lemma unnecessarily inherits `[Fintype σ]`, producing an unused-section-variable warning. | Scope `omit [Fintype σ]` to that membership lemma. Keep finite enumeration assumptions only on union and the resulting actual occupation equivalence; no guarded source changes. |
| 2026-10-11 | CH13 algebraic tensor transport scratch | Typed binder notation `⨂[ℂ] (_ : σ), ...` is rejected by the installed PiTensorProduct parser; the dependent ket-image proof then has unresolved module metavariables. | Use the explicit `PiTensorProduct ℂ (fun (_ : σ) => ...)` type and scope the tprod notation according to the installed API before proving the basis image. No statement or carrier change. |
| 2026-10-11 | A05 multispecies lexicographic carrier data | Scratch named def lexOrder triggered class-definition reducibility warning. | Use a complete exported instance on the ordinary product carrier, taking its structure from the definitionally identical lex wrapper; retain actual Ch07 speciesBudget carrier and explicitly state ordering law. |

| 2026-10-11 | CH13 actual species carrier API probe | First scratch import succeeded but short Core namespaces were unresolved outside Bosonize; named class-valued order def also triggered reducibility and local computability diagnostics. | Open Bosonize explicitly and use a complete noncomputable local instance imported from the definitionally identical Lex carrier. No chapter, Core, or lock edits. |
| 2026-10-11 | A05 jointBudget / liftedAnnihilation data elaboration | CH07 speciesBudget abbreviation requires noncomputable; guessed A01.fourierNormalizationComplex name does not exist. | Mark actual-budget alias noncomputable and use installed CH06Ext Fourier normalization API; no carrier/operator changes. |
| 2026-10-11 | CH13 raw-product lex order probe | Lex comparison theorem had unconstrained implicit pair types; actual annihilation ket RHS inferred product DecidableEq while Ch04 uses order-derived DecidableEq, preventing direct exact. | Supply explicitly typed lex pairs and normalize actual operator plus Finset.erase through simp, which removes proof-irrelevant decision-instance differences. |

| 2026-10-11 | CH13 tensor-basis transport scratch | Installed PiTensorProduct basis API reports `Module.Basis.piTensorProduct` unknown despite file-level `open Module`. | Check the exported `Basis` namespace resolution and use the exact installed name; retain complete independently checked configuration equivalence separately. |
| 2026-10-11 | CH13 lex instance diamond | Local LinearOrder on raw product does not override the independently inferred componentwise product LT/LE/DecidableEq; the positive lex ordering goal elaborated with Prod.instPreorder.toLT. | Install local LT/LE/DecidableEq projections from the same complete lex LinearOrder before all definitions and statements; verify comparison and actual annihilation contracts together. |

| 2026-10-11 | CH13 tensor ket image scratch | `change` cannot identify tensor-basis evaluation with pure tprod definitionally. | Use installed propositional lemma `Basis.piTensorProduct_apply` in a simp proof of `Basis.equiv_apply`; no carrier or contract change. |

| 2026-10-11 | CH13 tensor image API scratch | `Basis.equiv_apply` treats basis parameters as implicit; positional supplied bases are read as index argument. | Supply exact named `b`, `b'`, `e` parameters, retain only index positional. |

| 2026-10-11 | CH13 tensor image normalization scratch | Ket-image simp leaves named tensor transport and occupation inverse opaque. | Include their complete definitions in simp-only normalization so `join` and basis transport match; no mathematical change. |
| 2026-10-11 | CH13 current intertwining pre-review | Initial natural-m contract allowed m=0, but rho_0 counts species particles and changes by one under the same-species Klein lowering, so its square cannot commute. | Retain the source's positive-mode scope explicitly with hmpos in raising/lowering intertwining and typed squares; zero-transfer remains a separate number-shift theorem. |
| 2026-10-11 | A05 lexicographic order independent feasibility review | A global product LinearOrder risks leaking ordering to downstream modules; product LT/LE/DecEq can override the intended lexical projections. | Replace the global instance with complete named speciesOrder data and explicit local LinearOrder/LT/LE/DecEq projections in both staging modules, preserving the actual CH07 product carrier. |

| 2026-10-11 | CH13 tensor image inverse reduction | `simp only` leaves coercion of constructed Equiv.symm opaque. | Allow standard simp projection rules along with the explicit transport definitions. |
