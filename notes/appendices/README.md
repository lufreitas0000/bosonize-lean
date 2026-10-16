# Appendices for the Lean Formalization

Status: Source and proof-suggestion reconciliation completed on 2026-10-09 within the explicit algebraic scope. See the [completion ledger](../../note/notes_review_completion_2026-10-09.md), [proof revision guide](../../note/proof_suggestions_revision_2026-10-09.md), and [adaptive roadmap](../../adaptative_roadmap.md).

The current promoted Core contains 31 locked Lean source files covering Chapters 1–18 and implemented supporting portions of Appendices A01–A07 and A10. The CH19/A08 development is Phase-B complete but not promoted to Core. A08 state and formal-vertex constructions remain staged or specified; A09 duality/spin/Umklapp topics are manuscript targets, not promoted Lean results. The finite field dictionary in CH14 uses a conditional cyclic criterion; a universal finite field equality from numerical margins alone remains outside the frozen interface. Continuum evaluation and comparisons with finite CAR models are separate extensions. Historical reviews are dated snapshots and do not override current source and machine records.

| Appendix | Subject | Chapters |
| --- | --- | --- |
| [A01](a01_fourier_scalars_and_characters.md) | Fourier characters, scalar assumptions, and isolated normalization | 3, 5, 15–16, 21 |
| [A02](a02_car_hilbert_and_normal_ordering.md) | Hilbert carriers, CAR signs, adjoints, and normal-ordering syntax | 4–6, 8, 13, 17 |
| [A03](a03_energy_budgets_and_filtered_maps.md) | Integer energies, coordinate projections, and intermediate-state budgets | 7–21 |
| [A04](a04_density_partitions_and_sugawara.md) | Truncated shifts, edge formulas, partition counting, and Sugawara | 9–12 |
| [A05](a05_exponentials_klein_and_vertex_scope.md) | Exact finite exponentials, Klein maps, and vertex scope | 8, 13–14, 20 |
| [A06](a06_chiral_fields_and_lattice_kernels.md) | Chirality signs, gradients, zero modes, and exact lattice kernels | 15–16 |
| [A07](a07_interactions_and_bogoliubov.md) | Interaction domains, quadratic models, and scalar diagonalization | 17–18 |
| [A08](a08_states_and_correlations.md) | State existence, positivity, finite contractions, and asymptotics | 19–20 |
| [A09](a09_duality_spin_and_umklapp.md) | Duality domains, spin/charge constraints, and Umklapp shifts | 20–21 |
| [A10](a10_discrete_rg_and_schrieffer_wolff.md) | Discrete energy shells, Schrieffer-Wolff perturbation theory, and RG context | 17–18, 21 |

The book includes all ten appendix topics. Promoted supporting implementations currently include A01 Fourier, A02 CAR, A03 budgets, A04 currents/partitions/Sugawara, A05 exponentials/Klein/conditional fields, A06 Chapters 15–16 support, A07 interactions/Bogoliubov, and A10 discrete Schrieffer--Wolff algebra. A08 and A09 are included for pedagogical coverage with their staging or manuscript status stated explicitly. Appendix inclusion is not itself a proof or promotion signal.
