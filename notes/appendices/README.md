# Appendices for the Lean Formalization

Status: Source and proof-suggestion reconciliation completed on 2026-10-09 within the explicit algebraic scope. See the [completion ledger](../../note/notes_review_completion_2026-10-09.md), [proof revision guide](../../note/proof_suggestions_revision_2026-10-09.md), and [adaptive roadmap](../../adaptative_roadmap.md).

Only Chapters 1–2 have proved, frozen Core implementations. Later notes have explicit targets and proof obligations: the raw quartic includes its exact one-body correction; the abstract state, formal vertices and duality have specified constructions; the finite field dictionary uses a conditional cyclic criterion. A universal finite field equality under numerical margins alone remains a research candidate excluded from freezing. Analytic evaluation and finite-model comparisons are separate extensions. Historical reviews remain dated snapshots.

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

Immediate implementation: read A01 and draft Chapter 3 in Phase A. Then use A02 with Chapters 4–6, A03 with Chapter 7, A04 with Chapters 9–12, and later appendices alongside their dependent chapters. Appendices are supporting obligations, not a requirement to implement all ten before Fourier. Follow the roadmap and chapter A–B–C review gates.
