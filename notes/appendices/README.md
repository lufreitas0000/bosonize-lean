# Proposed appendices for the Lean formalization

Status: mathematical and architectural proposals, 2026-10-08. These notes supplement a full reading of chapters 1–21 and TOC. They are not approved specifications or proved Lean modules. The original chapter notes and suggestion files are preserved. See [the complete audit](../../docs/audit/reference_notes_lean_audit.md) for chapter coverage, equation references, counterexamples, and validation limits.

The immediate recommendation is to adopt Appendix A01 before drafting chapter 3. The remaining appendices address downstream definitions and statements before their interfaces are frozen. A theorem marked false as stated must be repaired mathematically; adding tactics or additional premises that force zero states is not a repair.

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

Proposed order: A01 → A02 → A03 → A04. Then resolve A05/A06 and choose the quadratic model in A07 before adopting the state and dictionary claims in A08/A09. Chapters 1–2 are already frozen and are not reopened by this review.
