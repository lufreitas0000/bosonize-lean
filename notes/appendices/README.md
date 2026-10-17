# Appendices for the Lean Formalization

Status: Source and proof-suggestion reconciliation completed on 2026-10-09 within the explicit algebraic scope. See the [completion ledger](../../note/notes_review_completion_2026-10-09.md), [proof revision guide](../../note/proof_suggestions_revision_2026-10-09.md), and [adaptive roadmap](../../adaptative_roadmap.md).

Current status (2026-10-17): 34 frozen Core files cover CH01–20 within their reviewed scopes and implemented support. CH19/A08 (62 contracts) and finite CH20 (64 contracts) are Phase C complete. CH20b is the working label for the open Chapter 20 completion bridge, not another numbered chapter. CH21 has an R&D proposal but no accepted Lean interface. Polynomial CCR, formal-series results and finite CAR comparisons remain distinct. The book master includes CH01–21; manuscript inclusion does not imply proof acceptance. The CH14 field criterion remains conditional on cyclicity, full ground equality and common residual recurrences.

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

The book includes all ten appendix topics. Promoted supporting implementations currently include A01 Fourier, A02 CAR, A03 budgets, A04 currents/partitions/Sugawara, A05 exponentials/Klein/conditional fields, A06 Chapters 15–16 support, A07 interactions/Bogoliubov, and A10 discrete Schrieffer--Wolff algebra. A08 oscillator-state support is promoted; remaining A08/A09 vertex, comparison and spin/Umklapp topics retain their explicitly open status. Appendix inclusion is not itself a proof or promotion signal.
