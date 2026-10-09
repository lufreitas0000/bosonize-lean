# Appendices for the Lean Formalization

Status: Mathematical and architectural reference inventory, audited and synchronized on 2026-10-09 against the verification record (`note/revision_confirmation_2026-10-09.md`).
The notes delineate verified finite-algebraic identities on energy budget spaces $\mathcal{B}_K$ from abstract operator/state formulations (e.g., abstract Weyl correlators in A08/Ch20 and dual model structures in A09/Ch20) and physical continuum motivations (e.g., KT flow and Umklapp Mott gaps in Ch21/A10). Inclusion in this inventory establishes mathematical specification and interface scoping, serving as an audit baseline prior to formal Lean proof-draft review.

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

Implementation order: A01 → A02 → A03 → A04. Then resolve A05/A06 and choose the quadratic model in A07 before adopting the state and dictionary claims in A08/A09, followed by energy-shell Schrieffer-Wolff methods in A10.
