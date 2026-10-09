# Proposal for Refactoring Bosonize-Lean Notes

## 1. Core Principles
* **Chapter Numbering Integrity**: The numbering and titling of the main chapters (`ch01` through `ch21`) will remain strictly intact.
* **Content Offloading**: To keep the main chapters lean and focused on physical narrative, any massive conceptual proofs or mathematical blocks (a "whole section worth") will not clutter the main files. They will be offloaded to dedicated `aXX_...` appendix notes.
* **Strict Sequential Freezing**: We will write, verify, and freeze exactly one note at a time. Once a note is frozen, it is never modified again. Chapters will only be updated *after* the appendices they rely on have been fully resolved and frozen.
* **Formal Lean Readiness**: All proofs and constructions will avoid continuous limits, continuous path integrals, or thermodynamic bounds. We will use strict algebraic finite-dimensional structures, discrete umbral operators, and energy budget subspaces to ensure direct translation into Lean 4.

## 2. New Appendix Proposal: `a10_discrete_rg_and_schrieffer_wolff.md`
Based on the `brainstorm.md` discussion, interactions (such as Umklapp scattering and backscattering) cause operations to "leave the budget space" (i.e. jumping to energy levels $K$). A raw projection simply drops these essential loop corrections, leading to false exact fixed lines. 
* **Content**: We will create a new, dedicated appendix formalizing **Discrete Mode Decimation** using the **Schrieffer-Wolff Transformation (SWT)**. 
* **Mechanism**: It will formally define the budget partitioning $\mathcal{B}_K = \mathcal{P} \oplus \mathcal{Q}$, the orthogonal projectors $P$ and $Q$, and the exact unitary rotation $e^S$ that block-decouples the highest-energy subspace *before* projecting. This algebraically replaces analytical RG flow equations with an exact matrix trace projection.

## 3. Sequential Execution Plan
We will iterate through the sequence by ensuring the foundational mathematical appendices are written and frozen first, followed immediately by the chapters that depend on them.

### Phase I: Fourier, CAR, and Budgets
1. **Write/Freeze**: `a01_fourier_scalars_and_characters.md`
2. **Update/Freeze**: `ch03_fourier.md` (Integrates A01)
3. **Write/Freeze**: `a02_car_hilbert_and_normal_ordering.md`
4. **Update/Freeze**: `ch04_CAR_Fock_space.md` (Integrates A02)
5. **Update/Freeze**: `ch06_lattice_AQFT_net.md` (Integrates A02)
6. **Write/Freeze**: `a03_energy_budgets_and_filtered_maps.md`
7. **Update/Freeze**: `ch07_vacuum_budget_space.md` (Integrates A03)

### Phase II: Density Modes and Sugawara Equivalence
8. **Write/Freeze**: `a04_density_partitions_and_sugawara.md`
9. **Update/Freeze**: `ch05_fermions_lattice_band.md` (Integrates A01, A04)
10. **Update/Freeze**: `ch09_density_modes.md` (Integrates A03, A04)
11. **Update/Freeze**: `ch10_Heisenberg_algebra.md` (Integrates A03, A04)
12. **Update/Freeze**: `ch11_Haldane_completeness.md` (Integrates A04)
13. **Update/Freeze**: `ch12_Sugawara_construction.md` (Integrates A04)

### Phase III: Bosonization Dictionary
14. **Write/Freeze**: `a05_exponentials_klein_and_vertex_scope.md`
15. **Update/Freeze**: `ch08_boson.md` (Integrates A02, A03, A05)
16. **Update/Freeze**: `ch13_Klein_factors.md` (Integrates A02, A05)
17. **Update/Freeze**: `ch14_Mattis_Mandelstam_formula.md` (Integrates A03, A05)

### Phase IV: Field Kinematics
18. **Write/Freeze**: `a06_chiral_fields_and_lattice_kernels.md`
19. **Update/Freeze**: `ch15_dual_fields.md` (Integrates A06)
20. **Update/Freeze**: `ch16_field_Hamiltonian.md` (Integrates A06)

### Phase V: Interactions, RG, and Correlators
21. **Write/Freeze**: `a07_interactions_and_bogoliubov.md`
22. **Write/Freeze**: `a10_discrete_rg_and_schrieffer_wolff.md` *(New Appendix handling boundary modes and SWT projectors)*
23. **Update/Freeze**: `ch17_LL_Models.md` (Integrates A07, A10)
24. **Write/Freeze**: `a08_states_and_correlations.md`
25. **Update/Freeze**: `ch18_bogoliubov.md` (Integrates A07, A08, A10)
26. **Update/Freeze**: `ch19_correlations.md` (Integrates A08)

### Phase VI: Duality and Gaps
27. **Write/Freeze**: `a09_duality_spin_and_umklapp.md`
28. **Update/Freeze**: `ch20_CDW.md` (Integrates A05, A08, A09)
29. **Update/Freeze**: `ch21_spinful_models.md` (Integrates A09, A10)

## 4. Updates Inside the Chapters
When updating a specific chapter:
* Existing incorrect hypotheses (e.g. continuum Virasoro algebras or incorrect continuous variables) will be actively deleted and rewritten to use the finite algebraic bounds detailed in the appendices.
* Any massive structural proof will be truncated into a succinct declaration and a reference pointing to the formalized proof in the relevant appendix note.
