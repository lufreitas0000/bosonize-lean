## How to use this context

This packet supplies the API of all 23 currently frozen Core modules, with selected
complete proofs for the budget, tensor and character bridges. Check the exact local
variables, sections, instance assumptions and namespace around each declaration.
The excerpts preserve their original source order; the omitted bodies do not turn
these references into additional hypotheses. Only the A06 target is editable.
Mathlib is imported through `Bosonize`; its entire source library is not included.

A browser without Lean can still construct candidate proofs for the local verifier.
Do not claim compilation until real diagnostics are supplied. Work through the
clusters below within this conversation, retaining completed candidate bodies;
only submit the final JSON once all 16 bodies are complete. If blocked, provide
attempted Lean code, the exact remaining mathematical step and missing API, rather
than merely repeating the task. A partial draft is discussion material, not an
acceptable importer response. Do not weaken statements or invent theorem names.

## Obligation coverage and construction order

| A06 obligation | Existing API and required construction |
| --- | --- |
| `forward_diff_add` | Unfold the additive difference; use additive group identities. No multiplicative commutativity of operators is needed. |
| `forward_diff_smul` | Unfold the difference and distribute scalar multiplication over subtraction. |
| `integer_lift_periodic` | Integer casts into `ZMod (2*h)` kill the modulus, including h=0; this theorem has no NeZero hypothesis. |
| `forward_diff_sum_zero` | Translation x ↦ x+1 is a permutation of the finite ZMod type; reindex the sum, then subtract equal sums. |
| `skew_kernel_diff_sum_zero` | Apply the previous theorem directly to the complex-valued function y ↦ skewKernel h M ζ x y. |
| `admissible_ground_nonzero` | Use A05.ground_mem_budget and A05.ground_ne_zero with the same groundKet. |
| `concrete_two_branch_parameters` | Construct h=4, M=1, K=0, Ns=0, rightSpecies=0 and leftSpecies=1 in Fin 2. Unfold A05.admissible and Ch07.admissible, branchMargins and marginAt; discharge arithmetic and use the two ground lemmas. |
| `lattice_character_conj` | A01.complex_character_conj at the integer representative x.val; latticeCharacter is defined by integerCharacter. |
| `lattice_character_shift` | Identify latticeCharacter with residueCharacter at k cast to ZMod; A01.residue_character_int_cast and residue_character_add_right handle wraparound at x+1. |
| `chiral_adjoint` | LinearMap.adjoint is a conjugate-linear equivalence. Distribute across finite sums and subtraction with map_sum/map_sub, and across scalars with map_smulₛₗ. Use A05.rho_adjoint and the character conjugation; conjugate I/m as well. |
| `chiral_forward_diff` | Distribute the difference over the finite sum and scalars; apply lattice_character_shift and factor the character coefficient minus itself. |
| `dirichlet_diagonal` | At x=y=0 every character is 1, even without root primitivity. Count the integer interval [-M,M] and simplify the normalization. |
| `dirichlet_spatial_sum` | Reindex y ↦ x-y; rewrite each character as residueCharacter at the integer mode cast to ZMod. Apply A01.character_sum. The bound 2*M<2*h ensures every mode in [-M,M] that casts to zero is literally zero. Sum the single zero-mode contribution and cancel 2*h. |
| `chiral_cross_commute` | Expand finite sums/scalars/subtractions using the definition of A02.commutator and bilinearity of endomorphism composition. Apply A05.rho_cross_commute using branches.distinct to all four mode pairings. |
| `joint_signed_current_commutator` | Use the actual coordinate-space span, occupation factorization, nonnegative species energies and A05.rho_tensor to transport Ch10.rho_signed_ccr; see below. |
| `chiral_same_commutator_on_budget` | After the joint CCR bridge, expand the double finite sum. For positive retained m,n, equal-sign current pairs give zero and opposite-sign pairs survive only at m=n. Apply the uniform margin to every pair; simplify I²=-1, positive-mode denominators and residue-character products to the orientationSign times skewKernel in direction x-y. |

## Critical joint-budget bridge

`Ch07.speciesBudget h Ns K` is `A03.coordinateSpace` on configurations with
all species charges fixed and **total** excitation ≤ K. It is not a Cartesian
product of independent species budgets. A03.coordinateSpace is a span of allowed
occupation kets; use Submodule.span_induction for the action identity.

For an allowed configuration S, set Ss η := Ch07.speciesConfiguration h S η.
Ch07.excitation_nonneg h hh (Ss η) holds for every species. The finite sum definition
of Ch07.totalExcitation therefore bounds each excitationEnergy h (Ss ν) by K.
Ch07.ket_mem_fixed_budget places A02.ket (Ss ν) in the single-species fixedBudget
at charge Ns ν and cutoff K. Apply Ch10.rho_signed_ccr with the exact hmargin.

A05.tensor_kets and A05.joint_species_configuration factor A02.ket S.
Apply A05.rho_tensor twice to each ordered product. Composition applies the
rightmost current first; do not require its intermediate vector to remain in the
original input budget, since the single-species commutator theorem already handles
that product at its stated margin. Use the definition of tensorVector and finite
product distributivity, or prove local multilinearity facts, to transport the
single-species action equality and its scalar to the joint ket. Extend using
linearity to zero, sums and scalar multiples in the span induction.

The existing complete A05.rho_budget_map proof illustrates this exact span and
factorization pattern. It also selects the product DecidableEq instance locally
when necessary: follow its stored coordinate-budget instance rather than silently
assuming all definitional equality decisions agree. No global admissibility or
r2 hypothesis is available in the target; do not use partition_spanning to introduce
those stronger hypotheses. The occupation-ket span is sufficient.

## Signs, witnesses and remaining limits

Ch10.schwingerCoefficient m n is -m when m+n=0. Thus [ρ_-m,ρ_m] contributes +m
and [ρ_m,ρ_-m] contributes -m. Conjugation changes both the root character and I.
The A06 same-branch kernel has no extra I, 2, or normalization 1/(2*h).
The Dirichlet kernel alone carries the 1/(2*h) normalization.

The full Core API is supplied to avoid missing project definitions and theorem
signatures. This does not guarantee proof success or provide all Mathlib source.
Compiler feedback remains necessary to resolve elaboration and tactic issues;
no claim that the 16 A06 statements have been proved follows from this context.
