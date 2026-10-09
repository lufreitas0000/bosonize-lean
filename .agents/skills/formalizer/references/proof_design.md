# Proof design for Bosonize-Lean

Use this reference for the mathematical contracts that recur across chapters. Exact helper names below are proposals unless verified in the current project. Examples explain how to choose hypotheses; they are not replacements for a chapter's approved statement.

| Task | Read |
| --- | --- |
| Reconcile a chapter with appendices, suggestions, or older reviews | Source contracts |
| Compose budget maps, take adjoints, or prove a vertex formula | Restricted maps and projections |
| Simplify CAR/current products or normal-order words | Noncommutative algebra |
| Choose a current, Gram, or Sugawara margin | Grading and useful hypotheses |
| Define a bosonic form, exponential, or BCH identity | Carriers, pairings, and exponentials |
| Diagonalize a paired Hamiltonian or construct SW coefficients | Scalar matching and SW |
| Define a vacuum, duality, or leakage theorem | Existence and witnesses |

## Source contracts

Read the relevant chapter and its linked appendices using the [appendix index](../../../../notes/appendices/README.md). Read applicable entries in [the proof-suggestion review](../../../../note/proof_suggestions_revision_2026-10-09.md); this dated report records a snapshot, so reconcile it with current source edits. Separate a mathematical statement, a proposed implementation, a compiler result, and a proved declaration.

Before drafting or freezing, identify:

- The ambient carrier, scalar structure, index type, and actual integer momentum labels.
- The operator normalization, commutator order, adjoint convention, and source/target budgets.
- Which assumptions establish existence, which establish an algebraic identity, and which justify a restricted action or a physical interpretation.

Record a contradiction with an explicit example or a missing implication. Preserve the intended claim and propose a repair rather than silently strengthening assumptions. Do not interpret a historical “issue solved” annotation as a Lean proof. When the source changes during review, record the revision/snapshot reviewed and recheck affected conclusions.

## Restricted maps and projections

For typed maps `C : V → W` and `A,B : W → Z`, agreement of A and B on the image of C permits composition. Agreement on V alone does not. For ambient projections, use the exact identity

\[
 P_tABP_s-P_tAP_mBP_s=P_tA(1-P_m)BP_s.
\]

The minimal equality criterion is vanishing of this remainder. `B(source) ⊆ intermediate` is sufficient; annihilation of the escaped component by `P_t A` is another sufficient condition. Avoid demanding that every factor preserve a single cutoff when the theorem only needs this remainder to vanish.

Taking adjoints reverses source/target and factor order. An isometry has an inverse on the target only after surjectivity is established; common basis labels and completeness in both sectors can supply it. A budget isometry does not automatically extend to an ambient unitary.

For a projected vertex identity, match the entire projected ground vector, including excited hole components, before induction on partition words. One ground-to-ground matrix coefficient is insufficient. Prove typed intertwining and keep its edge/projection residuals; multiplying two restricted identities does not automatically yield CAR.

## Noncommutative algebra

`Module.End` multiplication is composition. Fix `[A,B]=AB−BA` and distinguish lowering A from raising C: the scalar convention is `[A,C]=mI`, so `[C,A]=−mI`.

Expand sums/scalar actions, apply justified operator reorderings, and then normalize scalar coefficients. `ring` is not a general tactic for endomorphism words. `noncomm_ring` can prove identities that need only ring axioms; for example `(X+Y)²+(X−Y)²=2(X²+Y²)` needs no commutativity. A commutative product API is not available on all endomorphisms merely because a selected family commutes; use fixed ordered products or explicit pairwise-commutation support.

Derive quadratic CAR commutators from the checked CAR relations. Symmetric swap rules can loop, so normal ordering needs an orientation and a terminating measure such as word length followed by inversion count. Distinguish fermionic swaps from the bosonic rule `AC=CA+mI`.

Use free words for raw products and distinct creator/annihilator labels for normal symbols. Check the installed signature of `FreeAlgebra` (scalar type first). Evaluate fixed ordered monomials and extend linearly; a commutative polynomial algebra's universal property does not give an algebra homomorphism to noncommuting images. Prove evaluation preservation when rewriting words, including all contractions.

## Grading and useful hypotheses

Boson weights must be positive. On `Fin M`, use a proved positive weight such as `i.val+1`, rather than a raw zero-based index. Define the budget through finite monomial/configuration support and prove the grading of its operators. A zero-weight variable would make a fixed weight slice infinite-dimensional.

For a written word, the rightmost factor acts first. Track signed cumulative shifts and the input of each commutator substitution, including suffixes of rewritten words. A sum of positive shifts is a convenient sufficient wrapper; it may be stronger than the maximum actual excursion. An identity `[A,C]ψ=mψ` already proved on ψ does not additionally require Aψ and Cψ to stay in the same input budget.

Keep scalar, exact edge, diagonal-action, and all-mode CCR results separate. For example, a same-mode hypothesis can admit `h=2,m=1,K=1,N=0` even when a uniform all-pair bound rejects it. Do not weaken a frozen theorem based on a toy example; propose a separate useful helper with a proved local contract.

For Gram pull-through, establish the induction invariant on the right remainder. With remainder energy `E≤K−n`, the bound `m+n+E≤m+K≤2K` supports the R2 margin `2K+|N|≤h`. In Sugawara, modes `m>K` already annihilate the input on the right; do not impose an upper-cutoff margin on them merely because the sum runs to M.

Compute partial shifts using equality of integer labels in the actual positive-Nyquist band. Same-sign shift composition can simplify globally; mixed signs retain an intermediate-in-band test. Prove exact edge coefficients before scalar budget CCR, and lift via dΓ as a linear Lie map, not an algebra homomorphism.

## Carriers, pairings, and exponentials

| Carrier | What to establish |
| --- | --- |
| Algebraic polynomial module | Creation/derivative grading and an algebraic pairing; creation need not be locally nilpotent. |
| Finite compressed slice | Finite basis, projected action, nilpotency when grading proves it, and boundary commutators. |
| Formal series or coefficients modulo t^(d+1) | The coefficient ring, central parameter, and exact degree of the identity. Truncation of t is not nilpotency of the operator. |
| Analytic exponential | A separate justified construction and domain/convergence theorem; outside the present purely algebraic workflow. |

Over ℂ, the weighted monomial form is Hermitian/sesquilinear, with conjugation in the first slot. Positive weights give finite-slice inner products. Prove ambient creator/derivative pairing identities algebraically; apply the finite-dimensional adjoint API only on carriers meeting its hypotheses.

For expNil, prove power vanishing from grading, then cutoff independence, inverse, and adjoint compatibility. Write coefficients as scalar actions, for example `((j! : ℂ)⁻¹) • A^j`. Factorial cancellation requires suitable invertibility, such as a ℚ-algebra; it is not division in `Module.End`.

Compressed creation/annihilation operators acquire boundary terms, so ambient central-commutator BCH cannot be used globally after compression. Check scalar BCH on its actual carrier and parameters. Distinguish Lie-algebra nilpotency from nilpotency of its represented operators. Verify library exponential signatures before use; `PowerSeries.exp` takes a coefficient type, not an endomorphism to exponentiate.

## Scalar matching and SW

Bogoliubov inversion uses the scalar relation `c²−s²=1` and needs no CCR margin. Star compatibility needs real/self-adjoint scalars or the appropriate conjugate relations. Restricted CCR preservation and quadratic diagonalization are separate results; use same-mode CCR if that is all the quadratic expansion needs.

For the plus-sign transform and pairing convention, match `v1=u(c²+s²)` and `v2=2ucs` after expanding the operator quadratic, including its vacuum constant. A scalar construction under `v1>|v2|` is

\[
 u=\sqrt{v1^2-v2^2},\qquad c=\sqrt{(v1+u)/(2u)},\qquad s=v2/(2uc).
\]

Prove u>0 and c>0 before division and prove the matching relations once. This allows negative or zero v2; downstream proofs should use the relations rather than repeatedly unfold square roots. Check the physical/computational branch dictionary before identifying a hopping model with a pairing model.

For SW, choose an actual block-adapted eigenbasis of self-adjoint H₀ commuting with the projections. Require `E_λ≠E_μ` only where a nonzero cross-block coupling is divided. Set the generator entry to zero on uncoupled pairs; prove anti-adjointness and `[S₁,H₀]=−V_off`.

For a second-order algebraic result, coefficient triples modulo t³ suffice. Expand `1+tS₁+t²S₁²/2`, conjugate H₀+tV, and project. Prove `P[S₁,V_diag]P=0`. The unprojected expansion can still contain this term, and full second-order block decoupling can require S₂. The anti-Hermitian matrix `[[0,−1],[1,0]]` has square −I: finite dimension and anti-Hermiticity do not make S₁ nilpotent. A projected coefficient identity is not an exact rotation, RG flow, or spectral-gap theorem.

## Existence and witnesses

A quantum state is a normalized positive complex-linear functional. A multiplicative scalar map sends commutators to zero and cannot represent a state on nonzero scalar CCR. Construct positivity/existence in a suitable abstract representation before using its contractions. A compressed finite model need not have a vector annihilated by every proposed dressed annihilator. Define a Weyl/formal vertex carrier before evaluating exponential moments; the polynomial CCR algebra does not automatically contain them.

For duality, define the maps on actual generators, prove relation/star preservation and inverse identities, and track charges and phases. For spin/charge sectors, construct the parity-constrained integer charge-lattice equivalence; a total-energy budget sums over compatible energy splits rather than tensoring two independently bounded budgets. `Hψ≤Kψ` is not an ordinary complex-vector predicate; use coordinate energy support or an established spectral projection.

A leakage proof needs an actual outside-projection coefficient, not only a formal charge shift or nonzero total action. Check Pauli allowance and the spatial Fourier sum, then rule out cancellation. Under the computational field convention, the zero-charge ground with `L=2h`, `h≥1`, admits the witness that adds momentum 1 in each L species and removes momentum `1−h` in each R species. Its selected exponent is −L; derive the CAR sign and normalization before adopting the coefficient. Recompute it if branch conventions change.

Use small admissible examples to assess hypothesis usefulness, including zero coupling or negative charges where the theorem permits them. Counterexamples outside a regime clarify its scope. Distinguish a proposed witness lemma, an exact finite calculation, and a completed Lean proof in the notebook.
