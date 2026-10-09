# Appendix A08 proposal: state existence and finite correlation contracts

## State data and existence

**Definition (Normalized positive functional):**
A normalized positive functional is more than a linear map with rewrite axioms. Specify a star algebra, normalization ω(I)=1, and positivity `ω(A†A)≥0` in a precise real-valued sense. Prove existence on the actual carrier before using annihilation conditions as an interface.

*Lean 4 Proof Strategy:*
- Formalize a Star Algebra using a typeclass `StarAlgebra A` over `ℂ`.
- Define a structure `NormalizedPositiveFunctional` containing a linear map `ω : A →ₗ[ℂ] ℂ`, a normalization axiom `ω 1 = 1`, and a positivity axiom `∀ a : A, 0 ≤ (ω (star a * a)).re` (with imaginary part equal to zero).
- Separate the abstract CCR word-algebra from finite representations to explicitly construct the positive carrier.

**Theorem (Common Kernel of Compressed Annihilators Can Be Zero):**
In a finite matrix algebra, a positive state is represented by a positive density matrix of trace one. Vacuum annihilation conditions require support inside the common kernel of all proposed annihilators. That common kernel can be zero after compression. Avoid hiding an impossible vacuum in a universally quantified assumption and calling the resulting correlator nonvacuous.

A finite witness: on the two-mode total-degree ≤1 slice with basis `{1,X_R,X_L}`, compressed annihilators and creators give

\[
 Q_R=cD_R+s\widetilde X_L,\qquad
 Q_L=cD_L+s\widetilde X_R.
\]

For c=5/3,s=4/3 (so c²−s²=1),

\[
 Q_R^\dagger Q_R+Q_L^\dagger Q_L
 =\operatorname{diag}(32/9,25/9,25/9)>0.
\]

Thus their common kernel is zero. There is no normalized positive vacuum satisfying both annihilation conditions on this slice. This is a counterexample to an automatic-existence strategy, not a claim that every finite interacting model lacks a ground state. The actual finite Hamiltonian always needs its own ground-state construction; it need not be annihilated exactly by the compressed continuum-style modes.

*Lean 4 Proof Strategy:*
- Define the two-mode finite slice as a finite-dimensional Hilbert space isomorphic to `Fin 3 → ℂ` with the specified basis.
- Define explicit matrix representations for $Q_R$ and $Q_L$ with parameters $c=5/3, s=4/3$.
- State an auxiliary lemma evaluating the sum $Q_R^\dagger Q_R + Q_L^\dagger Q_L$ as the matrix $\operatorname{diag}(32/9, 25/9, 25/9)$.
- Use mathlib's `Matrix.PosDef` to establish strictly positive eigenvalues, proving the kernel is trivial (`{0}`).
- Conclude the main theorem by contradiction: any valid density matrix $\rho$ supported on the intersection of the kernels of $Q_R$ and $Q_L$ must have $\text{Tr}(\rho) = 0$, violating the normalization requirement $\text{Tr}(\rho) = 1$.

Two possible layers should be kept distinct:

- Actual finite model: construct a normalized ground vector/density matrix and evaluate finite matrix products, retaining boundary effects.
- Abstract untruncated CCR model: construct a Gaussian/quasi-free functional on a suitable word/Weyl algebra, prove positivity and existence, then prove any finite-model comparison separately.

A formal scalar rewrite evaluator need not be positive and need not factor through the represented finite operator algebra. Do not identify it with an actual finite-Fock state without the consistency proof.

## Both mode contractions are needed

**Lemma (Bare Right-Branch Moments):**
Assuming a legitimately constructed dressed vacuum and valid contractions, the bare right-branch moments are

\[
 \omega(C_mA_n)=\delta_{mn}m s^2,\qquad
 \omega(A_mC_n)=\delta_{mn}m c^2.
\]

The second follows from the first and c²−s²=1. It supplies the nonzero free-vacuum fluctuation when s=0. Both are needed when expanding the Hermitian density `ρ(x)=L⁻¹Σ(ζ^−mx C_m+ζ^mx A_m)`.

*Lean 4 Proof Strategy:*
- Formalize the Bogoliubov transformation connecting the bare operators $(C_m, A_m)$ to the dressed (Bogoliubov) operators.
- Introduce the dressed vacuum state $\omega$ mathematically via $\omega(P^\dagger P) = 0$.
- Prove the first identity $\omega(C_m A_n) = \delta_{mn} m s^2$ by inverting the Bogoliubov transformation and evaluating the expectation on the dressed vacuum.
- Auxiliary Lemma: Prove the bare commutation relations $[C_m, A_n] = m \delta_{mn}$.
- Conclude the second identity using the auxiliary lemma and the given algebraic identity $c^2 - s^2 = 1$.

**Theorem (Ordered Two-Point Function):**
With vanishing same-branch anomalous contractions in the specified Gaussian state, the ordered two-point function is

\[
 \omega(\rho(x)\rho(y))=
 L^{-2}\sum_{m=1}^M m\big(s^2\zeta^{-m(x-y)}+c^2\zeta^{m(x-y)}\big).
\]

Chapter 19.8 incorrectly assigns s² to both terms. At s=0 and x=y, its expression is zero, whereas the finite vacuum variance is `L⁻²Σm>0`. For h=2,M=1 it is exactly 1/16, verified by the saved CAR computation. A symmetrized correlator has another coefficient; define the observable being measured before changing to a cosine expression.

*Lean 4 Proof Strategy:*
- Define the Hermitian density operator `ρ(x)` as the finite sum `L⁻¹ ∑_m (ζ^{-mx} C_m + ζ^{mx} A_m)`.
- Apply linearity of the state $\omega$ to expand the product $\omega(\rho(x)\rho(y))$ into a double sum.
- Apply the *Lemma (Bare Right-Branch Moments)* to evaluate the cross terms $\omega(C_m A_n)$ and $\omega(A_m C_n)$.
- Apply the hypothesis of vanishing same-branch anomalous contractions to set $\omega(C_m C_n) = \omega(A_m A_n) = 0$.
- Simplify the resulting algebraic sum to obtain the stated result.
- Auxiliary Lemma: Prove that the evaluation at $s=0$ and $x=y$ reduces to the free-vacuum variance $L^{-2} \sum_{m=1}^M m$.

## Exact kernels and asymptotics

**Definition (Mode Cutoff and Correlation Functions):**
Define the mode cutoff M and the ordered/symmetrized two-point function explicitly. Prove finite character-sum formulas first. A periodic finite sum does not establish a power-law decay theorem by itself. If asymptotics are wanted, specify scaling variables, separation regime, limiting regulator sequence, and error estimates in a separate analytic layer.

*Lean 4 Proof Strategy:*
- Formalize `M : ℕ` as a strictly finite truncation parameter.
- Define the two-point functions as precise functions into `ℂ` using `Finset.sum` over `1 ≤ m ≤ M`.
- Avoid mixing asymptotic approximations with exact algebraic identities. When defining scaling limits, set up a proper `Filter.Tendsto` limit as $M \to \infty$ within Mathlib's `Asymptotics` framework.

**Definition (Candidate Logarithmic Kernel):**
Chapter 20's D₁ is not defined by chapter 19's m-weighted density kernel. Define a candidate logarithmic kernel explicitly, such as a specified `Σ_(m=1)^M(1−cos(mt))/m`, before asserting any relation to vertex moments. A finite polynomial exponential calculation is a polynomial in its scalar parameters; it does not generally equal a scalar `Complex.exp` without a new series/analytic interpretation and a Gaussian-state proof.

*Lean 4 Proof Strategy:*
- Define `D_1 (M : ℕ) (t : ℝ) : ℝ := ∑ m in Finset.Icc 1 M, (1 - Real.cos (m * t)) / m`.
- Provide a rigorous proof (e.g., using Wick's Theorem for Gaussian states, formalized via a `IsGaussianState` typeclass) that relates the exact finite sum of vertex moments to the exponentiation of `D_1`, ensuring no undocumented continuous limiting assumptions are hidden in the derivation.

**Theorem (Exact Order-Parameter Correlations):**
For exact order-parameter correlations, retain all Klein/zero-mode factors, normalization, regulator dependence, and source/target projections. Replace every `∝` by a declared equality with a specific prefactor. Separate a future continuum interpretation from the finite identity being frozen.

*Lean 4 Proof Strategy:*
- Formalize the full correlation function as an explicit equality `=` instead of proportionality `∝`.
- Define structures for `KleinFactor` and `ZeroMode` and prove their exact algebraic commutation relations with the vertex operators.
- Incorporate all normalization factors explicitly in the formal identity, ensuring the theorem maps exactly to finite finite-matrix computations without appealing to continuum approximations.
