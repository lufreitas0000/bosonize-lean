# Appendix A08 proposal: state existence and finite correlation contracts

## State data and existence

A normalized positive functional is more than a linear map with rewrite axioms. Specify a star algebra, normalization ω(I)=1, and positivity `ω(A†A)≥0` in a precise real-valued sense. Prove existence on the actual carrier before using annihilation conditions as an interface.

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

Two possible layers should be kept distinct:

- Actual finite model: construct a normalized ground vector/density matrix and evaluate finite matrix products, retaining boundary effects.
- Abstract untruncated CCR model: construct a Gaussian/quasi-free functional on a suitable word/Weyl algebra, prove positivity and existence, then prove any finite-model comparison separately.

A formal scalar rewrite evaluator need not be positive and need not factor through the represented finite operator algebra. Do not identify it with an actual finite-Fock state without the consistency proof.

## Both mode contractions are needed

Assuming a legitimately constructed dressed vacuum and valid contractions, the bare right-branch moments are

\[
 \omega(C_mA_n)=\delta_{mn}m s^2,\qquad
 \omega(A_mC_n)=\delta_{mn}m c^2.
\]

The second follows from the first and c²−s²=1. It supplies the nonzero free-vacuum fluctuation when s=0. Both are needed when expanding the Hermitian density `ρ(x)=L⁻¹Σ(ζ^−mx C_m+ζ^mx A_m)`.

With vanishing same-branch anomalous contractions in the specified Gaussian state, the ordered two-point function is

\[
 \omega(\rho(x)\rho(y))=
 L^{-2}\sum_{m=1}^M m\big(s^2\zeta^{-m(x-y)}+c^2\zeta^{m(x-y)}\big).
\]

Chapter 19.8 incorrectly assigns s² to both terms. At s=0 and x=y, its expression is zero, whereas the finite vacuum variance is `L⁻²Σm>0`. For h=2,M=1 it is exactly 1/16, verified by the saved CAR computation. A symmetrized correlator has another coefficient; define the observable being measured before changing to a cosine expression.

## Exact kernels and asymptotics

Define the mode cutoff M and the ordered/symmetrized two-point function explicitly. Prove finite character-sum formulas first. A periodic finite sum does not establish a power-law decay theorem by itself. If asymptotics are wanted, specify scaling variables, separation regime, limiting regulator sequence, and error estimates in a separate analytic layer.

Chapter 20's D₁ is not defined by chapter 19's m-weighted density kernel. Define a candidate logarithmic kernel explicitly, such as a specified `Σ_(m=1)^M(1−cos(mt))/m`, before asserting any relation to vertex moments. A finite polynomial exponential calculation is a polynomial in its scalar parameters; it does not generally equal a scalar `Complex.exp` without a new series/analytic interpretation and a Gaussian-state proof.

For exact order-parameter correlations, retain all Klein/zero-mode factors, normalization, regulator dependence, and source/target projections. Replace every `∝` by a declared equality with a specific prefactor. Separate a future continuum interpretation from the finite identity being frozen.
