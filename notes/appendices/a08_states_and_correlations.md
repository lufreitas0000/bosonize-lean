# Appendix A08 proposal: state existence and finite correlation contracts

## State data and existence

**Definition (Normalized positive functional):**
A normalized positive functional is more than a linear map with rewrite axioms. Specify a star algebra, normalization ω(I)=1, and positivity `ω(A†A)≥0` in a precise real-valued sense. Prove existence on the actual carrier before using annihilation conditions as an interface.

*Lean 4 Proof Strategy:*
- Use actual ambient instances `[Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]` and verify their compatibility; `StarAlgebra A` is not an installed typeclass.
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
- Auxiliary Lemma: Prove `[A_m,C_n] = δ_mn*m*I` in the abstract uncompressed carrier; `[C_m,A_n]` has the opposite sign.
- Conclude the second identity using the auxiliary lemma and the given algebraic identity $c^2 - s^2 = 1$.

> [!WARNING]
> **Proof-review correction (2026-10-09):** Reverse the CCR order in the preceding auxiliary lemma: `[A_m,C_n] = δ_mn*m*I`; `[C_m,A_n]` has the negative sign. The vacuum assumptions must hold for the stated family of dressed annihilators in a constructed normalized positive state. A single unspecified condition `ω(P†P)=0` does not establish existence or all required contractions.

**Theorem (Ordered Two-Point Function):**
With vanishing same-branch anomalous contractions in the specified Gaussian state, the ordered two-point function is

\[
 \omega(\rho(x)\rho(y))=
 L^{-2}\sum_{m=1}^M m\big(s^2\zeta^{-m(x-y)}+c^2\zeta^{m(x-y)}\big).
\]

*(Historical note: an early draft of Chapter 19 assigned $s^2$ to both terms; Chapter 19 now correctly distinguishes $s^2$ and $c^2$ mode contractions).* At $s=0$ and $x=y$, the expression reduces to the finite vacuum variance $L^{-2} \sum_{m=1}^M m > 0$. For $h=2, M=1$ it is exactly $1/16$, verified by direct CAR computation. A symmetrized correlator has another coefficient; define the observable being measured before changing to a cosine expression.

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

**Definition (Explicit Logarithmic Kernel):**
*(Chapter 20 now defines $D_1$ explicitly via Definition 20.3)*:
\[
 D_1(x, y) = \sum_{m=1}^M \frac{1}{m} \left( 1 - \cos\left(\frac{2\pi m (x-y)}{L}\right) \right).
\]
A finite polynomial exponential $\operatorname{expNil}$ of nilpotent operators on a truncated budget is a polynomial in its generator words; it does not automatically equal a scalar Gaussian exponential. The scalar Gaussian exponential $\exp[-2g D_1(x,y)]$ arises strictly when evaluating the state functional on abstract Weyl / vertex operators $\mathcal{V}(x) = : e^{i \Phi(x)} :$ within an abstract CCR/Weyl algebra equipped with a quasi-free Gaussian state, not as an exact identity of finite-Fock CAR operators.

*Lean 4 Proof Strategy:*
- Define `D_1 (M : ℕ) (t : ℝ) : ℝ := ∑ m in Finset.Icc 1 M, (1 - Real.cos (m * t)) / m`.
- Construct the abstract Weyl algebra generated by unitary exponentials $W(f) = e^{i \rho(f)}$.
- On this abstract Weyl algebra, evaluate the quasi-free Gaussian state $\omega(W(f)) = e^{-\frac{1}{2}\omega(\rho(f)^2)}$ using Wick's theorem.

**Theorem (Abstract Vertex Correlators):**
Formulate exact equalities for abstract vertex correlators $\omega_{\tilde{\Omega}}(\mathcal{V}^\dagger(x) \mathcal{V}(y))$, explicitly tracking Klein/zero-mode expectation values $C_0, C_0'$, phase characters $\zeta^{(N_L - N_R - 1)(x-y)}$ and $\zeta^{(N_R + N_L)(x-y)}$, and normalization. Any comparison to concrete finite-lattice CAR observables $O(x) = c^\dagger_R(x) c_L(x)$ must be formulated as a separate comparison theorem with explicit budget projections and finite-size corrections.

*Lean 4 Proof Strategy:*
- Formalize the full correlation function as an explicit equality `=` instead of proportionality `∝`.
- Define structures for `KleinFactor` and `ZeroMode` and prove their exact algebraic commutation relations with the vertex operators.
- Keep the abstract vertex equality on its constructed carrier/state. Any comparison with finite CAR matrices is a separate theorem with explicit error or restriction; the scalar Gaussian is not automatically a finite-Fock expectation.
