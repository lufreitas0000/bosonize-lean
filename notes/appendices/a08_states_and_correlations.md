# Appendix A08: constructed algebraic states and formal vertex correlations

## Uncompressed oscillator carrier and a positive state

Fix L>0, the canonical complex root ζ=exp(2πi/L), and a finite positive mode set 1≤m≤M. The oscillator carrier is the unital complex star-algebra quotient of words in Aνm,Cνm, ν∈{R,L}, by
$$
[A_{\nu m},C_{\eta n}]=\delta_{\nu\eta}\delta_{mn}mI,
\quad[A_{\nu m},A_{\eta n}]=[C_{\nu m},C_{\eta n}]=0,
\quad A_{\nu m}^*=C_{\nu m}.
$$
There is no degree or energy compression in this algebra. Finitely many generators do not make it finite dimensional.

**Construction (Polynomial vacuum).** Use polynomials in variables Xνm. Represent Cνm by multiplication by Xνm and Aνm by m times partial differentiation. Give monomials the Hermitian Gram form
$$
\langle X^\alpha,X^\beta\rangle
 =\delta_{\alpha\beta}\prod_{\nu,m}\alpha_{\nu m}!\,m^{\alpha_{\nu m}}.
$$
All weights are strictly positive. The operators A and C are adjoint on this pre-Hilbert carrier and satisfy the quotient relations. Define ω₀(a)=⟨1,π(a)1⟩. This descends through the quotient, is complex linear, is normalized, and satisfies ω₀(a* a)=‖π(a)1‖²≥0. Thus the quotient and its positive functional are nonvacuous, without a Hilbert completion or an infinite-dimensional adjoint on arbitrary endomorphisms.

For the real parameter record P=(u,c,s,g,gInv), c²−s²=1, define the star-algebra automorphism β_P on generators by
$$
\beta_P(C_R)=cC_R+sA_L,\quad \beta_P(C_L)=cC_L+sA_R,
\qquad\beta_P(A_\nu)=\beta_P(C_\nu)^*.
$$
The inverse uses −s. Define the dressed state **ω_P=ω₀∘β_P⁻¹**, so that ω_P(a β_P(Aνm))=0 and ω_P(β_P(Cνm) a)=0 for every a. Pullback by a star automorphism preserves positivity and normalization. Pullback by β_P in the wrong direction would not give this dressed vacuum.

*Lean 4 Proof Strategy:*
Construct the word quotient with a star-stable relation ideal and its polynomial representation; do not assume a nonexistent `StarAlgebra` typeclass. Use compatible algebra and star instances, and a `NormalizedPositiveFunctional` structure with complex linearity, ω1=1, vanishing imaginary part of ω(a*a), and nonnegative real part. Prove monomial Gram positivity, generator adjointness, relation descent, β inverse/star preservation, and positive pullback before deriving contractions. Names for these project constructions are proposed helpers, not claims about installed Mathlib declarations.

## Charge extension and full model state

Let the charge module be `(ℤ × ℤ) →₀ ℂ`, with orthonormal kets δ_N. Work in the **generated adjointable star-algebra** of the diagonal charges N_R,N_L, phase maps Zν(x)δ_N=ζ^(Nν x)δ_N, and signed shifts
$$
F_\nu\delta_N=P_\nu(N)\delta_{N-e_\nu},\qquad
P_\nu(N)=(-1)^{\sum_{\eta<\nu}(h+N_\eta)+(h+N_\nu-1)},\quad R<L.
$$
Here h is a fixed integer reference phase offset. Integer parity powers allow all charges, with no natural subtraction. Each generator has an explicit adjoint on finite-support kets; the algebra consists of finite sums/products of them, not all endomorphisms of this infinite module. The δ_N expectation is a normalized positive charge functional. Tensor its representation with the polynomial oscillator representation and define ω_(P,N) as the product expectation with oscillator state ω_P. Positivity follows on finite tensor sums from the product pre-Hilbert Gram form. This is an infinite charge-lattice algebraic model; no finite-band charge bound is inherited automatically.

*Lean 4 Proof Strategy:*
Define the signed basis shifts and prove inverse/adjoint laws on kets, then generate the star-closed operator subalgebra. Construct the tensor representation on finite-support polynomial-valued charges and its positive vacuum functional. Do not use a scalar-valued multiplicative homomorphism as a state.

## Finite compressed vacua are a separate question

**Theorem (Common Kernel of Compressed Annihilators Can Be Zero):**
In a finite matrix algebra, a positive state is represented by a positive density matrix of trace one. Vacuum annihilation conditions require support inside the common kernel of all proposed annihilators. That common kernel can be zero after compression. Avoid hiding an impossible vacuum in a universally quantified assumption and calling the resulting correlator nonvacuous.

A finite witness: on the two-mode total-degree ≤1 slice with basis $\{1,X_R,X_L\}$, compressed annihilators and creators give

$$
 Q_R=cD_R+s\widetilde X_L,\qquad
 Q_L=cD_L+s\widetilde X_R.
$$

For c=5/3,s=4/3 (so c²−s²=1),

$$
 Q_R^\dagger Q_R+Q_L^\dagger Q_L
 =\operatorname{diag}(32/9,25/9,25/9)>0.
$$

Thus their common kernel is zero. There is no normalized positive vacuum satisfying both annihilation conditions on this slice. This is a counterexample to an automatic-existence strategy, not a claim that every finite interacting model lacks a ground state. The actual finite Hamiltonian always needs its own ground-state construction; it need not be annihilated exactly by the compressed continuum-style modes.

*Lean 4 Proof Strategy:*

- Define the two-mode finite slice as a finite-dimensional Hilbert space isomorphic to `Fin 3 → ℂ` with the specified basis.
- Define explicit matrix representations for $Q_R$ and $Q_L$ with parameters $c=5/3, s=4/3$.
- State an auxiliary lemma evaluating the sum $Q_R^\dagger Q_R + Q_L^\dagger Q_L$ as the matrix $\operatorname{diag}(32/9, 25/9, 25/9)$.
- Use mathlib's `Matrix.PosDef` to establish strictly positive eigenvalues, proving the kernel is trivial ($\{0\}$).
- Conclude the main theorem by contradiction: any valid density matrix $\rho$ supported on the intersection of the kernels of $Q_R$ and $Q_L$ must have $\text{Tr}(\rho) = 0$, violating the normalization requirement $\text{Tr}(\rho) = 1$.


The oscillator quotient above is not a representation by the compressed finite matrices. A finite Hamiltonian's actual ground vector or density matrix must be constructed separately; comparisons with the abstract state retain boundary corrections.

## Bare contractions and exact density kernels

**Lemma (Both bare right-branch contractions).** In the constructed state ω_P,
$$
\omega_P(C_{Rm}A_{Rn})=\delta_{mn}m s^2,\qquad
\omega_P(A_{Rm}C_{Rn})=\delta_{mn}m c^2,
$$
with same-branch AA and CC contractions zero. Derive these from β_P⁻¹ and the polynomial vacuum, including $[A,C]=mI$; the second term remains nonzero at s=0. Chapter 19's ordered density kernel is therefore
$$
\omega_P(\rho_R(x)\rho_R(y))=
 L^{-2}\sum_{m=1}^M m\big(s^2\zeta^{-m(x-y)}+c^2\zeta^{m(x-y)}\big),
\quad \rho_R(x)=L^{-1}\sum_m(\zeta^{-mx}C_{Rm}+\zeta^{mx}A_{Rm}).
$$

*Lean 4 Proof Strategy:*
Compute the vacuum contractions from the represented monomial basis, then expand β inverse and the finite double sum. Apply both CA and AC formulas, collapse the Kronecker sum, and retain the ordered complex kernel. A cosine-only expression describes a different symmetrized observable.

## Formal Weyl-type vertices: precise carrier and normalization

Choose the series algebra A[[t]], where A is the charge/oscillator tensor algebra, t is central, and t*=t. Define `exp_formal(t a)` by coefficients aⁿ/n!; each coefficient product is a finite convolution. Extend ω_(P,N) **coefficientwise into ℂ[[t]]**. This extension is a formal evaluator, not an ordinary ℂ-valued positive state on all series, and there is no substitution t=1 without additional convergence data.

Write the dressed generators as C̃,Ã. Use opposite spatial chirality orientations:
$$
Q_R(x)=\sum_{m=1}^M\frac{\zeta^{-mx}\widetilde C_{Rm}+\zeta^{mx}\widetilde A_{Rm}}m,
\quad Q_L(x)=\sum_{m=1}^M\frac{\zeta^{mx}\widetilde C_{Lm}+\zeta^{-mx}\widetilde A_{Lm}}m.
$$
Both are Hermitian. Set X_CDW=(c−s)(Q_R+Q_L), X_SC=(c+s)(Q_R−Q_L), and
$$
K_{CDW}(x)=F_R^\dagger F_L\zeta^{(N_L-N_R-1)x},\qquad
K_{SC}(x)=F_R F_L\zeta^{(N_R+N_L)x}.
$$
The diagonal phases act on the source charge. Define
$$
W_J(P,t,x)=L^{-1}K_J(x)\operatorname{exp}_{formal}(itX_J(P,x)),\qquad J\in\{CDW,SC\}.
$$
These are **Weyl-type formal vertices**, deliberately distinct from normal-ordered exponentials and the candidate finite Mattis–Mandelstam map. Normal ordering changes normalization and cannot be added as an innocuous colon.

Let
$$
D_1(x,y)=\sum_{m=1}^M\frac{1-\cos(2\pi m(x-y)/L)}m.
$$
Opposite chirality orientations give $[X_J(x),X_J(y)]=0$; the two chiral scalar commutators cancel. Polynomial vacuum Wick moments give variance 4gD₁ for X_CDW(y)−X_CDW(x), and 4gInvD₁ for X_SC(y)−X_SC(x). Consequently, as coefficientwise identities,
$$
\omega_{P,N}(W_{CDW}(t,x)^*W_{CDW}(t,y))=
 L^{-2}\zeta^{(N_L-N_R-1)(y-x)}\operatorname{Exp}_{formal}(-2gD_1(x,y)t^2),
$$
$$
\omega_{P,N}(W_{SC}(t,x)^*W_{SC}(t,y))=
 L^{-2}\zeta^{(N_R+N_L)(y-x)}\operatorname{Exp}_{formal}(-2gInvD_1(x,y)t^2).
$$
At x=y the normalization is L⁻²; the charge shifts are unitary, so C₀=C₀′=1 in this specified model.

*Lean 4 Proof Strategy:*
Prove charge-phase products on each δ_N and oscillator Gaussian moments by fixed-word Wick induction. Establish Hermitian phases, cancellation of spatial commutators, and both difference variances. Prove the formal exponential product identity coefficientwise for commuting X values, then evaluate the coefficients to obtain the displayed scalar formal series. Validate the chosen noncommutative series carrier before freezing definitions; do not guess that a commutative formal-exponential API applies to it. A Weyl C*-completion, analytic exponentials at t=1, and equality with finite CAR observables are separate tasks outside this algebraic theorem.

## Limits and physical interpretation

The finite D₁ sum is periodic and exact. Power-law decay, continuum duality, and physical order-parameter correlators require specified comparison maps, regulator/scaling limits, separation regimes, and error estimates. Coefficientwise formal series identities alone establish none of these analytic statements.
