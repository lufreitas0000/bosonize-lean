### Chapter 20: Projected Order Parameters, Formal Vertex Correlators, and Model Duality

This chapter has two explicit carriers: finite CAR order parameters with exact intermediate-projection residuals, and formal Weyl-type vertices in the uncompressed algebraic model of [A08](../appendices/a08_states_and_correlations.md). The latter do not assert a finite-CAR correlator or an analytic exponential at parameter 1. [A05](../appendices/a05_exponentials_klein_and_vertex_scope.md) supplies the conditional field criterion and [A09](../appendices/a09_duality_spin_and_umklapp.md) the duality contracts.

#### 20.1 Exact Finite CAR Products

**Definition 20.1 (Order Parameters).** On the finite Fock Hilbert carrier,
$$
O_{CDW}(x)=c_{R,x}^\dagger c_{L,x}^{\phantom{\dagger}},\qquad O_{SC}(x)=c_{R,x}^{\phantom{\dagger}}c_{L,x}^{\phantom{\dagger}}. \tag{20.1–20.2}
$$
They are even CAR words. Define them directly as endomorphisms; no new order-parameter structure is needed.

**Lemma 20.2 (Typed Product with Projection Residual).** Let $V_s$ be the source budget at charge $N$, $V_m$ an intermediate budget at $N-e_L$, and $V_t$ the target budget at $N+e_R-e_L$ (CDW) or $N-e_R-e_L$ (SC). Write $i_s,i_m$ for inclusions, $p_m,p_t$ for orthogonal projections into their carriers, and $P_m=i_m p_m$ on the ambient Fock space. Put
$$
B_L=p_m c_{L,x}i_s:V_s\to V_m,
$$
and $B_R^\dagger=p_t c_{R,x}^\dagger i_m:V_m\to V_t$ for CDW, or $B_R=p_t c_{R,x}i_m$ for SC. If using the candidate bosonized factors of Chapter 14, establish these single-factor equalities by Theorem 14.5 first. Then
$$
p_t O_{CDW}(x)i_s=B_R^\dagger\circ B_L+
 p_t c_{R,x}^\dagger(I-P_m)c_{L,x}^{\phantom{\dagger}}i_s, \tag{20.3}
$$
$$
p_t O_{SC}(x)i_s=B_R\circ B_L+
 p_t c_{R,x}(I-P_m)c_{L,x}i_s. \tag{20.4}
$$
The $B_R^\dagger$ label here requires the reversed source/target data of the adjoint annihilation map; it is not the adjoint of a map on an unrelated budget. Each cutoff belongs to its named carrier. Residuals vanish only after proving a range or final-projection annihilation condition, not by multiplying compressed equalities. No combined `expNil` expression is asserted.

For admissible source/target sector ground kets the source phase is $\zeta^{(N_L-N_R-1)x}$ for CDW and $\zeta^{(N_R+N_L)x}$ for SC. At $L=4,\zeta=i,x=1$ the exact coefficients are $i/4$ for CDW from $(0,0)$ to $(1,-1)$, and $i/4$ for SC from $(1,0)$ to $(0,-1)$, including the fixed Klein signs. These scalar checks do not prove equality on all budgets. In a ground-to-ground calculation, prove that a discarded L excitation cannot be removed by the R factor before dropping the residual.

*Lean 4 Proof Strategy:*
Use `LinearMap.comp`, explicitly typed inclusions/projections, and A03's insertion $I=P_m+(I-P_m)$. Give each factor its charge/cutoff arguments. Prove actual single-field formulas independently and retain the residual in the product theorem. Only factor exponentials after a separate commutation and cutoff-transition theorem.

#### 20.2 Constructed Formal Vertices and Exact Formal Correlators

**Definition 20.3 (Finite Logarithmic Kernel).** For the canonical root and positive mode cutoff,
$$
D_1(x,y)=\sum_{m=1}^M\frac{1-\cos(2\pi m(x-y)/L)}m. \tag{20.5}
$$

**Definition 20.4 (Formal Weyl-Type Vertices).** Use the uncompressed charge/CCR tensor star-algebra $A$ and constructed positive state $\omega_{P,N}$ of A08. Its oscillator state is $\omega_0\circ\beta_P^{-1}$ and its charge state is $\delta_N$ expectation. In $A[[t]]$, $t$ central and self-adjoint, define the opposite-orientation Hermitian dressed phases
$$
Q_R(x)=\sum_m\frac{\zeta^{-mx}\widetilde C_{Rm}+\zeta^{mx}\widetilde A_{Rm}}m,
\quad Q_L(x)=\sum_m\frac{\zeta^{mx}\widetilde C_{Lm}+\zeta^{-mx}\widetilde A_{Lm}}m,
$$
$$
X_{CDW}=(c-s)(Q_R+Q_L),\quad X_{SC}=(c+s)(Q_R-Q_L),
$$
$$
W_{CDW}(P,t,x)=L^{-1}F_R^\dagger F_L\zeta^{(N_L-N_R-1)x}
 \operatorname{exp}_{formal}(itX_{CDW}(P,x)), \tag{20.6}
$$
$$
W_{SC}(P,t,x)=L^{-1}F_R F_L\zeta^{(N_R+N_L)x}
 \operatorname{exp}_{formal}(itX_{SC}(P,x)). \tag{20.7}
$$
Charge phases act first on the source. The Klein convention is $R<L$ with $P_\nu(N)=(-1)^{\sum_{\eta<\nu}(h+N_\eta)+h+N_\nu-1}$. This is a specified formal oscillator model, distinct from normal-ordered Mattis–Mandelstam exponentials. All factorial divisions are complex scalar coefficients. Extend $\omega_{P,N}$ coefficientwise to $\mathbb C[[t]]$, without claiming a positive scalar-valued functional on arbitrary series.

**Theorem 20.5 (Coefficientwise Vertex Correlators).** In that construction,
$$
\omega_{P,N}(W_{CDW}(t,x)^*W_{CDW}(t,y))=
 \frac1{L^2}\zeta^{(N_L-N_R-1)(y-x)}
 \operatorname{Exp}_{formal}[-2gD_1(x,y)t^2], \tag{20.8}
$$
$$
\omega_{P,N}(W_{SC}(t,x)^*W_{SC}(t,y))=
 \frac1{L^2}\zeta^{(N_R+N_L)(y-x)}
 \operatorname{Exp}_{formal}[-2g^{-1}D_1(x,y)t^2]. \tag{20.9}
$$
Here $g=(c-s)^2>0$, $g^{-1}=(c+s)^2=1/g$, and $C_0=C_0^{\prime}=1$. Opposite chirality orientations cancel $[X_J(x),X_J(y)]$; the state variances of phase differences are $4gD_1$ and $4g^{-1}D_1$. At $x=y$ both correlators are $L^{-2}$ as constant series.

*Lean 4 Proof Strategy:*
Follow A08's polynomial representation and positive pullback state construction. Prove Klein phase products, Hermitian phases, commutator cancellation, both difference variances, and Gaussian moments by word induction. Prove the exponential coefficient identities on the chosen noncommutative series carrier; do not apply an unchecked commutative power-series API. No evaluation $t=1$, analytic convergence, or finite-CAR comparison is included. At $L=4$ the finite CAR sea correlator at equal points is 1/4, while this formal model has normalization 1/16; these are explicitly different observables/representations.

#### 20.3 Explicit Algebraic Model Duality

**Definition 20.6 (Duality on Generators and Charges).** Set $P^*=(u,c,-s,\mathrm{gInv},g)$; $v_1$ is fixed and $v_2$ changes sign. Define $D$ on bare oscillator generators by $R$ modes $\mapsto$ their negatives and $L$ modes $\mapsto$ themselves. This preserves star and CCR, and is an involution. On charges use $f(N_R,N_L)=(N_R,-N_L)$ and conjugation by the basis permutation $U_f\delta_N=\delta_{f(N)}$. In the signed Klein convention,
$$
D N_R=N_R,\quad D N_L=-N_L,\quad D F_R=F_R,\quad D F_L=-F_L^\dagger,
\quad D Z_R(x)=Z_R(x),\quad D Z_L(x)=Z_L(x)^\dagger.
$$
These tensor-factor maps define a star-algebra automorphism and extend coefficientwise to series. $D$ maps dressed $R$ generators at $P$ to their negatives at $P^*$, and dressed $L$ generators to themselves at $P^*$. Hence $D X_{CDW}(P)=-X_{SC}(P^*)$ and $D X_{SC}(P)=-X_{CDW}(P^*)$. Computing the source phase and shifted Klein order gives
$$
D W_{CDW}(P,t,x)=\zeta^x W_{SC}(P^*,t,x)^*,\qquad
D W_{SC}(P,t,x)=\zeta^x W_{CDW}(P^*,t,x)^*. \tag{20.10}
$$
The adjoint and $\zeta^x$ factor are required. The former direct CDW→SC exchange has the wrong charge shift.

**Theorem 20.7 (Hamiltonian and State Transport).** In the uncompressed algebraic model use the chemically adjusted symmetric zero-mode Hamiltonian
$$
H(P)=\frac{2\pi}{L}\sum_m\left[v_1(C_{Rm}A_{Rm}+C_{Lm}A_{Lm})
 +v_2(C_{Rm}C_{Lm}+A_{Rm}A_{Lm})\right]
 +\frac\pi L\left[v_1(N_R^2+N_L^2)+2v_2N_RN_L\right].
$$
Then
$$
D H(P)=H(P^*),\qquad \omega_{P^*,f(N)}\circ D=\omega_{P,N}. \tag{20.11}
$$
For the second identity prove oscillator vacuum invariance and $D\beta_P=\beta_{P^*}D$, then charge-basis expectation transport. It is a family of charge-indexed states, not a symmetry of every fixed-charge state. A linear $N_L$ term from an unadjusted chemical potential would break the displayed Hamiltonian relation. A finite-budget spectral equivalence, compactification/T-duality interpretation, and continuum phase claims each require an additional construction.

*Lean 4 Proof Strategy:*
Prove relation and star preservation, inverse, charge conjugation on kets, exact Klein/phase identities, and tensor transport. Extend via word induction and coefficient extensionality. Expand H preserving word order, and use positive-state pullback for the state identity. Do not infer finite unitary equivalence from a scalar parameter substitution or from this uncompressed quotient automorphism.
