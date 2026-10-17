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


#### Constructive realization in Lean

The verified finite part of this chapter is developed in the
[CH20 Core module](../../Bosonize/Core/Ch20CDW.lean), with exact theorem mappings
and validation evidence in its [companion](../../docs/companion/Bosonize/Core/Ch20CDW.md).
It realizes the CAR products and their projection residuals in §20.1, together
with charge-coefficient, parameter and mode-family identities underlying §20.3.
The formal vertices and state transport in §§20.2–20.3 retain the separate
construction obligations described below. The earlier proof strategies remain
reference proposals; the realization here explains the completed finite arguments.

**Occupation configurations and fields.** Fix a finite ordered species set,
distinct species R and L, and the momentum band $\{-h+1,\ldots,h\}$ of length
$2h$. The finite Fock space has an orthonormal ket $|S\rangle$ for every subset
of species–momentum pairs. Removing an occupied pair or inserting an empty pair
multiplies the ket by the fermionic sign determined by the occupied pairs
preceding it. Forbidden removal or insertion gives zero. These basis actions
supply the concrete CAR and their actual Hilbert adjoints.

The position field is the normalized finite Fourier sum of these annihilators.
The general order-parameter and residual identities retain a boundary twist for
each species and take integer positions $x$. Creation in the CDW word is the
Hilbert adjoint of the right field, including conjugation of its Fourier
coefficients. The charge commutators follow by applying the charge observable
to the occupation basis and then to the ordered two-field product: CDW raises
$N_R$ and lowers $N_L$, whereas SC lowers both. These are ambient operator
identities; a cutoff is introduced only when a budget map is requested.

**Three budgets and the retained remainder.** A configuration belongs to
$B(N,K)$ when each species has relative charge $N_\nu$ and the sum of its species
excitation energies is at most $K$. This is the total-energy condition of
[A03](../appendices/a03_energy_budgets_and_filtered_maps.md), so it couples the
species through one common excitation allowance. Its orthogonal projector
retains precisely the admitted occupation coordinates.

For source $B(N,K_s)$, middle $B(N-e_L,K_m)$, and the appropriate target
$B(N+e_R-e_L,K_t)$ or $B(N-e_R-e_L,K_t)$, the proof inserts
$I=P_m+(I-P_m)$ between the two fields. This gives exactly (20.3) and (20.4),
for arbitrary nonnegative cutoffs, with the escaped intermediate component
still present. No range-preservation hypothesis is needed for an identity
that retains that component. The projected right creation is also proved to
be the adjoint of the projected right annihilation with source and target
reversed. Thus the dagger in the typed CDW factor has its actual Hilbert-space
meaning on those two named budgets.

The difference between intermediate and final truncation can be seen in one
explicit state. Take $h=2$, periodic twists, $R=0$, $L=1$, $x=1$, and the
zero-charge source sea, whose two species both occupy $\{-1,0\}$. Set
$K_s=K_m=0$. Removing the left mode $-1$ leaves $S_L=\{0\}$: its charge is
$-1$ and its excitation above that sector's ground configuration is one.
It is therefore discarded by the middle projector. Creating the right mode
$+1$ then gives
$$
 S_R=\{-1,0,1\},\qquad S_L=\{0\}.
$$
The right species is a charge-one ground configuration and has zero excitation;
the total target excitation is exactly one. Hence the target cutoff $K_t=1$
retains this occupation. Equality with this occupation forces the unique pair
of removed and created modes $(-1,+1)$. Its Fourier coefficient is a product
of nonzero normalization factors, characters and fermionic signs, so no other
term can cancel it. This proves nonzero residual action on the specified source
ground vector. At $K_t=0$ the entire residual output is proved zero: removing
left mode $0$ was already admitted by the middle budget, while removing $-1$
leaves the left excitation that a right creation cannot change.

**Ground coefficients and the charge reflection.** The general ground-matrix
coefficient formulas specialize the fields to periodic twists. They require
$h>0$ and admissibility $-h\le N_\nu\le h$ for every species. For CDW the
additional edge conditions are $N_R<h$ and $-h<N_L$; for SC they are
$-h<N_R$ and $-h<N_L$. These conditions allow the required right insertion
or removal and left removal. Occupation matching reduces each ground-to-ground
coefficient to its unique boundary-mode pair, giving $1/(2h)$ times the
charge/Klein coefficient in §20.1. The two $L=4$ examples give $i/4$ in the
stated source sectors, and the SC operator is proved nonzero. The periodic
specialization is part of these coefficient theorems; the general operator
identities above still retain the twists.

Let $f$ negate $N_L$ and fix the other charges, and write $K_{CDW}$ and $K_{SC}$
for the scalar character–Klein coefficients. For $h>0$, the proved reflection
laws include
$$
 K_{CDW}(fN,x)=\zeta^x\,
 \overline{K_{SC}(N+e_R+e_L,x)},\qquad
 K_{SC}(fN,x)=\zeta^x\,
 \overline{K_{CDW}(N-e_R+e_L,x)}.
$$
Their coefficients have modulus one. The charge shifts on the conjugated side
express the reversed source of an adjoint; the extra root phase $\zeta^x$
is retained. These are scalar and charge-label identities, supplying that
part of (20.10) without asserting its full formal-vertex version.

**Parameter and mode-family substitution.** The hyperbolic construction sends
$(c,s)$ to $(c,-s)$, fixes $u,v_1$, and sends $v_2$ to $-v_2$. Applying it twice
recovers the original hyperbolic pair and the physical coordinates of the
parameter record. It exchanges $(c-s)^2$ and $(c+s)^2$. The explicit pair
$(5/4,3/4)$ gives $g=1/4$ and its dual gives $g=4$.

For a family of endomorphisms $\rho_{\eta,m}$, substitute
$\rho_{R,m}\mapsto-\rho_{R,m}$ and $\rho_{L,m}\mapsto\rho_{L,m}$.
This substitution is involutive. Equal-orientation commutators are unchanged;
cross commutators gain a minus sign, so an already zero cross commutator stays
zero. Expanding the ordered quadratic words proves that the pairing expression
at $(v_1,v_2)$ becomes the expression at $(v_1,-v_2)$. Finite dressed phases
use the opposite spatial orientations explained in
[A06](../appendices/a06_chiral_fields_and_lattice_kernels.md); their substitution
laws give $X_{CDW}\mapsto-X_{SC}$ and $X_{SC}\mapsto-X_{CDW}$ at dual parameters.
These identities hold for the defined finite sums on a mode family. Their
specialization to the existing density modes is proved, but a unitary on the
finite Fock space implementing all of this is a further construction. A
nonzero pairing example at $h=8$, $m=1$, $v_1=17$, $v_2=15$ confirms that reversing
the interaction changes its action on an actual ground ket.

The symmetric quadratic charge energy transforms with $N_L\mapsto-N_L$ and
$g_2\mapsto-g_2$, as does the zero-mode energy at its specified canonical chemical
potential. The theorem does not extend to arbitrary chemical potentials: the
chapter proves a concrete inequality between the unadjusted energies at charges
$(0,1)$ and $(0,-1)$.

**Finite kernel and remaining formal theory.** The finite cosine sum (20.5)
is proved symmetric, nonnegative and zero at equal arguments. Its elementary
proof uses evenness of cosine and $\cos t\le1$ term by term; for $h=2$, $M=1$,
$x=1$, $y=0$ its value is one. This finite kernel is available for a subsequent
correlator construction. Constructing formal vertices, proving their Hermitian
properties and formal correlations, the full tensor-algebra duality and vertex law,
and state transport remain CH20b obligations. The finite results do not yet
supply the formal correlations (20.8)–(20.9), evaluation of a formal parameter
at one, or a continuum power law. The reference formulas above remain the
stated targets for those further constructions.


### S1 input for the remaining formal correlator construction

The [A08 S1 extension](../appendices/a08_states_and_correlations.md#ordered-wick-theorem-and-moments-s1-oscillator-extension)
now supplies the ordered Wick theorem and all polynomial moments for arbitrary
homogeneous oscillator linear forms in the existing uncompressed state.
Contractions retain their order, $Q(Y,Z)=\omega_P(YZ)$, and are complex bilinear.
For $q=\omega_P(Y^2)$, the even moments are $(2k)!q^k/(2^k k!)$ and odd moments
vanish. The explicit perfect-pairing sum is connected to pull-through by the
unique partner of the first position. This provides the oscillator moment
input for a later coefficientwise construction. The charge carrier, formal
vertices, full formal correlations, and comparisons with finite interacting
states remain separate Chapter 20 obligations.
