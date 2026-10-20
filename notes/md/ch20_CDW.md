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
The verified S2 realization is developed in the
[V1S2 Formal Vertices module](../../Bosonize/Core/V1S2FormalVertices.lean), with
exact theorem mappings and validation evidence in its
[companion](../../docs/companion/Bosonize/Core/V1S2FormalVertices.md).
Together they realize the CAR products and their projection residuals in §20.1,
plus the charge/polynomial carrier, basis pairing, coefficientwise formal vertices
and correlators, and the duality coefficients used in §§20.2–20.3. The earlier
proof strategies remain reference proposals; the realization here explains the
completed constructive arguments. The S3 realization of the formal duality and
charge-indexed functional transport is explained below and in Appendix A09;
Hamiltonian covariance remains a separate obligation.

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

**Finite kernel and remaining formal theory.** The finite cosine sum (20.5) is proved symmetric, nonnegative and zero at equal arguments. Its elementary proof uses evenness of cosine and $\cos t\le1$ term by term; for $h=2$, $M=1$, $x=1$, $y=0$ its value is one. In the promoted S2 realization, this same cutoff kernel is the scalar Dirichlet factor that enters the exact coefficientwise correlator theorem and the Gaussian variance calculation. The formal vertices and correlators are now constructed in the uncompressed polynomial model; the formal duality and charge-indexed functional transport are now proved in S3, as explained below. Comparisons with finite interacting states, analytic evaluation of the formal parameter and continuum interpretations also require separate results. The Hamiltonian part of §20.3 still requires a separate construction.


### S1 input for the coefficientwise formal correlator theorem

The [A08 S1 extension](../appendices/a08_states_and_correlations.md#ordered-wick-theorem-and-moments-s1-oscillator-extension)
now supplies the ordered Wick theorem and all polynomial moments for arbitrary
homogeneous oscillator linear forms in the existing uncompressed state.
Contractions retain their order, $Q(Y,Z)=\omega_P(YZ)$, and are complex bilinear.
For $q=\omega_P(Y^2)$, the even moments are $(2k)!q^k/(2^k k!)$ and odd moments
vanish. The explicit perfect-pairing sum is connected to pull-through by the
unique partner of the first position. This is the moment input used in the
coefficientwise formal-vertex construction and its normal-prefactor contracts.
The charge carrier, the formal vertices, and the correlator formulas are already
realized in the promoted S2 source; the remaining chapter obligations are the
Hamiltonian and physical-state comparisons beyond the formal S3 transport, not the correlator algebra
itself.

#### S2 verified realization: coefficientwise formal vertices and correlators

See the promoted source [V1S2 Formal Vertices](../../Bosonize/Core/V1S2FormalVertices.lean) and the matching [companion](../../docs/companion/Bosonize/Core/V1S2FormalVertices.md) for the exact declarations.

For every mode cutoff $M\in\mathbb N$, including $M=0$, and every $h>0$ with $L=2h$, with real parameters $c,s$ satisfying $c^2-s^2=1$, the verified construction works with all integer charges $N=(N_R,N_L)\in\mathbb Z^2$. The carrier is the actual tensor product
$$
\mathrm{JointCarrier}(M)=\mathrm{ChargeVec}\otimes \mathrm{OscPoly}(M),
$$
where $\mathrm{ChargeVec}=\mathrm{Finsupp}(\mathbb Z^2,\mathbb C)$ is the space of finitely supported complex charge vectors and $\mathrm{OscPoly}(M)$ is the polynomial algebra in finitely many mode variables. The mode set is finite, but polynomial degree is unbounded: there is no truncation of degree, only a finite list of generators.

The pairing is defined from the tensor-product basis. On basis vectors it is a weighted sesquilinear form: if $e_i$ and $e_j$ are basis vectors, then
$$
\langle e_i,e_j\rangle = \delta_{ij}\,w_i,
$$
where $w_i$ is the oscillator monomial weight attached to the basis index. Equivalently, for general vectors $v$ and $u$,
$$
\langle v,u\rangle = \sum_{i\in\mathrm{supp}(v)\cup\mathrm{supp}(u)} \overline{v_i}\,w_i\,u_i.
$$
This is a pairing on the carrier itself; it is not a star operation on arbitrary endomorphisms.

The oscillator syntax is also kept free at the word level. Finite words in the oscillator generators form a monoid algebra, and the dagger there is explicit: conjugate the coefficient, reverse the word, and swap creator with annihilator. Evaluation then sends that finite-word syntax into the A08 oscillator representation. So the proof does not assume a star on all endomorphisms; it proves the represented adjoint relation on the concrete basis pairing.

The charge words are likewise concrete. A charge word records a bijection of the charge lattice and a source-dependent scalar amplitude, acting on a charge vector by a finite sum over the support of the vector. The canonical CH13 Klein coefficients are obtained from the simplified charge shifts by the diagonal gauge factor $\mathrm{chargeGauge}_h$; the oscillator tensor factor is unchanged. Thus the simplified shifts are the raw combinatorics, while the canonical versions are the gauge-corrected ones actually used in the promoted theorem.

The source-first phase convention is built into the coefficient theorem. In the two-point coefficient, the rightmost factor acts first, the source charge label is restored by the adjoint relation, and only then is the conjugate phase read off. This is why the scalar phase factor appears as a character of $y-x$: the source charge is transported through the represented adjoint, not through a blanket star on an unrelated operator algebra.

The fields use the forward Bogoliubov substitution with parameters $(c,s)$. The oscillator state uses its inverse, with parameters $(c,-s)$. Accordingly, the represented coefficient action first evaluates its syntax, applies that inverse substitution and then acts on polynomials. Together with the charge action, this gives an action on the tensor carrier. Pairing its value on $|N\rangle\otimes1$ against the same vector yields the joint functional. The adjoint-pairing theorem separately proves that the explicit coefficient dagger gives the represented adjoint for this pairing.

The same-channel commutator cancellation is proved at the linear-form level and then at the represented-operator level. For each fixed channel $J$, the field at $x$ commutes with the field at $y$ in the required reversed sense, so the commutator contribution cancels exactly where the Gaussian proof needs it. From there the difference-variance theorem gives
$$
4\,g_J\,D_1(x,y),
$$
with $g_D=(c-s)^2$ and $g_S=(c+s)^2$. Here the two gains are actual squares; since $c^2-s^2=1$, they are reciprocal in the chapter’s abstract notation.

Each series coefficient is a finite multiset of charge/oscillator monomials, with multiplicity recording addition. The coefficient computation uses finite Cauchy sums and a binomial identity justified by the represented relations. This does not assert commutation in the free syntax algebra or multiplicativity of the vacuum functional. The product of two vertex series is the Cauchy product of coefficients, and the Gaussian/Wick theorem says that only even degrees survive. The exact degree-$2k$ coefficient in the main correlator is
$$
L^{-2}\,\text{phase}\,\frac{(-2\,g_J\,D_1(x,y))^k}{k!},
$$
and the odd coefficients are $0$. The two $L^{-1}$ factors are both genuine normalizations, one from each of the two vertices, so the total prefactor is $L^{-1}L^{-1}=L^{-2}$.

The normal conventions are the actual scalar-formal-series multipliers
$$
\exp_f(g_J\,H_M\,t^2)\qquad\text{and}\qquad \exp_f(H_M\,t^2),
$$
with $H_M$ the harmonic cutoff. Each vertex receives one multiplier; its two-point contract multiplies the Weyl correlator by the Cauchy product of two copies of that multiplier. In the customary scalar exponential notation these products are written as the factors $\exp_f(2\,g_J\,H_M\,t^2)$ and $\exp_f(2\,H_M\,t^2)$. The proved contracts retain these twofold scalar Cauchy products explicitly. They are not a separate creation/annihilation factorization and not a standalone BCH identity: the normal vertices are defined by these scalar convolutions, and the locked theorems extract those factors from the coefficientwise product.

The S1 moments supply the Gaussian coefficient calculation: the ordered Wick theorem gives the polynomial moments needed for the Gaussian coefficient extraction, and the odd moments vanish. The exact two-point formula is therefore the promoted S2 correlator theorem, while the earlier exponential language in the chapter should be read as reference formulas that need additional BCH-style interpretation if one wants to compare them with other presentations.

The construction is coefficientwise. Evaluation at $t=1$, analytic convergence and identification with finite CAR observables each require separate results. S3 now proves formal duality and charge-indexed functional transport; its Hamiltonian and physical-state limitations remain explicit below.


#### S3 verified realization: formal duality and charge-family transport

The [S3 formal duality module](../../Bosonize/Core/V1S3FormalDuality.lean)
constructs the involution on the same charge/polynomial carrier used in S2.
It reflects the left charge and applies parity to the right oscillator
variables. On represented coefficients it intertwines the actions at
$P=(c,s)$ and $P^*=(c,-s)$, so the two representation kernels correspond.

The canonical Klein phases and oscillator-field transformation prove (20.10)
coefficient by coefficient. Constant phase multiplication here scales each
summand of the finite multiset presentation; a scalar Cauchy product would
retain extra zero-scaled summands. The ordered Weyl, dressed-normal and
bare-normal functional identities retain the phase
$\zeta^x\overline{\zeta^y}$ and their written product order. Functional
covariance relates $(P,N)$ to $(P^*,(N_R,-N_L))$; it asserts no invariance of
an arbitrary fixed-charge functional.

[Appendix A09's constructive realization](../appendices/a09_duality_spin_and_umklapp.md#constructive-realization-in-lean-formal-duality)
explains the basis, polynomial-derivative and formal-power arguments. Exact
declaration mappings and validation evidence belong to the
[S3 companion](../../docs/companion/Bosonize/Core/V1S3FormalDuality.md).
The Hamiltonian assertion in (20.11) remains an unformalized reference target:
S3 contains neither the complete algebra-valued Hamiltonian nor its covariance
proof. Finite-CAR identification, physical interacting-state comparison,
analytic evaluation and continuum interpretation remain separate obligations.

#### S4 verified realization: exact finite current-word moments

The [S4 current-word module](../../Bosonize/Core/V1S4FiniteCurrentComparison.lean)
connects the algebraic oscillator polynomials to actual finite CAR current
states. Fix a positive regulator $h$, the band of size $L=2h$, admissible
integer charges $N_\nu$, and two distinct species assigned to the oscillator
orientations. A mode indexed by $i\in\{0,\ldots,M-1\}$ has the positive weight
$m=i+1$. The free-word substitution is
$$
\Theta(C_{\nu m})=\rho_\nu(+m),\qquad
\Theta(A_{\nu m})=\rho_\nu(-m).
$$
The positive density transfer raises excitation energy; the negative transfer
lowers it. Creation is multiplication by the corresponding polynomial variable,
and annihilation is $m$ times its derivative. There is no square-root
normalization. The substitution preserves the displayed order of free words;
it does not assert oscillator commutation relations on the entire finite
Fock space.

For an exponent array $r=(r_{\nu m})$, the polynomial-to-current map sends
$X^r$ to the ordered product of $r_{\nu m}$ copies of each positive current,
applied to the finite free sea $\Omega_N$. It extends by finite coefficient
sums. The polynomial energy is
$$
\mathcal E(r)=\sum_{\nu,m} m\,r_{\nu m},
$$
which differs from the number of polynomial factors. On polynomials whose
monomials satisfy $\mathcal E(r)\le K$, the image lies in the actual fixed-charge
total-energy budget. Under $2K+|N_\nu|\le h$ for every species, the map has the
exact weighted Gram form
$$
\langle J_N X^r,J_N X^t\rangle
 =\delta_{rt}\prod_{\nu,m}m^{r_{\nu m}}r_{\nu m}!,
$$
with the corresponding sesquilinear identity for arbitrary polynomials in
that domain. Its restricted kernel is zero. The normalization is the Hall
partition factor of the actual current states. The image is contained in the
span of partitions using parts at most $M$; no surjectivity onto the whole
energy budget is asserted when $M<K$.

A displayed word acts from its right edge. The path certificate records the
excitation energy of each active species after every such step. A creation
adds $m$ in its species. An annihilation requires the source margin
$m+E_\nu+|N_\nu|\le h$; if $E_\nu<m$, it kills that branch. Otherwise the
certificate continues with that species energy reduced by $m$. Every live
intermediate total energy must stay within $K$. These are numerical checks
on suffixes, rather than an assumed equality of the two actions. The selected
word theorems also retain the global Gram margin $2K+|N_\nu|\le h$.

The proof tracks a scalar monomial through this execution. Positive-current
commutativity handles insertion of a part. The finite Haldane lowering theorem
removes a matching part with coefficient $m r_{\nu m}$; the species tensor
realization transfers that identity to the multispecies carrier. A lowering
mode above the relevant energy annihilates the actual vector by the
one-species negative-budget theorem. Pairing with the sea extracts the
polynomial constant coefficient, giving
$$
\langle\Omega_N,\Theta(w)\Omega_N\rangle=\omega_0(w)
$$
for every covered word. This method uses a sufficient certified domain; it
does not claim that its combined margins are optimal.

For the squeezed functional, expand the actual inverse Bogoliubov
substitution before checking the paths. Each generator independently keeps
its label with coefficient $c$, or flips creation/annihilation and orientation
with coefficient $-s$. Every branch with nonzero total coefficient must be
covered. Linearity then proves
$$
\langle\Omega_N,\Theta(\beta_P^{-1}(w))\Omega_N\rangle=\omega_P(w).
$$
The same comparisons hold for finite linear combinations with the stated
word-by-word branch coverage. A convenient fully proved numerical criterion is
$$
|w|\le d,\qquad 2dM+|N_\nu|\le h\quad\text{for every species}.
$$
It derives the certificates with $K=dM$, including every inverse-substitution
branch because substitution preserves word length. The regulator therefore
depends explicitly on the maximum word length.

The checked examples include the empty-mode constant case, unsqueezed
contractions and mixed species at $h=4,M=1$, and an order-sensitive fourth-order
word at $h=8,M=1$. For $c=5/4,s=3/4$, both the quadratic and fourth-order
dressed comparisons have explicit finite regulators. Raw free-sea currents
still give the unsqueezed functional: for instance the mixed annihilator pair
has zero $\omega_0$ expectation and nonzero $\omega_P$ expectation at these
nonzero squeeze parameters. The inverse substitution is essential.

This establishes selected transformed-observable moments in a free finite
sea. It constructs no interacting ground state and identifies no finite
interacting density matrix with $\omega_P$. Physical field/vertex equality,
intermediate-projection residuals, full-budget surjectivity, finite particle-hole
symmetry and analytic or thermodynamic limits remain separate obligations.
Exact declarations, reviewed hashes and validation receipts are in the
[S4 companion](../../docs/companion/Bosonize/Core/V1S4FiniteCurrentComparison.md).

## Constructive realization in Lean: finite interacting states and moment limits (S5)

The S4 comparison evaluates transformed observables in the free finite sea.
An interacting state requires a separate construction. Fix admissible integer
charges $N_\nu$, a regulator $h>0$, and a total excitation budget $K$.
Let $W_{h,N,K}$ be the actual fixed-charge budget subspace of the finite CAR
Hilbert space, and let $i:W_{h,N,K}\hookrightarrow\mathcal H_h$ be inclusion.
The interacting operator used here is the Chapter 17 bosonized Hamiltonian,
including its full charge zero-mode and chemical-potential terms. Its budget
Hamiltonian is
$$
H_W=i^\dagger H i.
$$
Compression retains the effect of leaving and returning to the budget inside
an ambient product. In general it does not preserve products:
$i^\dagger XYi$ need not equal $(i^\dagger Xi)(i^\dagger Yi)$.

Inclusion is isometric, $i^\dagger i=1_W$, and $ii^\dagger$ is the actual
coordinate projection onto the budget. The ambient Hamiltonian is Hermitian,
so $H_W$ is Hermitian. The admissible finite sea supplies a nonzero vector in
$W_{h,N,K}$. Finite-dimensional spectral theory therefore gives a unit vector
$\psi$ and a real energy $E$ satisfying
$$
H_W\psi=E\psi,\qquad
E\|v\|^2\le\operatorname{Re}\langle v,H_Wv\rangle
\quad(v\in W_{h,N,K}).
$$
This is a minimum on the entire budget. It makes no assertion that $i\psi$
minimizes the uncompressed ambient Hamiltonian. Existence here requires no
small-coupling assumption: every nonzero finite Hermitian problem has a
lowest eigenvalue, although that fact supplies no uniform regulator limit.

The corresponding functional on ambient operators is
$$
\omega_\psi(X)=\langle\psi,i^\dagger Xi\psi\rangle
             =\langle i\psi,Xi\psi\rangle.
$$
It is complex linear, normalized at the identity, and positive because
$\omega_\psi(X^\dagger X)=\|Xi\psi\|^2$. Its definition places compression
only outside the whole ambient observable.

The excitation filtration gives a sharp obstruction to unrestricted moment
matching with the squeezed oscillator functional. For $m>0$, negative current
transfer lowers the total excitation grade by $m$. Consequently
$$
K<qm\quad\Longrightarrow\quad
\rho_\nu(-m)^qv=0\qquad(v\in W_{h,N,K}).
$$
The grade has a nonnegative floor; this argument uses the actual lowering
map, rather than deducing nilpotence from finite dimension. It follows that
$$
\langle v,\rho_\nu(m)^q\rho_\nu(-m)^qv\rangle=0.
$$
The same vanishing is proved separately for products of compressed currents:
lowering stays in the budget, which justifies transporting its powers through
inclusion. The two compression placements are separate results.

Under the fixed raw dictionary $C_{\nu,m}\mapsto\rho_\nu(m)$ and
$A_{\nu,m}\mapsto\rho_\nu(-m)$, the squeezed oscillator value instead is
$$
\omega_P(C_{\nu,m}^qA_{\nu,m}^q)=q!(m s^2)^q.
$$
For nonzero squeeze and $K<qm$, this value is positive. Thus no budget vector
state can match all these raw oscillator moments. This does not contradict
S4's word-dependent, inverse-Bogoliubov comparison in the free sea: it uses a
different state/observable construction and keeps its finite margins explicit.

A complete small model demonstrates the issue already at selected quadratic
moments. Take two species, zero charges, $h=8$, $K=M=2$, and
$(v_F,g_4,g_2,\mu)=(1,32\pi,30\pi,\mu_{\rm canonical})$.
The normalized partition basis is ordered as vacuum, $R1$, $L1$, $R11$,
$L11$, $R1L1$, $R2$, $L2$. Here $R11=C_{R,1}^2Ω/\sqrt2$, $L11=C_{L,1}^2Ω/\sqrt2$,
$R2=C_{R,2}Ω/\sqrt2$, and $L2=C_{L,2}Ω/\sqrt2$.
Its span is the entire budget, of dimension eight.
Writing $\alpha=\pi/8$, the derived matrix has diagonal
$\alpha(0,17,17,34,34,34,34,34)$, with the only off-diagonal entries
$H_{0,5}=H_{5,0}=15\alpha$. Every entry is obtained from the actual currents
and the Chapter 17 operator, including the final projection of channels
outside the budget.

The full spectrum, with multiplicities, is
$$
\alpha(17-\sqrt{514}),\quad
17\alpha\ (2\text{ times}),\quad
34\alpha\ (4\text{ times}),\quad
\alpha(17+\sqrt{514}).
$$
With $\eta=15/(17+\sqrt{514})$, the selected ground vector is
$\psi=(|0\rangle-\eta|R1L1\rangle)/\sqrt{1+\eta^2}$.
Together with this ground vector, the remaining eigenvectors form a complete
orthonormal basis, so the
minimum is verified on all eight dimensions, not only on the coupled block.
For ambient products with final compression, its exact moments are
$$
\omega_\psi(\rho_R(1)\rho_R(-1))
 =\frac{1-17/\sqrt{514}}2,\qquad
\omega_\psi(\rho_R(1)\rho_L(1))
 =-\frac{15}{2\sqrt{514}}.
$$
Both differ from the corresponding oscillator values $9/16$ and $-15/16$ at
$c=5/4,s=3/4$. The concrete example supports the general finite-state
construction and obstruction. It supplies no physical-field equality,
continuum exponent, thermodynamic gap, or analytic limit. Physical-field and
residual norm comparisons remain S6 work.

See the [S5 companion](../../docs/companion/Bosonize/Core/V1S5FiniteInteractingStates.md)
and [finite-state source](../../Bosonize/Core/V1S5FiniteGroundState.lean) for
precise contracts and validation evidence.
