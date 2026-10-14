# Appendix A06 proposal: chiral signs and exact lattice field kernels

## Separate species from chirality

Independent species commute, but identical copies of the same chiral representation have the same commutator sign. Under the chapter 15 definitions, write C(x,y)=[ϕ_R(x),ϕ_R(y)]=[ϕ_L(x),ϕ_L(y)]. Then

$$
 [\phi(x),\phi(y)]=2C(x,y),\quad
 [\theta(x),\theta(y)]=2C(x,y),\quad
 [\phi(x),\theta(y)]=0.
$$

These are the opposite of the asserted cancellation pattern. Introduce a chirality orientation η∈{+1,−1} and construct its field expansion explicitly.

**Definition (Chiral Field Expansion):**
Let $\eta \in \{+1, -1\}$ be the chirality orientation. The chiral field is defined as:
$$
 \varphi_\eta(x)=i\sum_{m=1}^M\frac1m
 (\zeta^{\eta mx}\rho_{-m,\eta}-\zeta^{-\eta mx}\rho_{m,\eta}).
$$

*Lean 4 Proof Strategy:*

1. Define a type for `Chirality` with two values (e.g., `inductive Chirality | L | R`, mapped to $+1, -1$).
2. Formalize the sum using `Finset.sum` over `Icc 1 M`.
3. The operators $\rho_{m,\eta}$ act on a Hilbert space, so the sum evaluates to a linear map `V → V`. Use the `Module.End ℂ V` algebra.
4. Characters $\zeta$ should be defined using roots of unity in `ℂ` or a cyclotomic extension.

**Lemma (Chiral Field Commutators):**
With opposite spatial kernels for different chiralities, the self-commutator cancellation and nonzero $\varphi$--$\theta$ commutator are correctly established.

*Lean 4 Proof Strategy:*

1. Expand the commutators $[\varphi_\eta(x), \varphi_{\eta'}(y)]$ using bilinearity of the commutator.
2. Apply the known Kac-Moody algebra commutators for $\rho_{m, \eta}$ and $\rho_{m', \eta'}$.
3. Evaluate the resulting character sums to obtain the exact lattice kernel $C(x,y)$.

The reversed spatial character gives opposite chiral kernels while retaining the same current convention. Alternatively reverse the left momentum/sea convention; that changes its energy and density dictionary and must be propagated. Do not simply assume an opposite sign incompatible with previously defined identical copies.

With opposite kernels, the desired self-commutator cancellation and nonzero φ–θ commutator can be derived. Keep M explicit and enforce margins for all currents actually used, on the actual right-suffix inputs at each substitution.

## Exact gradient and zero-mode obstruction

**Lemma (Exact Forward Difference of Chiral Field):**
For the positive orientation field as originally defined, the exact forward difference $\Delta f(x) = f(x+1) - f(x)$ is:
$$
 \Delta\varphi(x)=i\sum_{m=1}^M\frac1m
 ((\zeta^m-1)\zeta^{mx}\rho_{-m}
 -(\zeta^{-m}-1)\zeta^{-mx}\rho_m).
$$

*Lean 4 Proof Strategy:*

1. Apply the $\Delta$ operator directly to the formal sum of $\varphi(x)$.
2. Use the linearity of $\Delta$ to move it inside the `Finset.sum`.
3. Use $\zeta^{m(x+1)} - \zeta^{mx} = (\zeta^m - 1)\zeta^{mx}$ to obtain the result algebraically.

**Theorem (Global Obstruction and Fluctuations):**
An identity $[\varphi(x),\Delta\theta(y)]=i C \delta_M(x−y)$ with $C \neq 0$ is impossible for periodic fields. A fluctuation-field commutator must have zero average, and requires an explicit subtraction of the zero-mode contribution.

*Lean 4 Proof Strategy:*

1. Prove that $\sum_y \Delta \theta(y) = 0$ due to periodic boundary conditions on the finite lattice (telescoping sum).
2. Show that summing the commutator $[\varphi(x), \Delta\theta(y)]$ over $y$ must yield $0$.
3. Note that $\sum_y \delta_M(x-y) = 1$, contradicting $iC = 0$ if $C \neq 0$. Thus the theorem holds by contradiction.

Three separate constructions are possible:

- Retain Δ and define the exact differentiated finite kernel; do not call it a constant times δ_M.
- Use a spectral derivative with multiplier proportional to m on the retained nonzero modes; state its nonlocal lattice definition and Nyquist/zero-mode conventions.
- Define lattice-adapted fields using inverse nonzero difference multipliers instead of 1/m, obtaining an exact density-gradient relation for those fields. Check conjugation and Hermiticity explicitly.

For the current program, retaining Δ with its exact kernel is the smallest mathematical change.

## Kernel identities and corner cases

**Definition (Dirac Delta Kernel):**
The periodic delta kernel is defined by finite character sums:
$$
\delta_M(t) = \frac{1}{L} \sum_{m=-M}^M \zeta^{mt}
$$
At $t=0$, $\delta_M(0)=(2M+1)/L$.

*Lean 4 Proof Strategy:*

1. Define $\delta_M(t)$ directly as a `Finset.sum` over `Icc (-M) M`.
2. Prove the value at $t=0$ by evaluating the sum where $\zeta^{0} = 1$, leading to the cardinality of the index set over $L$.
3. The Dirichlet quotient representation should be a separate lemma valid for $t \not\equiv 0 \pmod L$.

The finite sum $\sum_m\sin(2\pi mt/L)/m$ is a truncated Fourier series, not an exact piecewise-linear sawtooth or the exact inverse kernel of Δ. An inverse difference kernel has coefficients $(\zeta^m-1)^{-1}$ on nonzero modes, not 1/m. Define any claimed Green function by an equation it must satisfy and prove that equation.

**Definition (Operator-Valued Spatial Shift):**
A module-valued spatial shift/difference linear map that is evaluated on operator-valued fields without requiring commutativity of the coefficient algebra.

*Lean 4 Proof Strategy:*

1. Do not use `forwardDiff` from Chapter 2 if it strictly requires a commutative ring.
2. Define the periodic operator-valued difference on `ZMod L` by `fun x => f (x+1) - f x`, with `f : ZMod L → Module.End ℂ V`. An ℤ function is a periodic lift only when that periodicity is proved.
3. Prove linearity of `opForwardDiff` and any summation by parts formula without using commutativity of the `End` algebra.

> [!NOTE]
> **Proof-review clarification (2026-10-09):** For the actual periodic fields, use the domain `ZMod L`; an ℤ-domain wrapper is a periodic lift, not a replacement domain. The difference uses only the additive structure of the codomain, so it needs no commutative multiplication on `Module.End`. Prove additive/scalar compatibility once and keep the product order explicit in summation by parts.

## Correct square and normalization audit

Define normal ordering on symbols as in A02. For one chiral field with the Hermitian expansion above, the two mixed terms in the square both contribute. Provided retained indices cannot alias modulo L,

**Lemma (Normal Ordered Square of Forward Difference):**
$$
 \sum_x :\!(\Delta\varphi_\nu(x))^2\!:
 =2L\sum_{m=1}^M
 \frac{(\zeta^m-1)(\zeta^{-m}-1)}{m^2}\rho_{m,\nu}\rho_{-m,\nu}.
$$

*Lean 4 Proof Strategy:*

1. Expand the product of sums for $(\Delta\varphi_\nu(x))^2$.
2. Apply the normal ordering operator $:\! \dots \!:$.
3. Exchange the spatial sum over $x$ and the momentum sums over $m, m'$.
4. Use the orthogonality of characters $\sum_x \zeta^{(m \pm m')x} = L \delta_{m, \mp m'}$ to collapse the double momentum sum into a single sum, producing the factor $2L$ from the cross terms.

With the identity for the sum of $\phi$ and $\theta$ squares supplying another factor of two, and with $\varepsilon(m)=L(\zeta^m-1)(\zeta^{-m}-1)/m^2$, the resulting field Hamiltonian is $4 \sum_{\nu \in \{+1,-1\}} \sum_{m=1}^M \varepsilon(m)\rho_{m,\nu}\rho_{-m,\nu}$ under the no-aliasing condition $2M < L$.

**Definition (Total Two-Branch Sugawara Hamiltonian):**
At mode cutoff $M$, the reference total Sugawara Hamiltonian is:
$$
 H_{\text{sug}}^{(M)} := \sum_{\nu \in \{+1,-1\}} \sum_{m=1}^M \rho_{m,\nu}\rho_{-m,\nu}.
$$

**Theorem (Exact Finite Field Hamiltonian):**
With weight $\varepsilon(m) = L(\zeta^m - 1)(\zeta^{-m} - 1)/m^2$, the exact field Hamiltonian on budget vectors is given by $H_{\text{field}}^{(M)} = 4 \sum_{\nu,m=1}^M \varepsilon(m)\rho_{m,\nu}\rho_{-m,\nu}$.

*Lean 4 Proof Strategy:*

1. Combine the normal-ordered squares of $\Delta\varphi_\nu(x)$.
2. Prove that $\varepsilon(m)$ algebraically simplifies to real/positive terms using properties of roots of unity.
3. Express the Hamiltonian algebraically as this finite weighted sum of density operators.

For the canonical exponential root, the product in $\varepsilon$ is $4 \sin^2(\pi m/L) \ge 0$. Keep the algebraic form primary. The limiting constant $4\pi^2/L$ is transcendental and is not automatically an element of the cyclotomic number field. Work in $\mathbb{C}$ if using this comparison constant, or use an explicitly chosen algebraic reference weight such as $g_0 := \varepsilon(1)$.

**Kernel and Excited Witnesses:**
The exact error operator $E_{\text{error}}^{(M)} := H_{\text{field}}^{(M)} - 4 g_0 H_{\text{sug}}^{(M)} = 4 \sum_{\nu,m=1}^M (\varepsilon(m) - g_0) \rho_{m,\nu} \rho_{-m,\nu}$ is a finite weighted sum.

- Ground states $|\vec{N}\rangle_0$ in every admissible charge sector are annihilated by the lowering modes $\rho_{-m,\nu}$, so $\mathcal{H}_0 \subseteq \ker(E_{\text{error}}^{(M)})$.
- Any excited state composed purely of excitations in modes $m$ where $\varepsilon(m) = g_0$ (such as mode $m=1$ when $g_0 = \varepsilon(1)$) also lies in $\ker(E_{\text{error}}^{(M)})$.
- Nonzero action requires excitation in at least one mode $m \in \{1,\dots,M\}$ with $\varepsilon(m) \neq g_0$; when $M \ge 2$, single-mode state $\psi = \rho_{m,\nu}|\vec{N}\rangle_0$ for $m \ge 2$ provides an explicit nonzero witness: $E_{\text{error}}^{(M)} \psi = 4 m (\varepsilon(m) - g_0) \psi \neq 0$.

A Taylor leading term or RG irrelevance statement requires separately specified asymptotic/error estimates under a defined scaling sequence $(L_n, M_n)$. It is not an exact finite algebraic identity, and should be kept as physical motivation.


## Constructive realization in Lean

The preceding proposal, formulas, alternatives, and “Lean 4 Proof Strategy”
paragraphs are preserved as reference material. The strategies are historical
suggestions; the verified A06 realization is the following finite supporting
construction. Its [formal source](../../Bosonize/Core/A06ChiralFields.lean) and
[companion notebook](../../docs/companion/Bosonize/Core/A06ChiralFields.md)
map the sixteen proved contracts. Fresh Phase B compiler and axiom checks passed;
[completed Phase C validation](../../note/ch15_phase_c_validation_2026-10-13.md) records promotion and acceptance.

**Occupation carrier and transport of the current algebra.** The implementation
uses the existing finite multispecies Fock space with orthonormal occupation
kets and ambient complex linear operators. An occupation assigns each species
an integer charge $N_\nu$ and nonnegative excitation energy. The joint budget
is the span of configurations with these charges and total excitation at most
$K$. A species energy is bounded by that total. On each occupation ket, a linear
tensor insertion transports the single-species current identity into the joint
space; extending by linearity proves it on every vector of the budget. For
integer modes $p,q$ the sufficient condition is

$$
|p|+|q|+K+|N_\nu|\le h,
\qquad
[\rho_{p,\nu},\rho_{q,\nu}]v
=\begin{cases}-p\,v,&p+q=0,\\0,&p+q\ne0.\end{cases}
$$

This is an identity on the stated input subspace. Current products retain their
ambient order and are not compressed to the original budget between actions.
The bound $2M+K+|N_\nu|\le h$ covers every pairing retained in a chiral field.

**Characters, orientation, and actual adjoints.** Space is the residue lattice
$\mathbb Z/(2h)$, with $h>0$ for the current theorem and a nonzero lattice size
for the character and finite spatial-sum theorems. The character is
$\chi_k(z)=\zeta^{k\widetilde z}$. For a primitive $(2h)$-th root, its shift and
conjugation laws are proved with representative independence. The integer-domain
wrapper is separately proved periodic. Reversing the spatial orientation in the
field preserves the existing current convention and gives

$$
[\varphi_\eta(x),\varphi_\eta(y)]v=\eta S_M(x,y)v,
\qquad
S_M(x,y)=\sum_{m=1}^M
\frac{\chi_m(x-y)-\chi_{-m}(x-y)}{m}.
$$

The proof expands all four current pairings before using their budget identities.
Only the diagonal modes survive; $[\rho_m,\rho_{-m}]$ contributes $-m$, and
$i^2=-1$ supplies the required field sign. Distinct species commute globally.
The adjoint is the actual finite Hilbert-space adjoint: conjugation exchanges
the characters and sends $i/m$ to $-i/m$, while current adjoints exchange modes.
Thus each chiral field is globally self-adjoint. The resulting CH15 mixed
commutator is exactly $2S_M$, with no extra $i$ or $1/(2h)$ inserted into $S_M$.
The sine expression applies to the canonical exponential root and is not an
additional proved arbitrary-root identity.

**Exact finite differences, kernels, and nonzero witnesses.** The periodic
forward difference is additive, compatible with complex scalar multiplication,
and has zero spatial sum. Its chiral expansion has exactly the multipliers
$\zeta^{\pm\eta m}-1$ displayed above. In particular, the proof does not identify
this difference with an exact constant times density. The Dirichlet kernel has
diagonal value $(2M+1)/(2h)$ when $h>0$, and spatial sum one for primitive $\zeta$
under $2M<2h$. Character orthogonality and the no-alias bound exclude all nonzero
retained multiples of the lattice size. The differentiated skew kernel sums
to zero.

Every admissible charge sector has a nonzero ground ket in its joint budget.
The concrete parameters $h=4$, $M=1$, $K=0$, zero charges, and distinct species
$0,1\in\operatorname{Fin}(2)$ satisfy the margins and no-alias bound. These
witnesses make the budget claims non-vacuous. CH15's zero-mode obstruction then
uses the actual nonzero ground ket: summing an assumed nonzero multiple of the
unsubtracted Dirichlet kernel gives $c g$, whereas summing the periodic
commutator difference gives zero. Zero-mode-subtracted kernels and the alternative
field constructions listed above are not excluded by that conclusion.

**Boundary of the implemented portion.** These sixteen A06 contracts cover
characters, periodic differences, chiral adjoints and restricted commutators,
Dirichlet identities, and ground witnesses. The preserved “Correct square and
normalization audit” section and its Hamiltonian/error formulas remain reference
targets for later work. Normal-ordered squares, field Hamiltonians, excited error
witnesses, Green functions, continuum or scaling limits, and RG estimates are
not proved by this A06 module. Their presence here does not extend the verified
scope to CH16 or analytic claims.


## Constructive realization of normal ordering and field energy in Lean

The earlier realization section describes the sixteen contracts of the A06
module accepted with Chapter 15. Its scope statement remains a historical
record of that module. The separate CH16 construction now realizes the finite
normal-ordering and field-energy targets above through
[A07FiniteNormalOrdering](../../Bosonize/Core/A07FiniteNormalOrdering.lean)
and [Ch16FieldHamiltonian](../../Bosonize/Core/Ch16FieldHamiltonian.lean).
The [A07 companion](../../docs/companion/Bosonize/Core/A07FiniteNormalOrdering.md)
and [CH16 companion](../../docs/companion/Bosonize/Core/Ch16FieldHamiltonian.md)
record exact declarations and validation. These source links identify the
proved and frozen Core modules; [final Phase C validation](../../note/ch16_phase_c_validation_2026-10-13.md) records acceptance.
The A07 module here supports this appendix's normal-ordering construction;
it does not implement the separate interactions appendix numbered A07.

**Quadratic symbols before evaluation.** A signed-current label records a
branch, a retained index $i\in\operatorname{Fin}(M)$, and a creator flag. Its
positive mode is $m=i+1$, so all denominators represent nonzero modes. A quadratic
symbol is a complex coefficient function on ordered pairs of these labels.
Raw evaluation multiplies the represented currents in their original order.
Normal evaluation swaps a creator on the right past an annihilator on the left;
other pairs retain their order. Both evaluations concern the supplied symbol,
rather than a proposed operation on an already evaluated endomorphism. This
keeps distinct representations of the same operator from being silently confused.
Normal evaluation is proved additive and compatible with complex scalar
multiplication.

For a same-branch annihilator of mode $m$ followed by a creator of mode $n$,
the difference between normal and raw evaluation is
$[\rho_n,\rho_{-m}]$. On an actual joint-budget input, with
$2M+K+|N_\nu|\le h$, this difference is $-m\delta_{mn}$ times that input.
The sign follows the existing current convention; no global central extension
is assumed. Operators act in the ambient finite occupation Fock space without
intermediate budget projections.

**Exact coefficients and two surviving spatial terms.** The linear combination
of signed currents with the gradient coefficients is proved equal to the
existing periodic chiral forward difference. The proof explicitly matches
$\operatorname{Fin}(M)$ with $\{1,\ldots,M\}$ and retains the full multipliers
$\zeta^{\pm\eta m}-1$. At each spatial point, the coefficient identity
$(a+b)^2+(a-b)^2=2(a^2+b^2)$ cancels the two ordered cross terms separately.
This is algebra on scalar coefficient functions and needs no commutative
multiplication of current operators.

For primitive $\zeta$ and $2M<2h$, finite character orthogonality leaves exactly
the two opposite-sign pairings with equal positive mode. Normal evaluation sends
both to $\rho_{m,\nu}\rho_{-m,\nu}$, and each has spatial coefficient

$$
\varepsilon(m)=\frac{2h}{m^2}
 (\zeta^m-1)(\zeta^{-m}-1).
$$

Thus one chiral spatial square gives $2\sum_m\varepsilon(m)
\rho_{m,\nu}\rho_{-m,\nu}$. The dual-field coefficient identity supplies another
factor two, giving the reference factor four for the two branches. The finite
symbol collapse admits an ambient operator proof; the frozen chapter contracts
state its consequences on budget inputs and retain their explicit margins.

**The realized error witnesses.** The algebraic reference weight is
$g_0=\varepsilon(1)$. CH16 proves that the error kills the admissible ground ket
and the single excitation $\rho_{1,\nu}g$. More generally, for a retained
positive $m$ and sufficient input margins,

$$
E_{\mathrm{error}}\rho_{m,\nu}g
=4m\bigl(\varepsilon(m)-\varepsilon(1)\bigr)\rho_{m,\nu}g.
$$

The excited ket is proved nonzero using the restricted current commutator and
the genuine nonzero ground ket. A concrete witness uses $h=8$, $M=2$, $K=2$,
zero charges, two distinct species, and the canonical root of order sixteen;
the unequal weights are proved algebraically. The implementation does not
establish the reference's broader kernel assertion for arbitrary products of
reference-mode excitations. That multiword extension, analytic scaling limits,
RG estimates, general positivity claims, and Green-function constructions retain
separate obligations.


Independent final pedagogical reviewer `/root/characters` returned PASS for all
five documents after the link and historical-prose corrections. Both complete
reference prefixes are preserved, declaration mappings and predicted promoted
hashes are checked, the mathematics matches the proved contracts, and scope
limitations are explicit. No required findings remain. This review precedes the
runner's promoted compiler/axiom/CI acceptance and does not replace those gates.
