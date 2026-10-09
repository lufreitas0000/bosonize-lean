# Appendix A06 proposal: chiral signs and exact lattice field kernels

## Separate species from chirality

Independent species commute, but identical copies of the same chiral representation have the same commutator sign. Under the chapter 15 definitions, write C(x,y)=[ϕ_R(x),ϕ_R(y)]=[ϕ_L(x),ϕ_L(y)]. Then

\[
 [\phi(x),\phi(y)]=2C(x,y),\quad
 [\theta(x),\theta(y)]=2C(x,y),\quad
 [\phi(x),\theta(y)]=0.
\]

These are the opposite of the asserted cancellation pattern. Introduce a chirality orientation η∈{+1,−1} and construct its field expansion explicitly.

**Definition (Chiral Field Expansion):**
Let $\eta \in \{+1, -1\}$ be the chirality orientation. The chiral field is defined as:
\[
 \varphi_\eta(x)=i\sum_{m=1}^M\frac1m
 (\zeta^{\eta mx}\rho_{-m,\eta}-\zeta^{-\eta mx}\rho_{m,\eta}).
\]

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

With opposite kernels, the desired self-commutator cancellation and nonzero φ–θ commutator can be derived. Keep M explicit and enforce margins for all currents actually used, including intermediate vectors.

## Exact gradient and zero-mode obstruction

**Lemma (Exact Forward Difference of Chiral Field):**
For the positive orientation field as originally defined, the exact forward difference $\Delta f(x) = f(x+1) - f(x)$ is:
\[
 \Delta\varphi(x)=i\sum_{m=1}^M\frac1m
 ((\zeta^m-1)\zeta^{mx}\rho_{-m}
 -(\zeta^{-m}-1)\zeta^{-mx}\rho_m).
\]

*Lean 4 Proof Strategy:*
1. Apply the $\Delta$ operator directly to the formal sum of `\varphi(x)`.
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
\[
\delta_M(t) = \frac{1}{L} \sum_{m=-M}^M \zeta^{mt}
\]
At $t=0$, $\delta_M(0)=(2M+1)/L$.

*Lean 4 Proof Strategy:*
1. Define $\delta_M(t)$ directly as a `Finset.sum` over `Icc (-M) M`.
2. Prove the value at $t=0$ by evaluating the sum where $\zeta^{0} = 1$, leading to the cardinality of the index set over $L$.
3. The Dirichlet quotient representation should be a separate lemma valid for $t \not\equiv 0 \pmod L$.

The finite sum `Σ sin(2πmt/L)/m` is a truncated Fourier series, not an exact piecewise-linear sawtooth or the exact inverse kernel of Δ. An inverse difference kernel has coefficients `(ζ^m−1)⁻¹` on nonzero modes, not 1/m. Define any claimed Green function by an equation it must satisfy and prove that equation.

**Definition (Operator-Valued Spatial Shift):**
A module-valued spatial shift/difference linear map that is evaluated on operator-valued fields without requiring commutativity of the coefficient algebra.

*Lean 4 Proof Strategy:*
1. Do not use `forwardDiff` from Chapter 2 if it strictly requires a commutative ring.
2. Define `opForwardDiff (f : ℤ → Module.End ℂ V) : ℤ → Module.End ℂ V` as `fun x => f (x + 1) - f x`.
3. Prove linearity of `opForwardDiff` and any summation by parts formula without using commutativity of the `End` algebra.

> [!NOTE]
> **Proof-review clarification (2026-10-09):** For the actual periodic fields, use the domain `ZMod L`; an ℤ-domain wrapper is a periodic lift, not a replacement domain. The difference uses only the additive structure of the codomain, so it needs no commutative multiplication on `Module.End`. Prove additive/scalar compatibility once and keep the product order explicit in summation by parts.

## Correct square and normalization audit

Define normal ordering on symbols as in A02. For one chiral field with the Hermitian expansion above, the two mixed terms in the square both contribute. Provided retained indices cannot alias modulo L,

**Lemma (Normal Ordered Square of Forward Difference):**
\[
 \sum_x :\!(\Delta\varphi_\nu(x))^2\!:
 =2L\sum_{m=1}^M
 \frac{(\zeta^m-1)(\zeta^{-m}-1)}{m^2}\rho_{m,\nu}\rho_{-m,\nu}.
\]

*Lean 4 Proof Strategy:*
1. Expand the product of sums for $(\Delta\varphi_\nu(x))^2$.
2. Apply the normal ordering operator $:\! \dots \!:$.
3. Exchange the spatial sum over $x$ and the momentum sums over $m, m'$.
4. Use the orthogonality of characters $\sum_x \zeta^{(m \pm m')x} = L \delta_{m, \mp m'}$ to collapse the double momentum sum into a single sum, producing the factor $2L$ from the cross terms.

With the identity for the sum of $\phi$ and $\theta$ squares supplying another factor of two, and with $\varepsilon(m)=L(\zeta^m-1)(\zeta^{-m}-1)/m^2$, the resulting field Hamiltonian is $4 \sum_{\nu \in \{+1,-1\}} \sum_{m=1}^M \varepsilon(m)\rho_{m,\nu}\rho_{-m,\nu}$ under the no-aliasing condition $2M < L$.

**Definition (Total Two-Branch Sugawara Hamiltonian):**
At mode cutoff $M$, the reference total Sugawara Hamiltonian is:
\[
 H_{\text{sug}}^{(M)} := \sum_{\nu \in \{+1,-1\}} \sum_{m=1}^M \rho_{m,\nu}\rho_{-m,\nu}.
\]

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
