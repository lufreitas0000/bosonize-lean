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

Chapter 15.10 is missing both the prefactor i and the relative minus sign. The factor `(ζ^m−1)/m` is not a constant. Forward difference does not exactly cancel 1/m. A low-momentum approximation cannot prove an exact lattice equality.

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

The original chapter 16.3 omits this factor two. The identity for the sum of φ and θ squares supplies another factor two. With `ε(m)=L(ζ^m−1)(ζ^−m−1)/m²`, the resulting field Hamiltonian is `4 Σ_(ν,m) ε(m)ρ_mνρ_−mν` for the stated field normalization. Define the total Sugawara sum explicitly before subtracting its scaled version; the original error formula has inconsistent factors.

**Theorem (Exact Finite Field Hamiltonian):**
With the weight $\varepsilon(m) = L(\zeta^m - 1)(\zeta^{-m} - 1)/m^2$, the exact field Hamiltonian is given by $4 \sum_{\nu,m} \varepsilon(m)\rho_{m,\nu}\rho_{-m,\nu}$.

*Lean 4 Proof Strategy:*
1. Combine the normal-ordered squares of $\Delta\varphi_\nu(x)$.
2. Prove that $\varepsilon(m)$ algebraically simplifies to real/positive terms using properties of roots of unity.
3. Express the Hamiltonian algebraically as this finite weighted sum of density operators.

For the canonical exponential root, the product in ε is `4 sin²(πm/L)≥0`. Keep the algebraic form primary. The limiting constant `4π²/L` is transcendental and is not automatically an element of the cyclotomic number field. Work in ℂ if using this comparison constant, or use an explicitly chosen algebraic reference weight such as ε(1), which is a different comparison.

An exact error operator is a finite weighted sum. A Taylor leading term or RG irrelevance statement requires separately specified asymptotic/error estimates. It is not an exact finite algebraic proportionality. Ground states in every admissible charge sector are annihilated by the lowering modes; therefore the error does not vanish only on the single N=0 vacuum.
