# Appendix A06 proposal: chiral signs and exact lattice field kernels

## Separate species from chirality

Independent species commute, but identical copies of the same chiral representation have the same commutator sign. Under the chapter 15 definitions, write C(x,y)=[ϕ_R(x),ϕ_R(y)]=[ϕ_L(x),ϕ_L(y)]. Then

\[
 [\phi(x),\phi(y)]=2C(x,y),\quad
 [\theta(x),\theta(y)]=2C(x,y),\quad
 [\phi(x),\theta(y)]=0.
\]

These are the opposite of the asserted cancellation pattern. Introduce a chirality orientation η∈{+1,−1} and construct its field expansion explicitly, e.g.

\[
 \varphi_\eta(x)=i\sum_{m=1}^M\frac1m
 (\zeta^{\eta mx}\rho_{-m,\eta}-\zeta^{-\eta mx}\rho_{m,\eta}).
\]

The reversed spatial character gives opposite chiral kernels while retaining the same current convention. Alternatively reverse the left momentum/sea convention; that changes its energy and density dictionary and must be propagated. Do not simply assume an opposite sign incompatible with previously defined identical copies.

With opposite kernels, the desired self-commutator cancellation and nonzero φ–θ commutator can be derived. Keep M explicit and enforce margins for all currents actually used, including intermediate vectors.

## Exact gradient and zero-mode obstruction

For the positive orientation field as originally defined, the exact forward difference is

\[
 \Delta\varphi(x)=i\sum_{m=1}^M\frac1m
 ((\zeta^m-1)\zeta^{mx}\rho_{-m}
 -(\zeta^{-m}-1)\zeta^{-mx}\rho_m).
\]

Chapter 15.10 is missing both the prefactor i and the relative minus sign. The factor `(ζ^m−1)/m` is not a constant. Forward difference does not exactly cancel 1/m. A low-momentum approximation cannot prove an exact lattice equality.

There is also a global obstruction: summing any periodic forward difference over y yields zero. The kernel `δ_M(t)=L⁻¹ Σ_(m=−M)^M ζ^(mt)` includes the zero mode and sums to one over the lattice. Thus an identity `[φ(x),Δθ(y)]=i C δ_M(x−y)` with C≠0 is impossible for periodic fields. A fluctuation-field commutator must have zero average, including an explicit subtraction of the zero-mode contribution, and the actual difference multipliers still have to be retained.

Three separate constructions are possible:

- Retain Δ and define the exact differentiated finite kernel; do not call it a constant times δ_M.
- Use a spectral derivative with multiplier proportional to m on the retained nonzero modes; state its nonlocal lattice definition and Nyquist/zero-mode conventions.
- Define lattice-adapted fields using inverse nonzero difference multipliers instead of 1/m, obtaining an exact density-gradient relation for those fields. Check conjugation and Hermiticity explicitly.

For the current program, retaining Δ with its exact kernel is the smallest mathematical change.

## Kernel identities and corner cases

Define all kernels by finite character sums first. The Dirichlet quotient involving a sine denominator is a secondary evaluation valid away from coincident sites; at t=0 define `δ_M(0)=(2M+1)/L`. For M=h−1 this is `(L−1)/L`. A totalized division by zero does not supply this value.

The finite sum `Σ sin(2πmt/L)/m` is a truncated Fourier series, not an exact piecewise-linear sawtooth or the exact inverse kernel of Δ. An inverse difference kernel has coefficients `(ζ^m−1)⁻¹` on nonzero modes, not 1/m. Define any claimed Green function by an equation it must satisfy and prove that equation.

Chapter 2's `forwardDiff` requires a commutative coefficient ring. The coefficient algebra of operator-valued fields is noncommutative, so it cannot be instantiated with `Module.End ℂ V`. Define a module-valued spatial shift/difference linear map (whose formula is the same evaluation difference), or use the explicit difference formula and prove it compatible with the scalar chapter 2 construction. No commutativity of operator multiplication is needed for the spatial map.

## Correct square and normalization audit

Define normal ordering on symbols as in A02. For one chiral field with the Hermitian expansion above, the two mixed terms in the square both contribute. Provided retained indices cannot alias modulo L,

\[
 \sum_x :\!(\Delta\varphi_\nu(x))^2\!:
 =2L\sum_{m=1}^M
 \frac{(\zeta^m-1)(\zeta^{-m}-1)}{m^2}\rho_{m,\nu}\rho_{-m,\nu}.
\]

The original chapter 16.3 omits this factor two. The identity for the sum of φ and θ squares supplies another factor two. With `ε(m)=L(ζ^m−1)(ζ^−m−1)/m²`, the resulting field Hamiltonian is `4 Σ_(ν,m) ε(m)ρ_mνρ_−mν` for the stated field normalization. Define the total Sugawara sum explicitly before subtracting its scaled version; the original error formula has inconsistent factors.

For the canonical exponential root, the product in ε is `4 sin²(πm/L)≥0`. Keep the algebraic form primary. The limiting constant `4π²/L` is transcendental and is not automatically an element of the cyclotomic number field. Work in ℂ if using this comparison constant, or use an explicitly chosen algebraic reference weight such as ε(1), which is a different comparison.

An exact error operator is a finite weighted sum. A Taylor leading term or RG irrelevance statement requires separately specified asymptotic/error estimates. It is not an exact finite algebraic proportionality. Ground states in every admissible charge sector are annihilated by the lowering modes; therefore the error does not vanish only on the single N=0 vacuum.
