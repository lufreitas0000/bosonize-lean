# BOSONIZE-LEAN: Mathematical Reference Notes

## Part IV: Phase 4 Free Dynamics & Dual Fields

### Introduction to Phase 4: From Modes to Macroscopic Fields

In Phases 1 through 3, our formalization was strictly algebraic and focused on *kinematics*—the structure of the operators at a fixed time. We built the exact bosonization dictionary by mapping the localized fermionic operator $\psi(x)$ to an exponential of bosonic momentum modes $\rho_m$.

Phase 4 bridges the gap between these discrete momentum modes and the macroscopic, continuous-looking physics of **Luttinger Liquid theory**. In standard 1D physics, the low-energy dynamics are entirely captured by two macroscopic, canonically conjugate scalar fields:
*   $\phi(x)$: The "density" or "displacement" field.
*   $\theta(x)$: The "phase" or "momentum" field.

In a continuous infinite space, these fields satisfy the exact canonical commutation relation $[\phi(x), \partial_y \theta(y)] = i\pi\delta(x-y)$, and the free Hamiltonian looks like a vibrating string: $H_0 \propto \int [(\nabla\phi)^2 + (\nabla\theta)^2]$.

**The Lattice Challenge:** How do we define continuous field derivatives ($\partial_x$) and Dirac delta functions ($\delta(x-y)$) on a strictly finite, discrete integer lattice $\Lambda$ without introducing analytical limits?
**The Solution:** We resurrect the **Umbral Calculus** developed back in Chapter 2. By defining the fields algebraically using the truncated phase operators ($W^+, W^-$), and taking their exact discrete differences ($\Delta, \nabla$), the "vibrating string" Hamiltonian emerges purely algebraically as a finite matrix identity on the energy budget.

---

### Chapter 15: Dual Fields ($\phi$ and $\theta$)

**Physical Intuition (Hydrodynamics of the String):**
If we view the 1D electron gas as an elastic string, the field $\phi(x)$ measures how much the string has been longitudinally displaced (squished or stretched) at position $x$. The spatial gradient of this displacement naturally corresponds to the accumulation of particles—the local density.
The dual field $\theta(x)$ represents the momentum of that string. Its gradient corresponds to the physical current (how fast the string is moving).
Because standard definitions of these fields require summing $1/m$ factors, they are intimately related to the phase operators $W^\pm$ we defined for the Mattis-Mandelstam formula in Chapter 14.

#### 15.1 Defining the Chiral Phase Fields

We begin by defining a strictly Hermitian scalar field for each species branch (e.g., Right-movers and Left-movers). Recall from Chapter 14 (Definitions 14.1) the raising and lowering phase operators $W^+_\nu(x)$ and $W^-_\nu(x)$. Note that taking the Hermitian adjoint swaps the creation and annihilation modes while conjugating the roots of unity, giving exactly: $(W^+_\nu(x))^\dagger = - W^-_\nu(x)$.

To construct an observable (Hermitian) operator, we multiply the difference by the imaginary unit.

**Definition 15.1 (Chiral Fluctuation Field).**
For each species $\nu \in \mathcal{C}$ and spatial position $x \in \Lambda$, the purely bosonic, Hermitian chiral fluctuation field is defined as:

$$
\varphi_\nu(x) := i \left( W^+_\nu(x) + W^-_\nu(x) \right) \tag{15.1}
$$

Expanding this into the raw density modes, we see it matches the standard harmonic oscillator mode expansion for a real scalar field, truncated strictly to the lattice budget:

$$
\varphi_\nu(x) = i \sum_{m=1}^{h-1} \frac{1}{m} \left( \zeta^{mx} \rho_{-m, \nu} - \zeta^{-mx} \rho_{m, \nu} \right) \tag{15.2}
$$

**Lemma 15.2 (Hermiticity).**
The chiral field is exactly self-adjoint on the finite Fock space:

$$
\varphi_\nu^\dagger(x) = \varphi_\nu(x) \tag{15.3}
$$

#### 15.2 The Macroscopic Dual Fields

In systems with both Right-movers ($R$) and Left-movers ($L$), physical observables like the total electron density and current are formed by symmetric and antisymmetric combinations of the chiral fields.

**Definition 15.3 (The Phase and Density Fields).**
Assuming a two-species system $\mathcal{C} = \{R, L\}$, we define the macroscopic dual fields $\phi(x)$ and $\theta(x)$ as:

$$
\phi(x) := \varphi_R(x) + \varphi_L(x) \tag{15.4}
$$

$$
\theta(x) := \varphi_R(x) - \varphi_L(x) \tag{15.5}
$$

*(Note: Depending on the specific sign conventions chosen in the CFT literature, the definitions of* $\phi$ *and* $\theta$ *may carry overall minus signs or factors of* $\sqrt{\pi}$*. The fundamental algebraic structure remains identical).*

#### 15.3 Field Commutators and the Lattice Green's Function

**Physical Intuition (The Lattice Step Function):**
In continuum QFT, the commutator of chiral fields evaluates to a step function $[\varphi(x), \varphi(y)] \propto \mathrm{sgn}(x-y)$, and the cross-commutator of the dual fields evaluates exactly to a step function $[\phi(x), \theta(y)] \propto \mathrm{sgn}(x-y)$.
On our finite lattice, applying the exact Kac-Moody algebra yields a discrete truncated sum. This discrete sum forms a "sawtooth" function—a perfectly linear ramp that jumps at the boundary, which is the exact periodic lattice analog of the continuous step function.

**Theorem 15.4 (Exact Chiral Field Commutator).**
On the strict budget subspace $\mathcal{B}_{K, \vec{N}_{max}}$ under the M2 margin condition, the commutator of the chiral fields evaluates exactly to the discrete lattice Green's function for the difference operator:

$$
[\varphi_\nu(x), \varphi_{\nu'}(y)] = i \delta_{\nu \nu'} \sum_{m=1}^{h-1} \frac{2}{m} \sin\left(\frac{2\pi m (x-y)}{L}\right) I \tag{15.6}
$$

Because the $R$ and $L$ branches commute with each other, it immediately follows that the $\phi$ and $\theta$ fields commute with themselves, but not with each other:

$$
[\phi(x), \phi(y)] = 0 \tag{15.7}
$$

$$
[\theta(x), \theta(y)] = 0 \tag{15.8}
$$

$$
[\phi(x), \theta(y)] = 2i \sum_{m=1}^{h-1} \frac{2}{m} \sin\left(\frac{2\pi m (x-y)}{L}\right) I \tag{15.9}
$$

#### 15.4 Exact Gradients and Local Density

**Physical Intuition (Gradients via Umbral Calculus):**
In the continuum, $\partial_x \phi(x) \propto \rho(x)$. How do we express this strictly on a lattice where spatial sites are discrete integers? We use the exact forward difference operator $\Delta$ from our Umbral Calculus toolkit (Chapter 2): $(\Delta \varphi)(x) = \varphi(x+1) - \varphi(x)$.
Taking the discrete difference of the sum $\sum \frac{1}{m} \zeta^{mx}$ mathematically pulls down a factor of $(\zeta^m - 1)$. For small momenta (low energy modes where $m \ll L$), $(\zeta^m - 1) \approx i \frac{2\pi m}{L}$, which exactly cancels the $1/m$ in the field definition! Thus, the discrete gradient precisely recovers the linear density mode expansion without requiring limits.

**Theorem 15.5 (Umbral Gradient of the Field).**
Applying the exact spatial forward difference operator $\Delta$ to the chiral field algebraically recovers the local fluctuation density up to the exact lattice difference multiplier. For any state on the budget subspace:

$$
(\Delta \varphi_\nu)(x) = \sum_{m=1}^{h-1} \left( \frac{\zeta^m - 1}{m} \zeta^{mx} \rho_{-m, \nu} + \frac{\zeta^{-m} - 1}{m} \zeta^{-mx} \rho_{m, \nu} \right) \tag{15.10}
$$

#### 15.5 The Discrete CCR and the Band-Limited Delta

**Physical Intuition (Pulling out the Derivative):**
How do we evaluate the canonical commutator $[\phi(x), (\Delta \theta)(y)]$? Because the Umbral difference operator $\Delta_y$ acts exclusively on the spatial coordinate $y$ and is merely a linear combination of evaluations (shifting $y \mapsto y+1$ and subtracting), it factors completely outside the algebraic operator commutator! We don't need to compute complex operator sums; we simply apply $\Delta_y$ to the scalar "sawtooth" function we already found in Equation 15.9.

**Lemma 15.6 (Spatial Linearity of Commutators).**
Let $A(x)$ and $B(y)$ be operator-valued functions on the spatial lattice. The spatial difference operator $\Delta_y$ commutes with the Lie bracket:

$$
[A(x), (\Delta B)(y)] = \Delta_y [A(x), B(y)] \tag{15.11}
$$

**Physical Intuition (The Sharpness of a Point and the Dirichlet Kernel):**
When we apply $\Delta_y$ to our sawtooth commutator, the difference algebraically eliminates the $1/m$ scaling. What remains is a sum of pure plane waves: $\sum_{m \neq 0} \zeta^{m(x-y)}$.
In standard Fourier theory, summing all plane waves from $-\infty$ to $\infty$ yields the perfectly sharp Dirac delta function $\delta(x-y)$. However, on our lattice, the budget strictly truncates the sum at $h-1$. Therefore, we do not get an infinitely sharp point (which would require infinite energy).
Instead, we get the exact **Dirichlet kernel**—a "sinc" function that represents a **band-limited discrete delta function**. The physics is beautifully consistent: the uncertainty principle prevents a perfectly sharp spatial commutator when the maximum momentum (energy budget) is strictly capped.

**Definition 15.7 (Band-Limited Discrete Delta / Dirichlet Kernel).**
We define the truncated discrete delta function representing the maximum spatial resolution of the finite momentum band. Adding the missing $m=0$ term for normalization, it evaluates algebraically to:

$$
\tilde{\delta}(x-y) := \frac{1}{L} \sum_{m=-(h-1)}^{h-1} \zeta^{m(x-y)} = \frac{1}{L} \frac{\sin\left(\frac{2\pi (h - 1/2) (x-y)}{L}\right)}{\sin\left(\frac{\pi (x-y)}{L}\right)} \tag{15.12}
$$

**Theorem 15.8 (Discrete Field CCR).**
Evaluating the commutator of the displacement field with the Umbral gradient of the phase field yields the band-limited delta function exactly on the budget subspace. Applying $\Delta_y$ directly to Equation 15.9 algebraically yields:

$$
[\phi(x), (\Delta \theta)(y)] = i C \cdot \tilde{\delta}(x-y) \tag{15.13}
$$
*(where $C$ is an exact lattice-specific scaling constant compensating for the difference between the forward lattice derivative and the continuous derivative).*

#### 15.6 Technical Notes for the Lean 4 Formalization (Chapter 15)

1. **Defining Hermitian Operators:**
   * In Lean, the imaginary unit $i$ is `Complex.I`.
   * Proving Hermiticity (Lemma 15.2) in Lean requires setting up a `star` operation (`StarRing`) on the endomorphism algebra. You will map `star (Complex.I • W)` to `-Complex.I • star W` and use the adjoint lemmas from Chapter 14.

2. **Commutator Sum Evaluations:**
   * Proving Theorem 15.4 requires expanding the commutator of two sums. Lean's `Finset.sum_comm` and `LinearMap.map_sum` will handle the distribution.
   * You will encounter the cross-terms $[\rho_{-m}, \rho_{n}]$. Apply the Kac-Moody theorem (Theorem 10.5) using `span_induction` on the budget space to collapse the double sum into a single sum with $m \delta_{mn}$.
   * The remaining terms combine `\zeta^{m(x-y)} - \zeta^{-m(x-y)}`. Use Euler's formula in `Complex` to identify this uniquely with $2i \sin(\dots)$.

3. **Re-using the Umbral Calculus and Linearity (`Lemma 15.6`):**
   * Do not define a new derivative operator here. Import the exact $\Delta$ `LinearMap` defined over functions $R^\Lambda$ from Chapter 2.
   * Because the commutator `[ , ]` is an operation defined via `LinearMap.commutator` (or similar bilinear maps), and $\Delta_y$ acts exclusively on the $y$ argument, you simply invoke `map_add` and `map_sub` to pull the spatial shift out of the Lie bracket. Lean handles this linearly and algebraically.

4. **The Dirichlet Kernel in Lean:**
   * To formalize the band-limited Delta in Theorem 15.8, use Lean's `geom_sum` (geometric sum) API.
   * The sum of complex exponentials evaluates exactly to the fraction of sines shown in Eq 15.12, which is the exact, closed-form algebraic representation of the Dirichlet kernel discrete delta.
