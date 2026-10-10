# BOSONIZE-LEAN: Mathematical Reference Notes

This document provides the rigorous mathematical specification for the lattice AQFT bosonization in 1+1D. Every claim is an exact identity between finite-dimensional or purely algebraic objects. There are no unbounded operators, no analytical limits, and no approximations in the formal layer.

## Part I: Phase 1 Foundations

### Chapter 1: Lattice and Band Geometry

In 1+1-dimensional lattice quantum field theory, the exact specification of the discrete spatial manifold and its Fourier-dual momentum space is foundational. Let $L \ge 1$ be a strictly positive integer, representing the number of lattice sites. From Chapter 5 onwards, we will strictly require $L = 2h$ with $h > 0$ to be an even integer to ensure a half-filled Fermi sea (note that the centered integer band $\Lambda^* = \{-h+1, \dots, h\}$ is intrinsically asymmetric, retaining the positive Nyquist mode $h = L/2$, so the lattice coordinates and band representatives are not reflection-symmetric).

**Definition 1.1 (Spatial Lattice).** The 1D spatial lattice is defined as the periodic ring of $L$ sites, identified with the additive quotient group of integers modulo $L$.

*Lean 4 Proof Strategy:*

- Formalize the spatial lattice $\Lambda$ using Lean's `ZMod L`.

- Ensure $L : \mathbb{N}$ is endowed with a `[NeZero L]` or $L \ge 1$ typeclass/hypothesis.

- Periodic boundary conditions are naturally and exactly handled by the modular arithmetic of `ZMod L`.

- Auxiliary info: The physical interpretation implies a discrete 1D crystal with exact translation invariance mod $L$.

$$
\Lambda := \mathbb{Z}/L\mathbb{Z} \tag{1.1}
$$

 Positions are denoted by spatial variables $x, y \in \Lambda$. Periodic boundary conditions are inherent to the quotient group structure.

**Definition 1.2 (Momentum Band).** The momentum space (also called the dual lattice or Brillouin zone) is defined as the centered integer interval containing exactly $L$ elements.

*Lean 4 Proof Strategy:*

- Formalize $\Lambda^*$ as a subtype of integers: `{k : ℤ // -(L : ℤ) < 2 * k ∧ 2 * k ≤ (L : ℤ)}`.

- Auxiliary lemmas: Prove that `Fintype.card (Band L) = L`. Show that when `L` is even, this interval is exactly $[-L/2 + 1, L/2]$.

- Physical note: This discrete Brillouin zone avoids ultraviolet divergences by truncating momenta exactly, without relying on analytical cutoffs.

$$
\Lambda^* := \left\{ k \in \mathbb{Z} \ \Big\vert{}\ -L < 2k \le L \right\} \tag{1.2}
$$

 Momenta are denoted by variables $k, p, q \in \Lambda^*$. For $L$ even, the band is explicitly the set $\{-L/2+1, \dots, L/2\}$. Physical momentum is scaled as $2\pi k/L$.

**Constructive and Computable Enumeration:**
While $\Lambda^*$ is conceptually an abstract subtype of $\mathbb{Z}$, in formal computation we represent it via a decidable predicate and a bounded interval filter:
$$
\mathrm{bandFinset}(L) := \{ k \in \mathbb{Z} \cap [-L, L] \mid -L < 2k \le L \} \tag{1.2a}
$$
In Lean 4 (`Ch01LatticeBand.lean`), `Band L` is endowed with `Fintype (Band L)` constructively via `Fintype.ofFinset (bandFinset L)`, avoiding any reliance on non-constructive choice or classical logic for basic counting.

**Definition 1.3 (Projections and Band Arithmetic).** Because physical momenta must often be added (e.g., in scattering processes), the sum of two momenta $k, k' \in \Lambda^*$ may exceed the bounds of the band. We define standard mappings to project back into the valid band. Let $\pi$ be the canonical quotient map that takes an integer to its periodic equivalence class:

*Lean 4 Proof Strategy:*

- Formalize $\pi$ as the canonical projection `ℤ → ZMod L`.

- Reuse the frozen `Bosonize.Ch01` definitions and centered representative built from `ZMod.val`. Its positive Nyquist endpoint is already proved; do not substitute a different minimum-absolute-value convention or redefine the band.

- Define band addition $k \oplus k'$ as $r(\pi(k) + \pi(k'))$ and band negation $\ominus k$ as $r(-\pi(k))$.

- Physical note: The wrapping behavior of $k \oplus k'$ precisely models Umklapp scattering processes, where quasi-momentum is conserved modulo a reciprocal lattice vector.

$$
\pi : \mathbb{Z} \to \Lambda, \quad \pi(k) = k \bmod L \tag{1.3}
$$

**The Abstract Section and the Explicit Centered Lift:**
Abstractly, $r$ is the unique section of $\pi$ whose image lands in $\Lambda^*$:
$$
r : \Lambda \to \Lambda^* \tag{1.4}
$$
such that $\forall x \in \Lambda, \ \pi(r(x)) = x$ and $\forall k \in \Lambda^*, \ r(\pi(k)) = k$.

*Explicit Computational Construction:*
For computational and constructive evaluation (as formalized in `Ch01.representative`), every element $x \in \mathbb{Z}/L\mathbb{Z}$ has a standard unsigned residue $x.\mathrm{val} \in \{0, 1, \dots, L-1\}$. The centered lift is defined piecewise:
$$
r(x) := \begin{cases}
x.\mathrm{val} & \text{if } 2(x.\mathrm{val}) \le L, \\
x.\mathrm{val} - L & \text{if } 2(x.\mathrm{val}) > L.
\end{cases} \tag{1.4a}
$$
*Example:*

- For $L = 4$ (even, $h = 2$): the residues $\{0, 1, 2, 3\}$ map to $r(0) = 0$, $r(1) = 1$, $r(2) = 2 = +L/2$ (since $2 \times 2 \le 4$), and $r(3) = 3 - 4 = -1$. The resulting band is $\{-1, 0, 1, 2\} = [-h+1, h]$. The positive Nyquist boundary $+2$ is retained, and $-2$ is excluded.

- For $L = 5$ (odd): residues $\{0, 1, 2, 3, 4\}$ map to $r(0)=0, r(1)=1, r(2)=2$, $r(3)=3-5=-2$, $r(4)=4-5=-1$. The band is $\{-2, -1, 0, 1, 2\}$, which is fully symmetric.

We define the transported group addition on the band, denoted $\oplus$, to safely wrap momenta:

$$
\forall k, k' \in \Lambda^*, \quad k \oplus k' := r(\pi(k) + \pi(k')) \tag{1.5}
$$

$$
\forall k \in \Lambda^*, \quad \ominus k := r(-\pi(k)) \tag{1.6}
$$

**Lemma 1.4 (Band Properties).**

*Lean 4 Proof Strategy:*

- **Cardinality:** Prove `Fintype.card (Band L) = L`. This is a direct consequence of the properties of integer intervals of length $L$.

- **Bijection:** Prove that $\pi$ and $r$ define an equivalence (`Equiv`) between $\Lambda^*$ and `ZMod L`. You'll need auxiliary lemmas for $r \circ \pi = \mathrm{id}_{\Lambda^*}$ and $\pi \circ r = \mathrm{id}_{\Lambda}$.

- **Wrap Lemma:** To prove $k \oplus k' = k + k' - wL$, observe that $(k + k') - (k \oplus k')$ must be a multiple of $L$. Since $k, k' \in (-L/2, L/2]$, their sum $k + k'$ is bounded within $(-L, L]$. Thus the wrapping multiple $w$ is restricted to $\{-1, 0, 1\}$.

- **Nyquist Mode:** Assuming `Even L`, show $L/2 \in \Lambda^*$. Because $\pi(-L/2) = \pi(L/2)$ in `ZMod L`, $r(\pi(-L/2)) = L/2$, proving $\ominus (L/2) = L/2$. For $k \neq L/2$, $k \in (-L/2, L/2)$, meaning $-k$ stays in the same open bounds, so no wrapping occurs and $\ominus k = -k$.

1. **Cardinality:** The number of elements is strictly $L$.
$$
\#\Lambda^* = L \tag{1.7}
$$

2. **Bijection:** The map $\pi$ restricted to $\Lambda^*$ is a canonical bijection with inverse $r$, establishing the equivalence `Band L ≃ Lattice L`.

3. **Wrap Lemma & Explicit Umklapp Multiplier:** For any $k, k' \in \Lambda^*$, normal integer addition relates to band addition via a unique wrapping integer $w \in \{-1, 0, 1\}$:

   $$
   k \oplus k' = k + k' - wL \tag{1.8}
   $$

   *Explicit Formula for $w$ (`band_add_wrap`):*
   $$
   w(k, k') = \begin{cases}
   -1 & \text{if } 2(k + k') \le -L, \\
   +1 & \text{if } 2(k + k') > L, \\
   0 & \text{if } -L < 2(k + k') \le L.
   \end{cases} \tag{1.8a}
   $$
   *Physical Meaning:* In lattice scattering, when two fermions collide with total incoming quasi-momentum $k + k' > L/2$, they wrap back into the Brillouin zone with $w = +1$, transferring momentum $L$ (in units of $2\pi/L$, a reciprocal lattice vector) to the underlying crystal lattice.

4. **Nyquist Mode & Parity Inversion:**
   - For $L$ even, the positive boundary mode behaves uniquely under negation:

   $$
   \ominus (L/2) = L/2 \tag{1.9}
   $$

   $$
   \forall k \neq L/2, \quad \ominus k = -k \tag{1.10}
   $$

   - For $L$ odd, every mode reflects symmetrically without any self-inverse boundary mode (`odd_band_neg`):
   $$
   \forall k \in \Lambda^*, \quad \ominus k = -k \tag{1.11}
   $$

---

#### 1.5 Remark: Spatial Boundary Twists versus Graded Locality (von Delft–Schoeller Convention)

In the literature on constructive fermionic bosonization—most notably **von Delft and Schoeller (vDS 1998, cond-mat/9805275v3, Eqs. 2, 3, 5)**—chiral fermions on a finite interval of length $L$ are frequently defined with a spatial boundary holonomy:
$$
\psi_r(x + L) = \tau_r \psi_r(x), \qquad \tau_r = e^{i 2\pi \beta_r} \tag{1.12}
$$
In vDS notation, $\beta_r = (1 - \delta_b)/2$ (or $\tau = -e^{i\pi \delta_b}$). Setting $\delta_b = 1$ (or $\beta = 0$) corresponds to periodic boundary conditions (PBC), whereas $\delta_b = 0$ (or $\beta = -1/2$) yields standard **anti-periodic boundary conditions (APBC)**:
$$
\psi(x + L) = -\psi(x).
$$

**Why vDS Uses Half-Integer Shifted Momenta ($\beta = -1/2$):**

1. **Symmetric Half-Filled Fermi Sea:**
   For a linear chiral dispersion, shifting single-particle momenta to half-integers $k_n = \frac{2\pi}{L}(n - 1/2)$ removes the zero label $k = 0$, creating a strictly reflection-symmetric discrete band around zero. This allows an even number of fermions (a half-filled sea) to form a non-degenerate ground state.
   *(Scope Limit: This half-integer label shift eliminates zero modes for linear chiral dispersion; it does not eliminate Umklapp processes or edge artifacts for arbitrary lattice dispersions).*

2. **Bosonic Periodicity:**
   Because physical density operators $\rho(x) = \psi^\dagger(x) \psi(x)$ are bilinear in fermions, the boundary phase cancels:
   $$
   \rho(x + L) = (\tau^* \psi^\dagger(x))(\tau \psi(x)) = |\tau|^2 \rho(x) = \rho(x).
   $$
   Thus, bosonic density modes always carry integer wavevectors $q = \frac{2\pi}{L} m$ ($m \in \mathbb{Z}$), even when fermions carry half-integer wavevectors.

**Independence of Spatial Holonomy and Graded Locality:**
A crucial mathematical distinction established in the project review ([twisted-boundary review](../../note/issue_twisted_boundary_conditions_2026-10-09.md)) is:

- **Spatial Holonomy ($\psi(x+L) = \tau \psi(x)$):** Describes parallel transport around the compact spatial ring.

- **Graded Locality ($A B = (-1)^{\deg A \deg B} B A$):** Describes the graded exchange of local observables in disjoint spatial regions ($I \cap J = \emptyset$).
*Neither determines the other.* In particular, the positive Nyquist mode $+h = +L/2$ in Chapter 1 makes the discrete quotient enumeration on $\mathbb{Z}/L\mathbb{Z}$ complete; it does not implement APBC. Likewise, Chapter 6's proved twisted locality is a property of disjoint supports and cannot detect spatial holonomy $\tau$, because local algebras $\mathfrak{A}(I)$ generated by site operators are invariant under scalar phase rescalings.

**Formal Implementation Architecture in `bosonize-lean`:**

1. **Periodic Core Layer (Chapters 1–6):** The frozen Core sources implement the strictly periodic lattice $\Lambda = \mathbb{Z}/L\mathbb{Z}$ with integer momentum band $\Lambda^* \subset \mathbb{Z}$ and $\tau = 1$.

2. **Additive Spatial-Twist Contract (Planned Supplement):**
   To support arbitrary holonomy $\tau = r^L$ (with $|r| = 1$), one introduces an integer-lift field over $n \in \mathbb{Z}$:
   $$
   c_r(n) := r^n c_0([n]), \qquad c_r(n + L) = r^L c_r(n) = \tau c_r(n) \tag{1.13}
   $$
   where $[n] = n \bmod L \in \mathbb{Z}/L\mathbb{Z}$.

3. **Phase Consistency with Downstream Vertex Operators:**
   The physical comparison field and the reconstructed vertex operator in Chapter 14 must share the exact same phase parameter $r$. In the periodic Core baseline ($\tau = 1, r = 1$), the zero mode $Z(x) = \zeta^{x N}$ is strictly periodic on the lattice, matching $c_x$. For an external twist $\tau$, both the field lift $c_r(n)$ and the source zero mode $Z_r(n) |N\rangle = r^n \zeta^{n N} |N\rangle$ carry the matching holonomy $r^L = \tau$.
