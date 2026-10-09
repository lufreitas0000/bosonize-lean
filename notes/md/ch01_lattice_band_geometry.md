# BOSONIZE-LEAN: Mathematical Reference Notes

This document provides the rigorous mathematical specification for the lattice AQFT bosonization in 1+1D. Every claim is an exact identity between finite-dimensional or purely algebraic objects. There are no unbounded operators, no analytical limits, and no approximations in the formal layer.

## Part I: Phase 1 Foundations

### Chapter 1: Lattice and Band Geometry

In 1+1-dimensional lattice quantum field theory, the exact specification of the discrete spatial manifold and its Fourier-dual momentum space is foundational. Let $L \ge 1$ be a strictly positive integer, representing the number of lattice sites. From Chapter 5 onwards, we will strictly require $L = 2h$ with $h > 0$ to be an even integer to ensure a half-filled Fermi sea (note that the centered integer band $\Lambda^* = \{-h+1, \dots, h\}$ is intrinsically asymmetric, retaining the positive Nyquist mode $h = L/2$, so the lattice coordinates and band representatives are not reflection-symmetric).

**Definition 1.1 (Spatial Lattice).** The 1D spatial lattice is defined as the periodic ring of $L$ sites, identified with the additive quotient group of integers modulo $L$.

*Lean 4 Proof Strategy:*
- Formalize the spatial lattice $\Lambda$ using Lean's `ZMod L`.
- Ensure $L : \mathbb{N}$ is endowed with a `[NeZero L]` or `L \ge 1` typeclass/hypothesis.
- Periodic boundary conditions are naturally and exactly handled by the modular arithmetic of `ZMod L`.
- Auxiliary info: The physical interpretation implies a discrete 1D crystal with exact translation invariance mod $L$.

$$
\Lambda := \mathbb{Z}/L\mathbb{Z} \tag{1.1}
$$

 Positions are denoted by spatial variables $x, y \in \Lambda$. Periodic boundary conditions are inherent to the quotient group structure.

**Definition 1.2 (Momentum Band).** The momentum space (also called the dual lattice or Brillouin zone) is defined as the centered integer interval containing exactly $L$ elements.

*Lean 4 Proof Strategy:*
- Formalize $\Lambda^*$ as a subtype of integers: `{k : \mathbb{Z} // -L < 2 * k \land 2 * k \le L}`.
- Auxiliary lemmas: Prove that `Fintype.card \Lambda^* = L`. Show that when `L` is even, this interval is exactly `[-L/2 + 1, L/2]`.
- Physical note: This discrete Brillouin zone avoids ultraviolet divergences by truncating momenta exactly, without relying on analytical cutoffs.

$$
\Lambda^* := \left\{ k \in \mathbb{Z} \ \Big\vert{}\ -L < 2k \le L \right\} \tag{1.2}
$$

 Momenta are denoted by variables $k, p, q \in \Lambda^*$. For $L$ even, the band is explicitly the set $\{-L/2+1, \dots, L/2\}$. Physical momentum is scaled as $2\pi k/L$.

**Definition 1.3 (Projections and Band Arithmetic).** Because physical momenta must often be added (e.g., in scattering processes), the sum of two momenta $k, k' \in \Lambda^*$ may exceed the bounds of the band. We define standard mappings to project back into the valid band. Let $\pi$ be the canonical quotient map that takes an integer to its periodic equivalence class:

*Lean 4 Proof Strategy:*
- Formalize $\pi$ as the canonical projection `\mathbb{Z} \to ZMod L`.
- Formalize $r$ using the symmetric remainder function. Lean's `ZMod.valMinAbs` (which returns values in `(-L/2, L/2]`) is structurally identical and well-suited for this.
- Define band addition $k \oplus k'$ as `r (\pi k + \pi k')` and band negation $\ominus k$ as `r (-\pi k)`.
- Physical note: The wrapping behavior of $k \oplus k'$ precisely models Umklapp scattering processes, where quasi-momentum is conserved modulo a reciprocal lattice vector.

$$
\pi : \mathbb{Z} \to \Lambda, \quad \pi(k) = k \bmod L \tag{1.3}
$$

 Let $r$ be the unique representative function that lifts a periodic site back to the centered momentum band:

$$
r : \Lambda \to \Lambda^* \tag{1.4}
$$

 such that $\forall x \in \Lambda, \ \pi(r(x)) = x$. We define the transported group addition on the band, denoted $\oplus$, to safely wrap momenta:

$$
\forall k, k' \in \Lambda^*, \quad k \oplus k' := r(\pi(k) + \pi(k')) \tag{1.5}
$$

$$
\forall k \in \Lambda^*, \quad \ominus k := r(-\pi(k)) \tag{1.6}
$$

**Lemma 1.4 (Band Properties).**

*Lean 4 Proof Strategy:*
- **Cardinality:** Prove `Fintype.card \Lambda^* = L`. This is a direct consequence of the properties of integer intervals of length $L$.
- **Bijection:** Prove that $\pi$ and $r$ define an equivalence (`Equiv`) between $\Lambda^*$ and `ZMod L`. You'll need auxiliary lemmas for `LeftInverse r \pi` and `RightInverse r \pi`.
- **Wrap Lemma:** To prove $k \oplus k' = k + k' - wL$, observe that $(k + k') - (k \oplus k')$ must be a multiple of $L$. Since $k, k' \in (-L/2, L/2]$, their sum $k + k'$ is bounded within $(-L, L]$. Thus the wrapping multiple $w$ is restricted to $\{-1, 0, 1\}$.
- **Nyquist Mode:** Assuming `Even L`, show $L/2 \in \Lambda^*$. Because $\pi(-L/2) = \pi(L/2)$ in `ZMod L`, $r(\pi(-L/2)) = L/2$, proving $\ominus (L/2) = L/2$. For $k \neq L/2$, $k \in (-L/2, L/2)$, meaning $-k$ stays in the same open bounds, so no wrapping occurs and $\ominus k = -k$.

1. **Cardinality:** The number of elements is strictly $L$.
$$
\#\Lambda^* = L \tag{1.7}
$$

2. **Bijection:** The map $\pi$ restricted to $\Lambda^*$ is a canonical bijection with inverse $r$.

3. **Wrap Lemma:** For any $k, k' \in \Lambda^*$, normal integer addition relates to band addition via a unique wrapping integer $w \in \{-1, 0, 1\}$:

   $$
   k \oplus k' = k + k' - wL \tag{1.8}
   $$

4. **Nyquist Mode:** For $L$ even, the boundary mode behaves uniquely under negation:

   $$
   \ominus (L/2) = L/2 \tag{1.9}
   $$

   $$
   \forall k \neq L/2, \quad \ominus k = -k \tag{1.10}
   $$
