# BOSONIZE-LEAN: Mathematical Reference Notes

This document provides the rigorous mathematical specification for the lattice AQFT bosonization in 1+1D. Every claim is an exact identity between finite-dimensional or purely algebraic objects. There are no unbounded operators, no analytical limits, and no approximations in the formal layer.

## Part I: Phase 1 Foundations

### Chapter 1: Lattice and Band Geometry

In 1+1-dimensional lattice quantum field theory, the exact specification of the discrete spatial manifold and its Fourier-dual momentum space is foundational. Let $L \ge 1$ be a strictly positive integer, representing the number of lattice sites. From Chapter 6 onwards, we will require $L$ to be an even integer to ensure a symmetric Fermi sea.

**Definition 1.1 (Spatial Lattice).** The 1D spatial lattice is defined as the periodic ring of $L$ sites, identified with the additive quotient group of integers modulo $L$.

$$
\Lambda := \mathbb{Z}/L\mathbb{Z} \tag{1.1}
$$

 Positions are denoted by spatial variables $x, y \in \Lambda$. Periodic boundary conditions are inherent to the quotient group structure.

**Definition 1.2 (Momentum Band).** The momentum space (also called the dual lattice or Brillouin zone) is defined as the centered integer interval containing exactly $L$ elements.

$$
\Lambda^* := \left\{ k \in \mathbb{Z} \ \Big\vert{}\ -L < 2k \le L \right\} \tag{1.2}
$$

 Momenta are denoted by variables $k, p, q \in \Lambda^*$. For $L$ even, the band is explicitly the set $\{-L/2+1, \dots, L/2\}$. Physical momentum is scaled as $2\pi k/L$.

**Definition 1.3 (Projections and Band Arithmetic).** Because physical momenta must often be added (e.g., in scattering processes), the sum of two momenta $k, k' \in \Lambda^*$ may exceed the bounds of the band. We define standard mappings to project back into the valid band. Let $\pi$ be the canonical quotient map that takes an integer to its periodic equivalence class:

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
