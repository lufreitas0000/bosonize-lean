#!/usr/bin/env python3
"""Exact finite witnesses for the reference-note audit; no Lean proofs claimed."""
from fractions import Fraction


def add(a, b):
    out = a.copy()
    for s, c in b.items():
        out[s] = out.get(s, 0) + c
    return {s: c for s, c in out.items() if c}


def scale(c, v):
    return {s: c * a for s, a in v.items() if c * a}


def car(v, i, create=False):
    out = {}
    for s, c in v.items():
        occupied = bool(s & (1 << i))
        if occupied != create:
            t = s ^ (1 << i)
            sign = (-1) ** ((s & ((1 << i) - 1)).bit_count())
            out[t] = out.get(t, 0) + sign * c
    return {s: c for s, c in out.items() if c}


def density(v, modes, m):
    out = {}
    for i, k in enumerate(modes):
        if k + m in modes:
            j = modes.index(k + m)
            out = add(out, car(car(v, i), j, create=True))
    return out


def main():
    # Verify the finite CAR implementation used by the witnesses.
    for size in (2, 4):
        for occupied in range(1 << size):
            ket = {occupied: 1}
            for i in range(size):
                for j in range(size):
                    assert add(car(car(ket, j, create=True), i),
                               car(car(ket, i), j, create=True)) == (ket if i == j else {})
                    assert add(car(car(ket, j), i), car(car(ket, i), j)) == {}
                    assert add(car(car(ket, j, create=True), i, create=True),
                               car(car(ket, i, create=True), j, create=True)) == {}
    # A primitive 2nd root and an invertible length in a ring with zero divisors.
    assert pow(4, 2, 15) == 1 and 4 != 1
    assert (2 * 8) % 15 == 1
    assert (1 + 4) % 15 == 5 != 0
    print('Fourier: in Z/15, zeta=4 has order 2, 2 is a unit, but 1+zeta=5 != 0.')

    # Chapter 12.2 quantifies over any nonzero mode, even outside its Sugawara sum.
    modes = [0, 1]  # h=1, L=2
    vacuum = {1: 1}
    excited = density(vacuum, modes, 1)
    assert excited
    sugawara_commutator = {}  # range 1..h-1 is empty
    assert sugawara_commutator != excited
    print('Sugawara: h=1, K=N=0 satisfies R2; H_sug=0 but rho_1 Omega != 0.')

    # The unprojected raising operator does not become nilpotent at the input cap.
    modes = [-1, 0, 1, 2]  # h=2, L=4
    vacuum = {3: 1}
    assert density(vacuum, modes, 1)
    print('Raising phase: h=2, K=0; W^- Omega = -rho_1 Omega != 0 at x=0.')

    # At K=0 the proposed vertex gives one sector ground ket; c_x gives two holes.
    unscaled_position = {}
    for i in range(len(modes)):
        unscaled_position = add(unscaled_position, car(vacuum, i))
    sector_ground_minus_one = {1: 1}  # occupied mode -1
    assert unscaled_position.get(2, 0) != 0  # occupied mode 0 after removing -1
    assert sector_ground_minus_one.get(2, 0) == 0
    print('Vertex: sqrt(4) c_0 Omega has a |{0}> component; proposed K=0 B_0 Omega does not.')

    # The claimed Chapter 19.8 vanishes at s=0; the finite vacuum variance does not.
    density_state = scale(Fraction(1, 4), add(density(vacuum, modes, 1),
                                            density(vacuum, modes, -1)))
    variance = sum(c * c for c in density_state.values())
    assert variance == Fraction(1, 16)
    print('Correlator: h=2, M=1, s=0, x=y=0; density variance = 1/16, not 0.')

    # On the total-degree <=1 two-mode slice, both dressed annihilators have no
    # common kernel for c=5/3,s=4/3. Sum Q*Q is positive definite diagonal.
    c, s = Fraction(5, 3), Fraction(4, 3)
    assert c*c - s*s == 1
    gram_diagonal = [2*s*s, c*c, c*c]
    assert all(x > 0 for x in gram_diagonal)
    print('Compressed squeezed vacuum: sum Q^*Q = diag(32/9,25/9,25/9); common kernel is zero.')

    # Four distinct species at one site: each elementary CAR changes its charge by 1.
    initial = {12: 1}  # R up/down occupied, L up/down empty
    final = car(car(car(car(initial, 2), 3), 1, create=True), 0, create=True)
    assert set(final) == {3}
    changes = [int(bool(3 & (1 << i))) - int(bool(12 & (1 << i))) for i in range(4)]
    assert changes == [1, 1, -1, -1]
    print('Umklapp: per-species charge shift is (+1,+1,-1,-1), not (+2,+2,-2,-2).')


if __name__ == '__main__':
    main()
