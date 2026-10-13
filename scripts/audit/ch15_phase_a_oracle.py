#!/usr/bin/env python3
"""Independent finite CAR sanity check for CH15 Phase A.

Standard-library only. Floating-point numerical evidence, NOT a Lean proof,
not an exhaustive test of the theorem contracts, and not imported by Lean.
Run: python3 scripts/audit/ch15_phase_a_oracle.py --output note/ch15_phase_a_oracle_2026-10-13.json
"""
import argparse
import cmath
import json
from collections import defaultdict
from pathlib import Path


def run():
    h, cutoff, budget = 4, 1, 0
    modes = [(species, k) for species in range(2) for k in range(-h + 1, h + 1)]
    ground = frozenset(i for i, (_, k) in enumerate(modes) if k <= 0)
    v = {ground: 1.0 + 0j}
    root = cmath.exp(2j * cmath.pi / (2 * h))
    tolerance = 1e-10

    def combine(*terms):
        out = defaultdict(complex)
        for scalar, vector in terms:
            for occupation, coefficient in vector.items():
                out[occupation] += scalar * coefficient
        return dict(out)

    def rho(species, transfer, vector):
        # c^dagger_(k+transfer) c_k, with ordered-occupation CAR signs.
        out = defaultdict(complex)
        for occupation, coefficient in vector.items():
            for q, (branch, k) in enumerate(modes):
                target = (species, k + transfer)
                if branch != species or q not in occupation or target not in modes:
                    continue
                p = modes.index(target)
                removed = occupation - {q}
                if p in removed:
                    continue
                sign = (-1) ** (sum(i < q for i in occupation) + sum(i < p for i in removed))
                out[frozenset(removed | {p})] += sign * coefficient
        return dict(out)

    def chiral(species, orientation, x, vector):
        terms = []
        for m in range(1, cutoff + 1):
            terms += [(1j * root ** (orientation * m * x) / m, rho(species, -m, vector)),
                      (-1j * root ** (-orientation * m * x) / m, rho(species, m, vector))]
        return combine(*terms)

    def phi(x, vector):
        return combine((1, chiral(0, 1, x, vector)), (1, chiral(1, -1, x, vector)))

    def theta(x, vector):
        return combine((1, chiral(0, 1, x, vector)), (-1, chiral(1, -1, x, vector)))

    def difference(field, y, vector):
        return combine((1, field((y + 1) % (2 * h), vector)), (-1, field(y, vector)))

    def commutator(a, x, b, y, vector):
        return combine((1, a(x, b(y, vector))), (-1, b(y, a(x, vector))))

    def skew(x, y):
        t = (x - y) % (2 * h)
        return sum((root ** (m * t) - root ** (-m * t)) / m for m in range(1, cutoff + 1))

    def delta(x, y):
        return sum(root ** (m * ((x - y) % (2 * h))) for m in range(-cutoff, cutoff + 1)) / (2 * h)

    def residual(vector):
        return max((abs(c) for c in vector.values()), default=0.0)

    maxima = {name: 0.0 for name in ['phi_self', 'theta_self', 'mixed', 'mixed_forward_difference',
                                   'delta_spatial_sum', 'difference_spatial_sum']}
    for x in range(2 * h):
        maxima['delta_spatial_sum'] = max(maxima['delta_spatial_sum'], abs(sum(delta(x, y) for y in range(2 * h)) - 1))
        maxima['difference_spatial_sum'] = max(maxima['difference_spatial_sum'], residual(combine(*[(1, difference(theta, y, v)) for y in range(2 * h)])))
        for y in range(2 * h):
            checks = {'phi_self': commutator(phi, x, phi, y, v),
                      'theta_self': commutator(theta, x, theta, y, v),
                      'mixed': combine((1, commutator(phi, x, theta, y, v)), (-2 * skew(x, y), v)),
                      'mixed_forward_difference': combine((1, commutator(phi, x, lambda t, w: difference(theta, t, w), y, v)),
                                                           (-2 * (skew(x, (y + 1) % (2 * h)) - skew(x, y)), v))}
            for name, value in checks.items():
                maxima[name] = max(maxima[name], residual(value))
    margin = 2 * cutoff + budget <= h
    no_alias = 2 * cutoff < 2 * h
    example = 2 * skew(1, 0)
    passed = margin and no_alias and abs(example) > tolerance and all(x < tolerance for x in maxima.values())
    return {'schema': 1, 'status': 'PASS' if passed else 'FAIL',
            'limitations': 'Numerical finite ground-input sanity checks only; not Lean proofs or universal validation.',
            'parameters': {'h': h, 'M': cutoff, 'K': budget, 'charges': [0, 0], 'species': [0, 1],
                           'root': 'exp(2*pi*i/8)', 'tested_site_pairs': (2*h)**2},
            'branch_margin': margin, 'no_alias': no_alias,
            'mixed_ground_coefficient_x1_y0': {'real': example.real, 'imag': example.imag},
            'tolerance': tolerance, 'max_residuals': maxima}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = run()
    rendered = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end='')
    if report['status'] != 'PASS':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
