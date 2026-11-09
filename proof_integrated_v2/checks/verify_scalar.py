#!/usr/bin/env python3
"""Exact checks for two scalar-proof simplifications, with no legacy imports.

The universal derivations are in NS_P14_INTEGRATED_PROOF_JA.md section 11.  This checks the new
rational-function identity coefficient by coefficient, the seven small rational
comparisons, and optional finite diagnostics of the frozen-cutoff argument.
"""
if not __debug__:
    raise RuntimeError("Run without -O: exact checks use assertions")

from fractions import Fraction as Q
from math import comb
import argparse
import json


def add(p, q):
    out = [Q(0)] * max(len(p), len(q))
    for i, c in enumerate(p):
        out[i] += c
    for i, c in enumerate(q):
        out[i] += c
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def scale(p, c):
    return [Q(c) * x for x in p]


def mul(p, q):
    out = [Q(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] += x * y
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def rf_add(left, right):
    p, q = left
    u, v = right
    return add(mul(p, v), mul(u, q)), mul(q, v)


def harmonic(n):
    return sum((Q(1, j) for j in range(1, n + 1)), Q(0))


def triangular(r):
    return r * (r + 1) // 2


def threshold(r, eps=None):
    a = triangular(r)
    if eps is None:
        eps = a % 2
    return (Q(a * (a + 22 - r), 2 * (r - 1) * (a + 9))
            + Q(2 * r - 3, r - 1)
            - Q(a * (a + 21) + 36, (a + 4 - eps) * (a + 9)))


def barrier(r):
    return Q(r, 4) + 1 + Q(9, 2 * r)


def check_new_symbolic_identity():
    # Ascending polynomial coefficients.  Construct T_1 from its definition.
    a = [Q(0), Q(1, 2), Q(1, 2)]
    a9 = add(a, [9])
    t1 = (mul(a, add(a, [22, -1])),
          scale(mul([-1, 1], a9), 2))
    t2 = ([-3, 2], [-1, 1])
    t3 = (scale(add(mul(a, add(a, [21])), [36]), -1),
          mul(add(a, [3]), a9))
    # L(r) = (r^2 + 4r + 18)/(4r).
    numerator, denominator = rf_add(
        rf_add(rf_add(t1, t2), t3), ([-18, -4, -1], [0, 4]))
    expected_numerator = [972, -900, 111, -148, -5, 2]
    expected_denominator = [2]
    for factor in ([0, 1], [-1, 1], [6, 1, 1], [18, 1, 1]):
        expected_denominator = mul(expected_denominator, factor)
    assert mul(numerator, expected_denominator) == mul(expected_numerator, denominator)
    # The readable positive grouping, rather than a coefficient-shift table.
    grouped = add(add(mul([0, 0, 0, 1], add(mul([-10, 1], [15, 2]), [2])),
                      mul([0, 1], add(scale([-10, 1], 111), [210]))), [972])
    assert grouped == expected_numerator


def slope(d, r, n, h):
    return d - 1 - (r - 1) * (h - 2 + Q(d + 2, n + 1))


def gap(e, d, r, n, h):
    m = e + d - 1
    v = Q(2 * e + d - 3, 2)
    alpha = Q(r - 1, n + 1)
    k = d + Q(d, n + 1) * (v - 1) + m * (h - 2 + Q(2, n + 1))
    return d * (v + 1) - m - (r - 1) * k + (Q(r + 1, 2) - alpha) * triangular(r)


def upper_direct(e, d, r, n):
    m = e + d - 1
    v = Q(2 * e + d - 3, 2)
    alpha = Q(r - 1, n + 1)
    c = Q(r + 1, 2) - alpha
    return (alpha * d * v + (r - 1 - alpha) * d + c * (m - triangular(r))
            + sum((Q(r - 1, t + 1) - alpha) * m for t in range(2, n)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--diagnostic-rank', type=int, default=30)
    parser.add_argument('--diagnostic-span', type=int, default=12)
    args = parser.parse_args()
    check_new_symbolic_identity()
    h23 = harmonic(23)
    assert Q(747, 200) - h23 == Q(2107451, 2974571600) > 0
    seeds = []
    for r in range(4, 10):
        n = triangular(r) // 2 + 1
        margin = threshold(r) - Q(747, 200) + Q(2 * (23 - n), n + 24)
        assert margin > 0
        seeds.append({'rank': r, 'rational_margin': str(margin)})
    new_anchor_margin = barrier(10) - Q(747, 200) - Q(65, 336)
    assert new_anchor_margin == Q(181, 8400) > 0
    smallest_gap = smallest_step = None
    diagnostics = 0
    for r in range(4, args.diagnostic_rank + 1):
        a = triangular(r)
        n = a // 2 + 1  # This remains fixed when d increases.
        h = harmonic(n)
        alpha = Q(r - 1, n + 1)
        a0 = slope(a, r, n, h)
        g0 = gap(10, a, r, n, h)
        c = Q(a * (-a * (n - r + 2) - n * (r - 4) + 3), 2 * (n + 1))
        b0 = a0 + 11 - r - 8 * alpha
        f = -c / (a + 9) + 11 - r - 8 * alpha
        f1 = (Q(a, 2) - Q(3 * r, 2) + Q(11, 2)
              + Q(3 * (5 * r + 31), 2 * (a + 9)) - Q(17 * (r - 1), a + 3))
        assert g0 == (r - 1) * (a + 9) * (threshold(r) - h)
        assert g0 == (a + 9) * a0 + c
        assert c < 0 and g0 > 0 and a0 > 0
        assert b0 > f >= f1 > Q(1, 4)
        if r >= 10:
            assert h < barrier(r) < threshold(r, 1) <= threshold(r)
            assert barrier(r + 1) - barrier(r) - Q(2, r) == Q(r * r - 7 * r - 26, 4 * r * (r + 1)) > 0
        for t in range(args.diagnostic_span + 1):
            d = a + t
            value = gap(10, d, r, n, h)
            assert slope(d, r, n, h) == a0 + t * (1 - alpha)
            assert value == g0 + t * b0 + (1 - alpha) * comb(t, 2)
            assert value == d * (Q(17 + d, 2) + 1) - upper_direct(10, d, r, n)
            step = gap(10, d + 1, r, n, h) - value
            assert step == b0 + t * (1 - alpha) > Q(1, 4)
            assert gap(11, d, r, n, h) - value == slope(d, r, n, h) > 0
            smallest_gap = value if smallest_gap is None else min(smallest_gap, value)
            smallest_step = step if smallest_step is None else min(smallest_step, step)
            diagnostics += 1
    print(json.dumps({'new_barrier_identity': 'all polynomial coefficients match',
                      'rank_4_to_9_margins': seeds,
                      'new_rank_10_anchor_margin': str(new_anchor_margin),
                      'frozen_cutoff_diagnostics': diagnostics,
                      'diagnostic_rank_range': [4, args.diagnostic_rank],
                      'diagnostic_delta_minus_a_range': [0, args.diagnostic_span],
                      'minimum_gap': str(smallest_gap),
                      'minimum_forward_gap_difference': str(smallest_step),
                      'scope': 'Universal derivations in manuscript section 11; finite diagnostics are supplementary.'},
                     indent=2))


if __name__ == '__main__':
    main()
