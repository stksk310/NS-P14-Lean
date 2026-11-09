#!/usr/bin/env python3
"""Independent exact-arithmetic supplement for e10_scalar_reduction_JA.md.

The universal argument is in the manuscript. This program independently checks
one harmonic anchor, seven elementary rational comparisons, and the polynomial
identity used by the rank induction. --diagnostic N also checks the original
weighted envelope against the simplified gap and forward differences for
10<=delta<=N at r=p(delta). No stored result or floating-point operation is used.
"""
if not __debug__:
    raise RuntimeError('Run without -O: exact checks require assertions')

from fractions import Fraction as Q
from math import comb, isqrt
import argparse
import json


def a(r):
    return r * (r + 1) // 2


def D(d):
    return d // 2 + 1


def threshold(r, eps=None):
    n = a(r)
    if eps is None:
        eps = n % 2
    return (Q(n * (n + 22 - r), 2 * (r - 1) * (n + 9))
            + Q(2 * r - 3, r - 1)
            - Q(n * (n + 21) + 36, (n + 4 - eps) * (n + 9)))


# Ascending coefficients, so poly_value(coeffs,r) is exact integer arithmetic.
P = (175104, -57088, -27568, -78276, -22712, -10513,
     -1543, -426, -18, -1, 1)
P_shift_10 = (37151424, 3111610752, 2388816952, 823740244,
              167027138, 21934307, 1934237, 114534, 4392, 99, 1)


def poly_value(coeffs, x):
    value = 0
    for c in reversed(coeffs):
        value = value * x + c
    return value


def poly_multiply(left, right):
    result = [Q(0)] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            result[i + j] += x * y
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def poly_add(left, right):
    result = [Q(0)] * max(len(left), len(right))
    for i, x in enumerate(left):
        result[i] += x
    for i, x in enumerate(right):
        result[i] += x
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def poly_scale(coeffs, scalar):
    return [scalar * x for x in coeffs]


def poly_shift(coeffs, offset):
    return [sum(coeffs[j] * comb(j, i) * offset ** (j - i)
                for j in range(i, len(coeffs)))
            for i in range(len(coeffs))]


def rational_poly_add(left, right):
    n1, d1 = left
    n2, d2 = right
    return (poly_add(poly_multiply(n1, d2), poly_multiply(n2, d1)),
            poly_multiply(d1, d2))


def rational_poly_threshold(eps):
    # R(r) as a rational function, assembled from the definition E1.
    n = [Q(0), Q(1, 2), Q(1, 2)]  # a=r(r+1)/2
    n9 = poly_add(n, [9])
    term1 = (poly_multiply(n, poly_add(n, [22, -1])),
             poly_scale(poly_multiply([-1, 1], n9), 2))
    term2 = ([-3, 2], [-1, 1])
    term3 = (poly_scale(poly_add(poly_multiply(n, poly_add(n, [21])), [36]), -1),
             poly_multiply(poly_add(n, [4 - eps]), n9))
    return rational_poly_add(rational_poly_add(term1, term2), term3)


def verify_rank_polynomial_identity():
    # Verify coefficient identity T1(r+1)-T0(r)-2/r=P(r)/Q(r).
    p1, q1 = rational_poly_threshold(1)
    shifted = (poly_shift(p1, 1), poly_shift(q1, 1))
    p0, q0 = rational_poly_threshold(0)
    lhs_num, lhs_den = rational_poly_add(
        rational_poly_add(shifted, (poly_scale(p0, -1), q0)), ([-2], [0, 1]))
    denom = [Q(4)]
    for factor in ([0, 1], [-1, 1], [8, 1, 1], [18, 1, 1],
                   [8, 3, 1], [20, 3, 1]):
        denom = poly_multiply(denom, factor)
    assert poly_multiply(lhs_num, denom) == poly_multiply(P, lhs_den)
    shifted_coeffs = poly_shift(P, 10)
    assert tuple(shifted_coeffs) == P_shift_10
    assert all(c > 0 for c in shifted_coeffs)


def slope(d, r, n, h):
    return d - 1 - (r - 1) * (h - 2 + Q(d + 2, n + 1))


def gap(e, d, r, n, h):
    m = e + d - 1
    v = Q(2 * e + d - 3, 2)
    alpha = Q(r - 1, n + 1)
    k = d + Q(d, n + 1) * (v - 1) + m * (h - 2 + Q(2, n + 1))
    return d * (v + 1) - m - (r - 1) * k + (Q(r + 1, 2) - alpha) * a(r)


def upper_direct(e, d, r, n):
    m = e + d - 1
    v = Q(2 * e + d - 3, 2)
    alpha = Q(r - 1, n + 1)
    c = Q(r + 1, 2) - alpha
    return (alpha * d * v + (r - 1 - alpha) * d + c * (m - a(r))
            + sum((Q(r - 1, t + 1) - alpha) * m for t in range(2, n)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--diagnostic', type=int, default=0)
    args = parser.parse_args()
    verify_rank_polynomial_identity()
    H23 = sum((Q(1, u) for u in range(1, 24)), Q(0))
    assert Q(747, 200) - H23 == Q(2107451, 2974571600) > 0
    seeds = []
    for r in range(4, 10):
        n = D(a(r))
        margin = threshold(r) - Q(747, 200) + Q(2 * (23 - n), n + 24)
        assert margin > 0
        seeds.append({'r': r, 'a_r': a(r), 'D_r': n,
                      'threshold': str(threshold(r)), 'rational_margin': str(margin)})
    step_margin = threshold(10) - threshold(9) - Q(1, 5)
    assert step_margin == Q(293, 18560) > 0
    result = {'H23': str(H23), '747/200-H23': str(Q(747, 200) - H23),
              'seed_comparisons': seeds, 'r9_step_margin': str(step_margin),
              'rank_polynomial_shift_10_ascending': P_shift_10,
              'number_of_harmonic_anchors': 1,
              'number_of_elementary_rational_comparisons': 7,
              'scope': 'Arithmetic supplement only. Universal bounds are proved in the manuscript.'}
    if args.diagnostic:
        N = args.diagnostic
        H = [Q(0)]
        for u in range(1, N + 3):
            H.append(H[-1] + Q(1, u))
        min_gap = min_slope = min_delta = None
        checks = 0
        for d in range(10, N + 1):
            r = (isqrt(8 * d + 1) - 1) // 2
            n = D(d)
            n0 = D(a(r))
            A = slope(d, r, n, H[n])
            G = gap(10, d, r, n, H[n])
            assert H[n0] < threshold(r)
            assert G > 0 and A > 0
            assert G == d * (Q(d + 17, 2) + 1) - upper_direct(10, d, r, n)
            fixed = gap(10, d + 1, r, n, H[n]) - G
            assert fixed == A + 11 - r - Q(8 * (r - 1), n + 1)
            assert fixed > Q(1, 4)
            next_n = D(d + 1)
            actual = gap(10, d + 1, r, next_n, H[next_n]) - G
            assert actual > Q(1, 4)
            nextA = slope(d + 1, r, next_n, H[next_n])
            Adiff = (1 - Q(r - 1, n + 1) if next_n == n else
                     1 - Q(2 * (r - 1), (n + 1) * (n + 2)))
            assert nextA - A == Adiff > 0
            if next_n != n:
                gain = gap(10, d + 1, r, next_n, H[next_n]) - gap(10, d + 1, r, n, H[n])
                assert gain == Q((r - 1) * (6 * n + a(r)), (n + 1) * (n + 2))
            aa = a(r)
            C = Q(aa * (-aa * (n0 - r + 2) - n0 * (r - 4) + 3), 2 * (n0 + 1))
            A0 = slope(aa, r, n0, H[n0])
            assert C < 0
            assert gap(10, aa, r, n0, H[n0]) == (aa + 9) * A0 + C
            F = -C / (aa + 9) + 11 - r - Q(8 * (r - 1), n0 + 1)
            F1 = (Q(aa, 2) - Q(3 * r, 2) + Q(11, 2)
                  + Q(3 * (5 * r + 31), 2 * (aa + 9)) - Q(17 * (r - 1), aa + 3))
            assert F >= F1 > Q(1, 4)
            for value, name in ((G, 'gap'), (A, 'slope'), (actual, 'delta')):
                row = (value, d, r)
                if name == 'gap' and (min_gap is None or value < min_gap[0]):
                    min_gap = row
                if name == 'slope' and (min_slope is None or value < min_slope[0]):
                    min_slope = row
                if name == 'delta' and (min_delta is None or value < min_delta[0]):
                    min_delta = row
            checks += 1
        result['optional_diagnostic'] = {'delta_range': [10, N], 'checks': checks,
              'rank_choice': 'r=p(delta), maximum rank permitted by a_r<=delta',
              'minimum_gap': {'value': str(min_gap[0]), 'delta': min_gap[1], 'r': min_gap[2]},
              'minimum_slope': {'value': str(min_slope[0]), 'delta': min_slope[1], 'r': min_slope[2]},
              'minimum_delta_step': {'value': str(min_delta[0]), 'delta': min_delta[1], 'r': min_delta[2]}}
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()

