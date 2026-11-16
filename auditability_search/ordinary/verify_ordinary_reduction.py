#!/usr/bin/env python3
"""Five exact scalar anchors replacing the 83-profile ordinary branch.

No manuscript or existing certificate is changed. Universal algebra and the
source-feasibility lemma are proved in ../ORDINARY_REDUCTION.md. The polynomial
calculation below checks every coefficient, rather than sampling e or delta.
"""

from fractions import Fraction as Q
from math import comb, lcm
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def add(*polynomials):
    answer = {}
    for polynomial in polynomials:
        for power, coefficient in polynomial.items():
            answer[power] = answer.get(power, Q(0)) + coefficient
    return {power: coefficient for power, coefficient in answer.items() if coefficient}


def scale(polynomial, scalar):
    return {power: scalar * coefficient for power, coefficient in polynomial.items()
            if scalar * coefficient}


def mul(left, right):
    answer = {}
    for (i, j), coefficient in left.items():
        for (k, ell), other in right.items():
            power = (i + k, j + ell)
            answer[power] = answer.get(power, Q(0)) + coefficient * other
    return {power: coefficient for power, coefficient in answer.items() if coefficient}


def constant(value):
    return {(0, 0): Q(value)} if value else {}


def harmonic(n):
    return sum((Q(1, j) for j in range(1, n + 1)), Q(0))


def gap_polynomial(r, cutoff):
    """G(r+1+s, a+t; cutoff), in independent formal variables s,t."""
    a = comb(r + 1, 2)
    e = {(0, 0): Q(r + 1), (1, 0): Q(1)}
    delta = {(0, 0): Q(a), (0, 1): Q(1)}
    m_minus_one = add(e, delta, constant(-1))
    resource = add(e, scale(delta, Q(1, 2)), constant(Q(-3, 2)))
    alpha = Q(r - 1, cutoff + 1)
    c = Q(r + 1, 2) - alpha
    tail_weight = sum((Q(r - 1, t + 1) - alpha
                       for t in range(2, cutoff)), Q(0))
    upper = add(scale(mul(delta, resource), alpha),
                scale(delta, r - 1 - alpha),
                scale(add(m_minus_one, constant(-a)), c),
                scale(m_minus_one, tail_weight))
    return add(mul(delta, add(resource, constant(1))), scale(upper, -1))


def main():
    # Common denominator, numerator of g, numerator of A, numerator of b.
    expected = {
        4: (7, 280, 2443, 762, 1007),
        5: (10, 6930, 39380, 28429, 32209),
        6: (13, 72072, -7479, 424147, 439591),
        7: (17, 2042040, -12196485, 17076937, 17076937),
        8: (21, 739024, -5070732, 8418651, 8250691),
    }
    rows = []
    for r, (cutoff, denominator, ng, na, nb) in expected.items():
        a = comb(r + 1, 2)
        polynomial = gap_polynomial(r, cutoff)
        alpha = Q(r - 1, cutoff + 1)
        beta = 1 - alpha
        g = polynomial.get((0, 0), Q(0))
        A = polynomial.get((1, 0), Q(0))
        b = polynomial.get((0, 1), Q(0)) + beta / 2
        identity = {
            (0, 0): g,
            (1, 0): A,
            (0, 1): b - beta / 2,
            (0, 2): beta / 2,
            (1, 1): beta,
        }
        require(polynomial == identity, (r, 'shifted polynomial identity'))
        require((g, A, b) == (Q(ng, denominator), Q(na, denominator), Q(nb, denominator)),
                (r, 'anchor table mismatch'))
        require(b == A + 2 - alpha * (r - 1), (r, 'forward-difference formula'))
        require(lcm(g.denominator, A.denominator, b.denominator) == denominator,
                (r, 'common denominator mismatch'))
        require(cutoff >= r and 0 < alpha < 1 and A > 0 and b > 0,
                (r, 'unpaid monotonicity'))
        if r <= 5:
            require(g > 0, (r, 'unpaid anchor'))
        else:
            require(g < 0 and g + A > 0 and g + b > 0,
                    (r, 'unpaid two adjacent anchors'))
            # At e=r+1 a full quadratic Apéry quotient requires delta >= r^2.
            # Its source proof is the ordered-difference injection in the note.
            require(r * r > a, (r, 'Sidon feasibility does not exclude the bad corner'))
        rows.append({
            'r': r, 'base_e': r + 1, 'a': a, 'cutoff': cutoff,
            'harmonic': str(harmonic(cutoff)), 'alpha': str(alpha),
            'common_denominator': denominator,
            'numerator_g': ng, 'numerator_A': na, 'numerator_b': nb,
            'gap_at_e_plus_one': str(g + A),
            'gap_at_delta_plus_one': str(g + b),
            'identity': 'G = g + s*A + t*b + (1-alpha)*(t*(t-1)/2+s*t)',
            'full_quadratic_delta_lower_bound_at_base_e': r * r,
        })
    print(json.dumps({
        'status': 'FIVE_EXACT_SCALAR_ANCHORS_PAID',
        'rows': rows,
        'scope': 'Universal proof in ../ORDINARY_REDUCTION.md; no finite source enumeration.',
        'coverage': 'All actual ordinary sources with e=5,...,9 and r>=4.',
        'original_manuscript_changed': False,
    }, indent=2))


if __name__ == '__main__':
    main()
