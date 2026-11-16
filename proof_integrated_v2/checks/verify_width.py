#!/usr/bin/env python3
"""Exact coefficient checks for manuscript section 13.

Sparse polynomials over Fraction; Python standard library only. Every
identity is checked coefficient by coefficient, not on sampled parameters.
Universal inequalities and source reductions are proved in the manuscript.
"""
from fractions import Fraction as Q
from math import comb
import json


class Poly:
    def __init__(self, value=0):
        data = value if isinstance(value, dict) else {(0, 0, 0): Q(value)}
        self.data = {powers: Q(c) for powers, c in data.items() if c}

    def __add__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        data = self.data.copy()
        for p, c in other.data.items():
            data[p] = data.get(p, Q(0)) + c
        return Poly(data)

    __radd__ = __add__

    def __neg__(self):
        return Poly({p: -c for p, c in self.data.items()})

    def __sub__(self, other):
        return self + (-other if isinstance(other, Poly) else -Poly(other))

    def __rsub__(self, other):
        return Poly(other) - self

    def __mul__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        data = {}
        for p, a in self.data.items():
            for t, b in other.data.items():
                powers = tuple(x+y for x, y in zip(p, t))
                data[powers] = data.get(powers, Q(0)) + a*b
        return Poly(data)

    __rmul__ = __mul__

    def __truediv__(self, denominator):
        return Poly({p: c/Q(denominator) for p, c in self.data.items()})

    def __pow__(self, exponent):
        result = Poly(1)
        for _ in range(exponent):
            result = result*self
        return result


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def equal(left, right, message):
    difference = left-right
    need(not difference.data, (message, difference.data))


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def main():
    x = Poly({(1, 0, 0): 1})
    y = Poly({(0, 1, 0): 1})
    z = Poly({(0, 0, 1): 1})
    q, length, h2 = x, y, z
    incidence = (q+(q-1)*q/2+(q-1)*h2/3
                 +(q-1)*(length-1-q-h2)/4)
    retained = (q-1)*length/4+(q+1)**2/4+(q-1)*h2/12
    equal(incidence, retained, "incidence retaining degree 2")
    substituted = (q-1)*length/4+(q+1)**2/4+(q-1)*q*(q+1)/24
    bounded = (q-1)*length/4+(q+1)*(q+2)*(q+3)/24
    equal(substituted, bounded, "general incidence constant")

    u, shift = x, y
    target = u*(u-1)/2+1
    expected = {
        6: shift**2/24+43*shift/24+Q(1, 2),
        7: 2*shift+1,
        8: 3*shift**2/32+63*shift/16+Q(211, 32),
        9: shift**2/16+17*shift/4+Q(29, 4),
    }
    tables = []
    for e, expected_gap in expected.items():
        s = e//2
        v = 2*e-2+shift
        delta = v-(e-1)
        cap = v+delta**2/(2*s)+delta/2+Q((s*s)//4, 2*s)
        gap = v*(v-1)/2+1-((e+5)*cap/4-v+Q((e-1)*e*(e+1), 24))
        equal(gap, expected_gap, ("sparse first-row identity", e))
        need(all(c >= 0 for c in gap.data.values()), ("positive coefficients", e))
        need(gap.data.get((0, 0, 0), 0) > 0, ("positive constant", e))
        tables.append({"e": e, "gap_coefficients_ascending_in_shift":
                       [str(gap.data.get((0, i, 0), Q(0))) for i in range(3)]})

    # Clear 6(e-1), then compare sparse polynomial coefficients.
    e, shift = x, y
    v = 2*e-2+shift
    cleared_gap = 6*(e-1)*(v*(v-1)/2+1+v-e*(e-1)/6)-2*(e+3)*v**2
    positive = (3*(e-1)**2*(e-10)+6*(e-1)
                +(4*e-33)*(e-1)*shift+(e-9)*shift**2)
    equal(cleared_gap, positive, "generic e>=10 sparse first row")

    # Retained higher-row identities.
    e, v, shift = 8+x, 2*(8+x)-2+y, y
    bracket = 2*v**2-(3*e+6)*v+6*e-2
    equal(bracket, 2*x**2+5*x*shift+16*x+2*shift**2+26*shift+18,
          "e>=8 second-row bracket")
    u = x
    equal(u*(2*u**2-24*u+34)/6+10,
          (u-10)*(u-3)*(u+1)/3, "e6 second-row factorization")
    equal(2*(12+y)**2-27*(12+y)+40,
          2*y**2+21*y+4, "e7 second-row bracket")

    small = []
    for width, length_cap, socle_cap in ((6, 8, 0), (7, 10, 3)):
        bounds = (5*length_cap+4*socle_cap, 4*length_cap+6*socle_cap-1,
                  length_cap+4*socle_cap, socle_cap)
        capacities = tuple(i*choose(width, i+1)
                           + min(choose(width, i-1), choose(width, i))
                           for i in range(2, 6))
        need(all(a <= b for a, b in zip(bounds, capacities)),
             ("five-generator capacity", width))
        small.append({"width": width, "bounds_rows_2_to_5": bounds,
                      "minimum_target_rows_2_to_5": capacities})
    need(Q(2, 3)*8+Q(10, 3) < 9, "u6 integral first-row bound")
    need(6+Q(2, 3)*6-Q(1, 6) < 10, "u7 conditional integral bound")
    need((5*13)//2-8+5 == choose(8, 2)+1, "u8 non-antipodal boundary")
    print(json.dumps({"status": "PASS_EXACT_COEFFICIENT_IDENTITIES",
                      "method": "Sparse polynomials over Fraction; no parameter sampling",
                      "sparse_first_rows": tables, "small_width_capacities": small,
                      "generic_first_and_retained_higher_identities": "PASS",
                      "logical_role": "Arithmetic supplement to manuscript section 13"},
                     indent=2))


if __name__ == "__main__":
    main()
