#!/usr/bin/env python3
"""Independent exact polynomial and finite rational-resource checks."""
from fractions import Fraction as Q
from pathlib import Path
import json

VARIABLES = ['a', 'r', 'n', 'alpha', 'w', 's', 't']
ZERO = (0,) * len(VARIABLES)


class P:
    def __init__(self, value=0):
        if isinstance(value, P):
            self.c = value.c.copy()
        elif isinstance(value, dict):
            self.c = {m: Q(c) for m, c in value.items() if c}
        else:
            self.c = {ZERO: Q(value)} if value else {}

    @staticmethod
    def variable(name):
        m = list(ZERO)
        m[VARIABLES.index(name)] = 1
        return P({tuple(m): 1})

    def __add__(self, other):
        out = self.c.copy()
        for m, c in P(other).c.items():
            out[m] = out.get(m, 0) + c
        return P(out)

    __radd__ = __add__

    def __neg__(self):
        return P({m: -c for m, c in self.c.items()})

    def __sub__(self, other):
        return self + -P(other)

    def __rsub__(self, other):
        return P(other) + -self

    def __mul__(self, other):
        out = {}
        for m, c in self.c.items():
            for n, d in P(other).c.items():
                monomial = tuple(a + b for a, b in zip(m, n))
                out[monomial] = out.get(monomial, 0) + c * d
        return P(out)

    __rmul__ = __mul__

    def __truediv__(self, scalar):
        return self * (1 / Q(scalar))

    def __pow__(self, n):
        out = P(1)
        for _ in range(n):
            out = out * self
        return out

    def __eq__(self, other):
        return self.c == P(other).c


a, r, n, alpha, w, s, t = [P.variable(name) for name in VARIABLES]


def poly_gap(e, d):
    e, d = P(e), P(d)
    v = e + d / 2 - Q(3, 2)
    upper = alpha * d * v + (r - 1 - alpha) * d + ((r + 1) / 2 - alpha) * (e + d - 1 - a) + (e + d - 1) * w
    return d * (v + 1) - upper


g = poly_gap(10, a)
A = poly_gap(11, a) - g
b = poly_gap(10, a + 1) - g
C = a * (-a + 4 - r + alpha * (a + 1)) / 2
assert g == (a + 9) * A + C
assert b == A + 11 - r - 8 * alpha
assert poly_gap(10 + s, a + t) == g + s * A + t * (b - (1 - alpha) / 2) + (1 - alpha) * (t**2 / 2 + s * t)
Cnum = a * (-a * (n - r + 2) - n * (r - 4) + 3)
assert Cnum == a * ((-a + 4 - r) * (n + 1) + (r - 1) * (a + 1))
Lnum = -Cnum + 2 * (n + 1) * (a + 9) * (11 - r) - 16 * (r - 1) * (a + 9)
floor_comparison_numerator = (Lnum * (a + 3)
    - (a - 3 * r + 11) * (a + 9) * (n + 1) * (a + 3)
    - 3 * (5 * r + 31) * (n + 1) * (a + 3)
    + 34 * (r - 1) * (a + 9) * (n + 1))
assert floor_comparison_numerator == (2 * n - a - 1) * (r - 1) * (a**2 + 17 * a + 144)

H = [Q(0)]


def harmonic(n):
    while len(H) <= n:
        H.append(H[-1] + Q(1, len(H)))
    return H[n]


def gap(rank, cutoff, e, d):
    aa = Q(rank * (rank + 1), 2)
    al = Q(rank - 1, cutoff + 1)
    wt = (rank - 1) * (harmonic(cutoff) - Q(3, 2)) - (cutoff - 2) * al
    v = e + d / 2 - Q(3, 2)
    upper = al * d * v + (rank - 1 - al) * d + (Q(rank + 1, 2) - al) * (e + d - 1 - aa) + (e + d - 1) * wt
    return d * (v + 1) - upper


def correction(rank, cutoff):
    aa = Q(rank * (rank + 1), 2)
    return aa * (-aa * (cutoff - rank + 2) - cutoff * (rank - 4) + 3) / (2 * (cutoff + 1))


def floor_step(rank):
    aa = Q(rank * (rank + 1), 2)
    return aa / 2 - Q(3 * rank, 2) + Q(11, 2) + Q(3 * (5 * rank + 31), 2 * (aa + 9)) - Q(17 * (rank - 1), aa + 3)


shifts = [Q(0), Q(1, 100), Q(1, 2), Q(1), Q(7, 3), Q(100)]
shift_cases = resource_cases = free_cutoff_cases = negative_residual_profiles = 0
for rank in range(9, 129):
    aa = Q(rank * (rank + 1), 2)
    cutoff = int(aa) // 2 + 1
    al = Q(rank - 1, cutoff + 1)
    beta = 1 - al
    seed = gap(rank, cutoff, Q(10), aa)
    slope = gap(rank, cutoff, Q(11), aa) - seed
    step = gap(rank, cutoff, Q(10), aa + 1) - seed
    corr = correction(rank, cutoff)
    low = -corr / (aa + 9) + 11 - rank - 8 * al
    floor = floor_step(rank)
    assert 0 < al < 1 and 0 < beta < 1 and corr < 0
    assert seed == (aa + 9) * slope + corr and seed > 0
    assert slope > -corr / (aa + 9) > 0
    assert step == slope + 11 - rank - 8 * al
    assert step > low >= floor > Q(5, 4)
    assert step - beta / 2 > Q(3, 4)
    assert (low == floor) == (int(aa) % 2 == 1)
    for nn in sorted({0, 1, rank, cutoff, cutoff + 1}):
        ll = -correction(rank, nn) / (aa + 9) + 11 - rank - Q(8 * (rank - 1), nn + 1)
        rhs = (2 * nn - aa - 1) * (rank - 1) * (aa**2 + 17 * aa + 144) / (2 * (aa + 9) * (nn + 1) * (aa + 3))
        assert ll - floor == rhs
        free_cutoff_cases += 1
    for ss in shifts:
        for tt in shifts:
            e, d = Q(10) + ss, aa + tt
            value = gap(rank, cutoff, e, d)
            assert value == seed + ss * slope + tt * (step - beta / 2) + beta * (tt**2 / 2 + ss * tt)
            assert value > 0
            shift_cases += 1
            # Exact greedy maximum over arbitrary finite nonnegative resource tails.
            # Head has the largest weight; tail weights decrease with layer index.
            v = e + d / 2 - Q(3, 2)
            budget = d * (v - 1)
            cap = e + d - 1
            head_cap = cap - aa
            assert budget >= 0 and cap > 0 and head_cap >= 0
            head = min(head_cap, budget)
            tail_budget = budget - head
            full = int(tail_budget // cap)
            remainder = tail_budget - full * cap
            assert 0 <= remainder < cap and head + full * cap + remainder == budget
            scalar = ((rank - 1) * d + Q(rank + 1, 2) * head
                      + cap * (rank - 1) * (harmonic(full + 2) - Q(3, 2))
                      + Q(rank - 1, full + 3) * remainder)
            upper = d * (v + 1) - value
            assert scalar <= upper < d * (v + 1)
            last = full if remainder else full - 1
            if last > cutoff - 2:
                negative_residual_profiles += 1
            resource_cases += 1
record = {"status": "PASS", "symbolic_polynomial_identities": 5,
          "ranks_checked": {"min": 9, "max": 128, "count": 120},
          "shift_values": [str(x) for x in shifts], "positive_gap_cases": shift_cases,
          "finite_resource_optimization_cases": resource_cases,
          "resource_profiles_with_negative_residual_tail": negative_residual_profiles,
          "free_cutoff_comparison_cases": free_cutoff_cases,
          "scope": "Polynomial identities are checked by exact multivariate coefficients. Rank and resource checks are supplementary finite tests; the universal result is proved in Lean."}
Path(__file__).with_name("large_scalar_rational_checks.json").write_text(json.dumps(record, indent=2) + "\n")
print(f"PASS: 5 polynomial identities; {shift_cases} positive rational gaps; {resource_cases} resource optimizations; {free_cutoff_cases} cutoff identities")
