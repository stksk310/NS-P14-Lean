#!/usr/bin/env python3
"""Independent polynomial identities and exact finite arithmetic checks."""
from fractions import Fraction as Q
from pathlib import Path
import json


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p)


def add(*ps):
    out = [0] * max(map(len, ps))
    for p in ps:
        for i, c in enumerate(p):
            out[i] += c
    return trim(out)


def scale(p, c):
    return trim([v * c for v in p])


def mul(*ps):
    out = (1,)
    for p in ps:
        new = [0] * (len(out) + len(p) - 1)
        for i, a in enumerate(out):
            for j, b in enumerate(p):
                new[i + j] += a * b
        out = trim(new)
    return out


def power(p, n):
    return mul(*([p] * n))


x = (0, 1)
x1, xm1, xm10 = add(x, (1,)), add(x, (-1,)), add(x, (-10,))
p = mul(x, x1)
a2, c2 = add(p, (6,)), add(p, (18,))
# Numerator obtained by clearing the independently written barrier increment.
step_numerator = add(mul(x, x1, a2), scale(a2, -18),
                     scale(mul(x, x1, add(x, (2,))), -8))
shifted_quartic = add(power(xm10, 4), scale(power(xm10, 3), 34),
                       scale(power(xm10, 2), 385), scale(xm10, 1472), (112,))
assert step_numerator == shifted_quartic == (-108, -28, -35, -6, 1)
# Common denominator 4*r*(r-1)*(r^2+r+6)*(r^2+r+18) gives 2*N(r).
threshold_numerator = add(
    mul(p, add(p, (44,), scale(x, -2)), x, a2),
    scale(mul(add(scale(x, 2), (-3,)), x, a2, c2), 4),
    scale(mul(add(mul(p, add(p, (42,))), (144,)), x, xm1), -4),
    scale(mul(x, x, xm1, a2, c2), -1),
    scale(mul(x, xm1, a2, c2), -4),
    scale(mul(xm1, a2, c2), -18))
structured_n = add(mul(power(x, 3), add(mul(xm10, add(scale(x, 2), (15,))), (2,))),
                   mul(x, add(scale(xm10, 111), (210,))), (972,))
assert structured_n == (972, -900, 111, -148, -5, 2)
assert threshold_numerator == scale(structured_n, 2)


def triangular(r):
    return r * (r + 1) // 2


def cutoff(r):
    return triangular(r) // 2 + 1


def barrier(r):
    return Q(r, 4) + 1 + Q(9, 2 * r)


def threshold(r, n):
    a = triangular(r)
    return (Q(a * (a + 22 - r), 2 * (r - 1) * (a + 9))
            + Q(2 * r - 3, r - 1)
            - Q(a * (a + 21) + 36, 2 * (n + 1) * (a + 9)))


def lower(r):
    a = triangular(r)
    return (Q(a * (a + 22 - r), 2 * (r - 1) * (a + 9))
            + Q(2 * r - 3, r - 1)
            - Q(a * (a + 21) + 36, (a + 3) * (a + 9)))


def direct_gap(r, n):
    d = Q(triangular(r))
    v = 10 + d / 2 - Q(3, 2)
    alpha = Q(r - 1, n + 1)
    tail = sum((Q(r - 1, j) - alpha for j in range(3, n + 1)), Q(0))
    upper = alpha * d * v + (r - 1 - alpha) * d + (Q(r + 1, 2) - alpha) * 9 + (d + 9) * tail
    return d * (v + 1) - upper


for r in range(10001):
    a, d, dn = triangular(r), cutoff(r), cutoff(r + 1)
    assert 2 * a == r * (r + 1)
    assert 2 * d == a + 2 - a % 2
    assert a + 1 <= 2 * d <= a + 2
    assert d <= dn and 2 * (dn - d) <= r + 2
    if r >= 4:
        assert r <= d
h = [Q(0)]
for j in range(1, cutoff(129) + 1):
    h.append(h[-1] + Q(1, j))
assert h[23] == Q(444316699, 118982864)
assert barrier(10) - h[28] == Q(1833472237, 80313433200)
assert direct_gap(9, 23) == Q(5845533, 7436429)
seed_cases = 0
barrier_cases = 0
for r in range(9, 129):
    a, d, dn = triangular(r), cutoff(r), cutoff(r + 1)
    assert h[dn] - h[d] <= Q(r + 2, a + 3)
    assert h[d] < threshold(r, d)
    g = direct_gap(r, d)
    assert g == (r - 1) * (a + 9) * (threshold(r, d) - h[d]) and g > 0
    seed_cases += 1
    if r >= 10:
        assert h[d] < barrier(r) < lower(r) <= threshold(r, d)
        assert Q(r + 2, a + 3) < barrier(r + 1) - barrier(r)
        barrier_cases += 1
identity_cases = 0
for r in [9, 10, 11, 12, 17, 24]:
    for n in sorted({2, 3, r, cutoff(r), cutoff(r) + 1}):
        g = direct_gap(r, n)
        assert g == (r - 1) * (triangular(r) + 9) * (threshold(r, n) - h[n])
        identity_cases += 1
assert barrier(10) - barrier(9) - Q(11, 48) == Q(-7, 240)
assert lower(9) - barrier(9) == Q(-1, 72)
assert Q(12, 58) - Q(2, 10) == Q(1, 145)
record = {"status": "PASS", "symbolic_polynomial_identities": 2,
          "barrier_increment_numerator_coefficients_ascending": list(step_numerator),
          "threshold_gap_numerator_coefficients_ascending": list(structured_n),
          "floor_and_step_ranks_checked": {"min": 0, "max": 10000, "count": 10001},
          "positive_seed_ranks_checked": {"min": 9, "max": 128, "count": seed_cases},
          "barrier_chain_ranks_checked": {"min": 10, "max": 128, "count": barrier_cases},
          "free_cutoff_seed_identity_cases": identity_cases,
          "anchor_values": {"H23": str(h[23]), "B10_minus_H28": str(barrier(10) - h[28]),
                            "rank9_seed": str(direct_gap(9, 23)),
                            "rank9_coarse_step_defect": "-7/240", "rank9_lower_minus_barrier": "-1/72",
                            "rank10_coarse_increment_minus_2_over_r": "1/145"},
          "scope": "Polynomial identities are checked by coefficient arithmetic. Rank sweeps are supplementary finite checks; the universal rank proof is Lean induction."}
Path(__file__).with_name("large_seed_rational_checks.json").write_text(json.dumps(record, indent=2) + "\n")
print(f"PASS: 2 polynomial identities; 10001 floor cases; {seed_cases} positive seeds; {barrier_cases} barrier chains; {identity_cases} free-cutoff identities")
