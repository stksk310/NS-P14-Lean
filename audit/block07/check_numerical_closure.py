#!/usr/bin/env python3
"""Independent exact checks of weights, binomial targets, and common profiles."""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def factor(r, k):
    return choose(r - 1, k - 1)


def weight(r, k, t):
    if k == 1:
        return Q(r - 1) if t == 0 else Q(r + 1, 2) if t == 1 else Q(r - 1, t + 1)
    if t == 0:
        return Q(choose(r - 1, k))
    return Q(k * choose(r - 1, k), t + k) + Q((k - 1) * choose(r - 1, k - 1), t + k - 2)


def target(e, d, r, k):
    return (e - r + k) * choose(d + r - 1, k) + k * choose(d + r - 1, k + 1)


def lower(e, r, k):
    return (e - 1) * choose(r - 1, k) - choose(r - 1, k + 1)


def volume(e, d):
    return Q(e) + Q(d, 2) - Q(3, 2)


balance_cases = weight_cases = target_cases = 0
for n in range(33):
    for k in range(1, n + 5):
        assert k * choose(n, k) == (n + 1 - k) * choose(n, k - 1)
        balance_cases += 1
for r in range(4, 33):
    for k in range(1, r + 1):
        assert factor(r, k) > 0
        for t in [0, 1, *range(2, 34), 1000]:
            assert weight(r, k, t) <= factor(r, k) * weight(r, 1, t)
            if k >= 2 and t == 1:
                assert weight(r, k, t) == factor(r, k) * Q(r + 1, k + 1)
            weight_cases += 1
assert weight(4, 2, 2) == factor(4, 2) * weight(4, 1, 2)
assert weight(3, 2, 2) > factor(3, 2) * weight(3, 1, 2)
negative_coefficient_cases = 0
for r in range(1, 25):
    for e in range(r + 5):
        for d in range(11):
            cap = e * d + d * (d - 1) // 2
            assert cap == d * (volume(e, d) + 1)
            assert e * (d + 1) + (d + 1) * d // 2 == cap + e + d
            for k in range(1, r + 4):
                assert target(e, 0, r, k) == lower(e, r, k)
                assert target(e, d + 1, r, k) - target(e, d, r, k) == (e + d) * choose(d + r - 1, k - 1)
                assert target(e, d, r, k) - lower(e, r, k) >= cap * factor(r, k)
                if k == 1:
                    assert target(e, d, r, k) - lower(e, r, k) == cap
                if e - r + k < 0:
                    negative_coefficient_cases += 1
                target_cases += 1

H = [Q(0)]


def harmonic(n):
    while len(H) <= n:
        H.append(H[-1] + Q(1, len(H)))
    return H[n]


def tail_prefix(r, k, q):
    if k == 1:
        return (r - 1) * (harmonic(q + 2) - Q(3, 2))
    return (k * choose(r - 1, k) * (harmonic(q + k + 1) - harmonic(k + 1))
            + (k - 1) * choose(r - 1, k - 1) * (harmonic(q + k - 1) - harmonic(k - 1)))


def optimize_profile(r, e, d):
    a = r * (r + 1) // 2
    budget = d * (volume(e, d) - 1)
    tail_cap = Q(e + d - 1)
    head_cap = Q(r * d) if r == 2 else Q(min(r * d, e + d - 1 - a))
    assert budget >= 0 and tail_cap > 0 and head_cap >= 0
    head = min(head_cap, budget)
    remaining = budget - head
    q = int(remaining // tail_cap)
    last = remaining - q * tail_cap
    assert 0 <= last < tail_cap and head + q * tail_cap + last == budget
    assert head <= r * d
    if r >= 3:
        assert a <= d and head <= e + d - 1 - a
    values = {}
    for k in range(1, r + 1):
        assert weight(r, k, 1) >= weight(r, k, 2) >= weight(r, k, q + 2)
        values[k] = (weight(r, k, 0) * d + weight(r, k, 1) * head
                     + tail_cap * tail_prefix(r, k, q) + last * weight(r, k, q + 2))
    return values


params = []
for r in range(2, 21):
    a = r * (r + 1) // 2
    for e in [r + 1, r + 2, r + 5, r + 15]:
        if 6 <= r <= 8 and e == r + 1:
            continue  # Boundary is not inferred merely from numerical parameters.
        for d in ([0, 1, 2, 3, 10, 30] if r == 2 else [a, a + 1, a + 3, 2 * a]):
            params.append((r, e, d))
boundary_witnesses = []
for r, m in [(6, 1000), (7, 2000), (8, 5000)]:
    e, d = r + 1, m - (r + 1)
    points = [0] + [3**i for i in range(e - 1)]
    sums = [(x + y) % m for i, x in enumerate(points) for y in points[i:]]
    assert len(set(points)) == e and len(set(sums)) == len(sums)
    assert max(points) * 2 < m
    boundary_witnesses.append({"rank": r, "modulus": m, "e": e, "d": d, "points": points})
    params.append((r, e, d))
closure_rows = 0
for r, e, d in params:
    rows = optimize_profile(r, e, d)
    capacity = d * (volume(e, d) + 1)
    if r >= 4:
        assert rows[1] < capacity
    for k, value in rows.items():
        assert value <= capacity * factor(r, k)
        assert lower(e, r, k) + value <= target(e, d, r, k)
        closure_rows += 1

# A valid Data relaxation without its essential Boundary premise can fail.
corner_countermodels = []
for r in [6, 7, 8]:
    e, d = r + 1, r * (r + 1) // 2
    rows = optimize_profile(r, e, d)
    excess = lower(e, r, 1) + rows[1] - target(e, d, r, 1)
    assert excess > 0 and e * (e - 1) > e + d - 1
    corner_countermodels.append({"rank": r, "e": e, "d": d, "first_row_excess": str(excess),
                                 "all_resource_fields_hold": True, "Boundary_impossible": True})
assert corner_countermodels[0]["first_row_excess"] == "831/8008"
assert target(3, 3, 2, 1) == lower(3, 2, 1) + Q(12)
assert factor(3, 2) * (weight(3, 1, 0) * 6 + weight(3, 1, 2) * 205) == Q(892, 3)
assert weight(3, 2, 0) * 6 + weight(3, 2, 2) * 205 == Q(627, 2)
record = {"status": "PASS", "binomial_balance_cases": balance_cases, "coefficient_weight_cases": weight_cases,
          "target_formula_and_margin_cases": target_cases,
          "formal_cases_with_negative_signed_target_coefficient": negative_coefficient_cases,
          "common_profile_parameters": len(params), "integrated_row_comparisons": closure_rows,
          "nonvacuous_boundary_witnesses": boundary_witnesses,
          "countermodels_when_Boundary_is_omitted": corner_countermodels,
          "rank_three_scalarization_counterexample": {"e": 200, "d": 6, "head": 0, "tail0": 205,
                                                       "factor_times_first_row": "892/3", "second_row": "627/2"},
          "scope": "Supplementary exact finite checks, not a substitute for universal Lean proofs or actual semigroup/Tor semantics."}
Path(__file__).with_name("numerical_rational_checks.json").write_text(json.dumps(record, indent=2) + "\n")
print(f"PASS: {weight_cases} weights; {target_cases} target cases; {closure_rows} rows from {len(params)} profiles; 3 omitted-Boundary countermodels")
