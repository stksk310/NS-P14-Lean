#!/usr/bin/env python3
"""Independent exact checks of the paper weights and low-rank relaxations."""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json


def volume(e, d):
    return e + d / 2 - Q(3, 2)


def paper_weight(r, k, layer):
    if k == 1:
        return Q(r - 1) if layer == 0 else Q(r + 1, 2) if layer == 1 else Q(r - 1, layer + 1)
    c1 = comb(r - 1, k) if k <= r - 1 else 0
    c2 = comb(r - 1, k - 1)
    if layer == 0:
        return Q(c1)
    return Q(k * c1, layer + k) + Q((k - 1) * c2, layer + k - 2)


def row(r, k, d, head, tail):
    return (paper_weight(r, k, 0) * d + paper_weight(r, k, 1) * head
            + sum((paper_weight(r, k, j + 2) * h for j, h in tail.items()), Q(0)))


expected = {(2, 1): (Q(1), Q(3, 2), lambda j: Q(1, j + 3)),
            (2, 2): (Q(0), Q(1), lambda j: Q(1, j + 2)),
            (3, 1): (Q(2), Q(2), lambda j: Q(2, j + 3)),
            (3, 2): (Q(1), Q(8, 3), lambda j: Q(2, j + 4) + Q(2, j + 2)),
            (3, 3): (Q(0), Q(1), lambda j: Q(2, j + 3))}
weight_checks = 0
for (r, k), (w0, w1, wt) in expected.items():
    assert paper_weight(r, k, 0) == w0
    assert paper_weight(r, k, 1) == w1
    weight_checks += 2
    for j in range(31):
        assert paper_weight(r, k, j + 2) == wt(j)
        weight_checks += 1

supports = [[], [0], [1], [10], [1000], [0, 3, 50], [2, 5, 1000]]
checks = {"rank_two": 0, "rank_three": 0}
branches = {"V_below_3": 0, "V_equal_3": 0, "V_above_3": 0, "zero_deficit": 0}
params = {2: ([Q(x) for x in [-2, -1, 0, 1, 2, 3, 4, 5, 6, 8, 10]]
               + [Q(3, 2), Q(5, 2), Q(7, 2), Q(9, 2)],
              [Q(0), Q(1, 4), Q(1, 2), Q(1), Q(3, 2), Q(2), Q(3), Q(4), Q(6), Q(10)]),
          3: ([Q(4), Q(17, 4), Q(9, 2), Q(5), Q(6), Q(8), Q(10), Q(20)],
              [Q(6), Q(25, 4), Q(13, 2), Q(7), Q(8), Q(10), Q(20)])}
minimum_margin = None
for r, (es, ds) in params.items():
    for e in es:
        for d in ds:
            v = volume(e, d)
            budget = d * (v - 1)
            if budget < 0:
                continue  # No nonnegative head/tail profile satisfies the mass budget.
            head_cap = 2 * d if r == 2 else min(3 * d, e + d - 7)
            assert head_cap >= 0
            if r == 3:
                margin = d * (v - 1) - 4 * (e + d - 7)
                assert margin >= 15
                minimum_margin = margin if minimum_margin is None else min(minimum_margin, margin)
            for support in supports:
                for k in range(1, r + 1):
                    # For all five rows, head has at least every tail weight.
                    # With no tail caps, the exact optimum fills head, then the
                    # largest available tail weight, respecting the common budget.
                    wh = paper_weight(r, k, 1)
                    assert all(paper_weight(r, k, j + 2) <= wh for j in support)
                    head = min(budget, head_cap)
                    tail = {}
                    if support:
                        best = max(support, key=lambda j: paper_weight(r, k, j + 2))
                        tail[best] = budget - head
                    mass = d + head + sum(tail.values())
                    assert mass <= d * v and head <= head_cap
                    f = row(r, k, d, head, tail)
                    target = d * (v - 1) if k == r else (r - 1 if k == 2 else 1) * d * (v + 1)
                    assert f <= target, (r, k, e, d, support, f, target)
                    if r == 2:
                        assert row(2, 1, d, head, tail) <= Q(3, 2) * mass - d / 2
                        assert row(2, 1, d, head, tail) <= Q(5, 2) * d + mass / 2
                        branches["V_below_3" if v < 3 else "V_equal_3" if v == 3 else "V_above_3"] += 1
                        if d == 0:
                            branches["zero_deficit"] += 1
                    else:
                        assert row(3, 1, d, head, tail) <= Q(4, 3) * d + Q(4, 3) * head + Q(2, 3) * mass
                        assert row(3, 2, d, head, tail) <= 3 * d + Q(3, 2) * mass
                    assert row(r, r, d, head, tail) <= mass - d
                    checks["rank_two" if r == 2 else "rank_three"] += 1
assert all(branches.values()) and minimum_margin == 15
assert row(2, 1, Q(3), Q(6), {}) == 12 and row(2, 2, Q(3), Q(6), {}) == 6
assert row(2, 1, Q(1), Q(3), {}) == Q(11, 2) > Q(1) * (volume(Q(5), Q(1)) + 1)
assert row(3, 1, Q(6), Q(18), {}) == 48 > Q(6) * (volume(Q(4), Q(6)) + 1)
record = {"status": "PASS", "weight_checks": weight_checks, "optimization_checks": checks,
          "rank_two_branch_checks": branches, "minimum_sampled_rank_three_margin": str(minimum_margin),
          "scope": "Supplementary finite rational checks; universal inequalities are proved in Lean.",
          "sharp_rank_two_profile": {"e": 3, "d": 3, "head": 6, "tail": {}, "V": 3, "first_row": 12, "top_row": 6},
          "counterexamples_when_head_caps_are_omitted": [
              {"rank": 2, "e": 5, "d": 1, "head": 3, "mass": 4, "budget": 4, "first_row": "11/2", "target": 5, "omitted": "head<=2d"},
              {"rank": 3, "e": 4, "d": 6, "head": 18, "mass": 24, "budget": 33, "first_row": 48, "target": 39, "omitted": "head<=e+d-7", "linear_head_cap_still_holds": True}]}
Path(__file__).with_name("low_rank_rational_checks.json").write_text(json.dumps(record, indent=2) + "\n")
print(f"PASS: {weight_checks} weight evaluations; {sum(checks.values())} exact optimization cases; all volume branches and d=0 covered")
