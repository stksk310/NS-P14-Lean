#!/usr/bin/env python3
"""Exact finite optimization checks; universal SO3 is proved in Lean."""
from fractions import Fraction as Q
from pathlib import Path
import json


def parameters(rank, cutoff, e, d):
    triangular = Q(rank * (rank + 1), 2)
    volume = e + d / 2 - Q(3, 2)
    cap = e + d - 1
    head_cap = cap - triangular
    budget = d * volume - d
    alpha = Q(rank - 1, cutoff + 1)
    residual_sum = sum((Q(rank - 1, denominator) - alpha
                        for denominator in range(3, cutoff + 1)), Q(0))
    upper = (alpha * d * volume + (rank - 1 - alpha) * d
             + (Q(rank + 1, 2) - alpha) * head_cap + cap * residual_sum)
    return cap, head_cap, budget, upper


def scalar(rank, d, head, tail):
    return ((rank - 1) * d + Q(rank + 1, 2) * head
            + sum((Q(rank - 1, j + 3) * value for j, value in tail.items()), Q(0)))


def bounds(rank, cutoff, e, d, head, tail):
    cap, head_cap, budget, upper = parameters(rank, cutoff, e, d)
    return {"budget": head + sum(tail.values()) <= budget,
            "head_cap": head <= head_cap,
            "tail_cap": all(value <= cap for value in tail.values()),
            "head_nonneg": head >= 0,
            "tail_nonneg": all(value >= 0 for value in tail.values()),
            "value": scalar(rank, d, head, tail), "upper": upper}


checks = 0
for rank in range(4, 13):
    triangular = Q(rank * (rank + 1), 2)
    cutoffs = set(range(rank, rank + 8))
    selected = {4: 7, 5: 10, 6: 13, 7: 17, 8: 21}.get(rank)
    if selected:
        cutoffs.add(selected)
    shifts = [Q(0), Q(1, 2), Q(1), Q(2)]
    for s in shifts:
        for t in shifts:
            e, d = Q(rank + 1) + s, triangular + t
            for cutoff in sorted(cutoffs):
                cap, head_cap, budget, upper = parameters(rank, cutoff, e, d)
                supports = [set(), {0}, {cutoff - 2}, {cutoff + 10},
                            {0, cutoff - 3, cutoff - 2, cutoff - 1, cutoff + 10, 1000},
                            set(range(cutoff + 3))]
                for support in supports:
                    # Exact greedy optimizer for a single total budget and individual caps.
                    # All objective weights are positive; fill in descending weight order.
                    entries = [(Q(rank + 1, 2), head_cap, None)]
                    entries += [(Q(rank - 1, j + 3), cap, j) for j in sorted(support)]
                    entries.sort(key=lambda item: item[0], reverse=True)
                    remaining = budget
                    head = Q(0)
                    tail = {}
                    for weight, limit, j in entries:
                        amount = min(remaining, limit)
                        remaining -= amount
                        if j is None:
                            head = amount
                        else:
                            tail[j] = amount
                    result = bounds(rank, cutoff, e, d, head, tail)
                    assert all(result[key] for key in ("budget", "head_cap", "tail_cap",
                                                       "head_nonneg", "tail_nonneg"))
                    assert result["value"] <= upper, (rank, cutoff, s, t, support)
                    checks += 1

counterexamples = []
profiles = {
    "budget": (Q(4), {j: Q(14) for j in range(6)}),
    "head_cap": (Q(75), {}),
    "tail_cap": (Q(4), {0: Q(71)}),
    "tail_nonneg": (Q(4), {**{j: Q(14) for j in range(6)}, 1000: Q(-13)}),
}
for omitted, (head, tail) in profiles.items():
    result = bounds(4, 7, Q(5), Q(10), head, tail)
    assert not result[omitted]
    assert all(result[key] for key in ("budget", "head_cap", "tail_cap", "head_nonneg",
                                       "tail_nonneg") if key != omitted)
    assert result["value"] > result["upper"]
    counterexamples.append({"omitted_condition": omitted, "rank": 4, "cutoff": 7,
                            "e": 5, "d": 10, "head": str(head),
                            "tail": {str(j): str(v) for j, v in tail.items()},
                            "scalar": str(result["value"]), "upper": str(result["upper"]),
                            "all_other_listed_conditions_hold": True})

sharp = bounds(4, 7, Q(5), Q(10), Q(4), {**{j: Q(14) for j in range(5)}, 5: Q(1)})
assert sharp["value"] == sharp["upper"] == Q(3451, 40)
record = {"status": "PASS", "optimization_cases": checks, "ranks": [4, 12],
          "shift_values": ["0", "1/2", "1", "2"],
          "scope": "Supplementary exact finite optimization checks; the Lean theorem is the universal proof.",
          "sharp_profile_scalar_and_upper": "3451/40",
          "counterexamples_when_a_condition_is_omitted": counterexamples}
Path(__file__).with_name("resource_bound_checks.json").write_text(json.dumps(record, indent=2) + "\n")
print(f"PASS: {checks} exact optimization cases; 4 omitted-condition counterexamples; sharp equality")
