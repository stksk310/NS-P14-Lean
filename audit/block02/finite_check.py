#!/usr/bin/env python3
"""Supplementary exhaustive checks; the universal result is proved in Lean."""
from pathlib import Path
import json

results = []
total = 0
for modulus in range(1, 15):
    count = 0
    max_cardinality = 0
    example = []
    for mask in range(1 << modulus):
        points = [i for i in range(modulus) if mask >> i & 1]
        size = len(points)
        sums = [(a + b) % modulus
                for i, a in enumerate(points) for b in points[i:]]
        sidon = len(sums) == len(set(sums))
        differences = [(a - b) % modulus
                       for a in points for b in points if a != b]
        injective = len(differences) == len(set(differences))
        assert sidon == injective, (modulus, points)
        if sidon:
            assert 0 not in differences
            assert size * (size - 1) <= modulus - 1
            count += 1
            if size > max_cardinality:
                max_cardinality = size
                example = points
        total += 1
    results.append({"modulus": modulus, "sidon_subsets": count,
                    "max_cardinality": max_cardinality, "example": example})
record = {"status": "PASS", "moduli": {"min": 1, "max": 14},
          "subsets_checked": total,
          "checks": ["Strong Sidon, including doubles, agrees with off-diagonal difference injectivity.",
                     "All Sidon subsets satisfy e(e-1)<=m-1."],
          "scope": "Supplementary finite checks only; the Lean theorems provide the universal proof.",
          "results": results}
Path(__file__).with_name("finite_check.json").write_text(
    json.dumps(record, indent=2) + "\n")
print(f"PASS: {total} subsets, moduli 1..14")
