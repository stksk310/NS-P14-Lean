#!/usr/bin/env python3
"""Exact arithmetic for the consolidated P14 proof; not Lean verification.

No archive module, stored PASS flag, or floating-point calculation is used.
The universal reductions and analytic induction are proved in the manuscript.
"""
from fractions import Fraction as Q
from math import comb, isqrt
from pathlib import Path
import argparse
import hashlib
import json


def need(condition, message):
    if not condition:
        raise ValueError(message)


def binom(n, j):
    return comb(n, j) if 0 <= j <= n else 0


def envelope(e, d, r, harmonic):
    """Compute the upper bound directly, before simplifying the gap."""
    mcap = e + d - 1
    volume = Q(2 * e + d - 3, 2)
    alpha = Q(r - 1, d + 1)
    correction = Q(r + 1, 2) - alpha
    # H_1 <= mcap - binom(r+1,2); later slots have cap mcap.
    upper = alpha * d * volume + (r - 1 - alpha) * d
    upper += correction * (mcap - binom(r + 1, 2))
    upper += sum((Q(r - 1, t + 1) - alpha) * mcap
                 for t in range(2, d))
    slope = d + r - 2 - (r - 1) * harmonic[d] - alpha
    gap = (slope * mcap - Q(d * (d + r - 2), 2) + d * alpha
           + correction * binom(r + 1, 2))
    need(d * (volume + 1) - upper == gap, (e, d, r, "gap identity"))
    return upper, gap, slope


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path,
                        default=Path(__file__).resolve().parents[1]
                        / "certificates/scalar_e13.json")
    args = parser.parse_args()
    harmonic = [Q(0)]
    for n in range(1, 211):
        harmonic.append(harmonic[-1] + Q(1, n))
    rows = []
    rank_envelope_checks = 0
    for d in range(10, 210):
        r = (isqrt(8 * d + 1) - 1) // 2
        upper, gap, slope = envelope(13, d, r, harmonic)
        need(gap > 0 and slope > 0, (d, r, "unpaid ray"))
        rows.append({"delta": d, "r": r, "initial_e": 13,
                     "gap": str(gap), "slope": str(slope)})
        # These diagnose the separately proved monotonicity in r.
        for actual_r in range(4, r + 1):
            value, _, _ = envelope(13, d, actual_r, harmonic)
            need(value <= upper, (d, actual_r, "rank monotonicity"))
            rank_envelope_checks += 1
    need(harmonic[210] < 6, "analytic induction base")
    canonical = json.dumps(rows, sort_keys=True, separators=(",", ":")) + "\n"
    minimum_gap = min(rows, key=lambda x: Q(x["gap"]))
    minimum_slope = min(rows, key=lambda x: Q(x["slope"]))

    # A finite diagnostic for the universal binomial identity (P) in the text.
    target_identity_checks = 0
    for e in (2, 13, 274):
        for d in range(31):
            for r in range(2, 21):
                volume = Q(2 * e + d - 3, 2)
                for j in range(1, r + 1):
                    baseline = ((e - 1) * binom(r - 1, j)
                                - binom(r - 1, j + 1))
                    target = ((e - r + j) * binom(d + r - 1, j)
                              + j * binom(d + r - 1, j + 1))
                    gamma = d * binom(r - 1, j - 1)
                    gamma += Q(1, 2) * sum(
                        (3 * binom(r - 1, j - u)
                         + (u - 2) * binom(r, j - u + 1)) * binom(d, u)
                        for u in range(2, j + 1))
                    gamma += Q(j - 1, 2) * binom(d, j + 1)
                    need(target - baseline == volume * (
                        binom(d + r - 1, j) - binom(r - 1, j)) + gamma,
                        (e, d, r, j, "target expansion"))
                    need(target - baseline >= d * (volume + 1)
                         * binom(r - 1, j - 1),
                         (e, d, r, j, "target lower bound"))
                    target_identity_checks += 1
    result = {
        "status": "PASS_EXACT_ARITHMETIC_ONLY",
        "finite_rays": 200,
        "embedding_dimension_ray": "e >= 13",
        "delta_range": [10, 209],
        "minimum_gap_row": minimum_gap,
        "minimum_slope_row": minimum_slope,
        "canonical_rows_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "rank_envelope_diagnostics": rank_envelope_checks,
        "target_identity_diagnostics": target_identity_checks,
        "H210": str(harmonic[210]),
        "six_minus_H210": str(6 - harmonic[210]),
        "all_exact_rows": rows,
        "scope": "Arithmetic certificate only. Boundary lemmas, numerical-semigroup "
                 "structure, module inequalities, and infinite induction require "
                 "their mathematical proofs; this is not a formal P14 verification.",
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ("all_exact_rows", "H210", "six_minus_H210")},
                     ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
