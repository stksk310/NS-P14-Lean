#!/usr/bin/env python3
"""Independent finite regression audit of O10, using lex rank unranking.

The frozen checker is not imported or executed.  The certificate is read only
for an independent data comparison.  This file never writes frozen inputs.
Finite samples are regression evidence, not a proof for every m.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from math import comb
from pathlib import Path
import time


ROOT = Path(__file__).resolve().parents[2]


def choose(n: int, k: int) -> int:
    return comb(n, k) if 0 <= k <= n else 0


def monomial_count(variables: int, degree: int) -> int:
    if variables == 0:
        return int(degree == 0)
    return choose(variables + degree - 1, degree)


def require(condition: bool, detail: object) -> None:
    if not condition:
        raise ValueError(detail)


def boundary_monomial(variables: int, degree: int, rank: int) -> tuple[int, ...]:
    """Unrank one monomial, 1-based, in ascending exponent-tuple lex order.

    A prefix of complete blocks with first exponent < a contains
    C(v+d-1,d) - C(v+d-a-1,d-a) monomials.  Binary search skips
    those blocks without constructing the degree-d monomial list.
    """
    require(1 <= rank <= monomial_count(variables, degree),
            (variables, degree, rank, "invalid lex rank"))
    result = []
    for remaining_variables in range(variables, 1, -1):
        total = monomial_count(remaining_variables, degree)
        low, high = 0, degree
        while low < high:
            middle = (low + high + 1) // 2
            skipped = total - monomial_count(remaining_variables, degree - middle)
            if skipped < rank:
                low = middle
            else:
                high = middle - 1
        exponent = low
        rank -= total - monomial_count(remaining_variables, degree - exponent)
        result.append(exponent)
        degree -= exponent
    result.append(degree)
    require(rank == 1, (result, rank, "unranking did not terminate"))
    return tuple(result)


def support_counts(variables: int, degree: int, length: int) -> tuple[int, ...]:
    """All S_j for one prefix, from its last monomial and binomial sums.

    Every complete block before the endpoint contributes its number of
    monomials on the first j available variables.  Add the endpoint itself
    when it uses only the first j variables.  Cost depends on e, not on the
    number C(e+d-1,d) of all degree-d monomials.
    """
    require(degree > 0, "only positive degrees are used")
    if length == 0:
        return (0,) * (variables + 1)
    boundary = boundary_monomial(variables, degree, length)
    result = [0] * (variables + 1)
    remaining_degree = degree
    for position, exponent in enumerate(boundary, 1):
        if exponent:
            for j in range(position, variables + 1):
                allowed = j - position + 1
                result[j] += (monomial_count(allowed, remaining_degree)
                              - monomial_count(allowed, remaining_degree - exponent))
        remaining_degree -= exponent
    last_variable = max(j for j, exponent in enumerate(boundary, 1) if exponent)
    for j in range(last_variable, variables + 1):
        result[j] += 1
    require(result[-1] == length, (variables, degree, length, result))
    return tuple(result)


def o10_counts(e: int, m: int) -> tuple[int, ...]:
    """T_j at rho=m-1, evaluated directly from frozen manuscript O10."""
    require(e >= 2 and m >= e + 1, (e, m))
    totals = list(range(1, e + 1))
    totals[-1] -= m - 1
    for degree in range(2, m - 1):
        length = min(m - 1, monomial_count(e, degree))
        supports = support_counts(e, degree, length)
        for j in range(1, e + 1):
            totals[j - 1] += supports[j - 1]
    return tuple(totals)


def betti_from_counts(totals: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sum(total * choose(j - 1, i - 1)
                     for j, total in enumerate(totals, 1))
                 for i in range(1, len(totals) + 1))


def capped_hilbert(e: int, m: int) -> tuple[int, ...]:
    return ((1, e)
            + tuple(min(m - 1, monomial_count(e, degree))
                    for degree in range(2, m - 1))
            + (m, m))


def o7_counts(e: int, m: int) -> tuple[int, ...]:
    """Sum degreewise O7 independently of the telescoped O10 expression."""
    hilbert = capped_hilbert(e, m)
    previous = support_counts(e, 1, e)
    totals = [0] * e
    for degree in range(2, m + 1):
        current = support_counts(e, degree, hilbert[degree])
        for j in range(1, e + 1):
            count = previous[j] - current[j] + current[j - 1]
            require(count >= 0, (e, m, degree, j, count, "negative O7 slot"))
            totals[j - 1] += count
        previous = current
    # Once degree reaches m-1, the standard monomials are precisely
    # X_(e-1)^a X_e^(d-a), 0 <= a < m.  O7 vanishes beyond degree m.
    return tuple(totals)


def prefix_by_successive_unranking(e: int, degree: int, length: int) -> set[tuple[int, ...]]:
    """Small audit oracle only: at most 54 standard monomials per degree."""
    return {boundary_monomial(e, degree, rank) for rank in range(1, length + 1)}


def direct_generator_counts(e: int, m: int) -> tuple[int, ...]:
    """Count actual lex-ideal minimal generators, without using O7 or O10.

    Each candidate is a variable times a standard monomial in the previous
    degree.  It is a minimal generator exactly when it is nonstandard and
    every immediate monomial divisor is standard.  Enumerates only the small
    standard prefixes in the 83 frozen profiles, never whole degree layers.
    """
    hilbert = capped_hilbert(e, m)
    previous = prefix_by_successive_unranking(e, 1, e)
    totals = [0] * e
    for degree in range(2, m + 1):
        current = prefix_by_successive_unranking(e, degree, hilbert[degree])
        for child in current:
            for j, exponent in enumerate(child):
                if exponent:
                    divisor = list(child)
                    divisor[j] -= 1
                    require(tuple(divisor) in previous,
                            (e, m, degree, child, "standard prefixes are not an order ideal"))
        candidates = set()
        for parent in previous:
            for j in range(e):
                child = list(parent)
                child[j] += 1
                candidates.add(tuple(child))
        for candidate in candidates - current:
            minimal = True
            for j, exponent in enumerate(candidate):
                if exponent:
                    divisor = list(candidate)
                    divisor[j] -= 1
                    if tuple(divisor) not in previous:
                        minimal = False
                        break
            if minimal:
                largest = max(j for j, exponent in enumerate(candidate) if exponent)
                totals[largest] += 1
        previous = current
    return tuple(totals)


def all_exponent_tuples(variables: int, degree: int):
    """Tiny complete layers used solely to test rank/support primitives."""
    if variables == 1:
        yield (degree,)
        return
    for first in range(degree + 1):
        for suffix in all_exponent_tuples(variables - 1, degree - first):
            yield (first,) + suffix


def primitive_checks() -> int:
    checked = 0
    for e, degree in itertools.product(range(2, 6), range(1, 6)):
        layer = list(all_exponent_tuples(e, degree))
        histogram = [0] * (e + 1)
        for rank, monomial in enumerate(layer, 1):
            require(boundary_monomial(e, degree, rank) == monomial,
                    (e, degree, rank, "unranking disagrees with tiny enumeration"))
            maximum = max(j for j, exponent in enumerate(monomial, 1) if exponent)
            histogram[maximum] += 1
            expected = tuple(sum(histogram[:j + 1]) for j in range(e + 1))
            require(support_counts(e, degree, rank) == expected,
                    (e, degree, rank, "support disagrees with tiny enumeration"))
            checked += 1
    return checked


def frozen_manifest_checks() -> int:
    frozen_root = ROOT / "proof_integrated_v2"
    manifest = json.loads((frozen_root / "MANIFEST_SHA256.json").read_text())
    for relative, expected in manifest.items():
        actual = hashlib.sha256((frozen_root / relative).read_bytes()).hexdigest()
        require(actual == expected, (relative, "frozen manifest mismatch"))
    return len(manifest)


def certificate_checks() -> dict:
    path = ROOT / "proof_integrated_v2/certificates/small_ordinary.json"
    frozen = json.loads(path.read_text())
    reproduced = []
    margins = []
    for item in frozen["profiles"]:
        e, m = item["e"], item["m"]
        counts = o10_counts(e, m)
        require(counts == o7_counts(e, m), (e, m, "O7/O10 disagreement"))
        require(counts == direct_generator_counts(e, m),
                (e, m, "O10/direct lex generator disagreement"))
        raw = betti_from_counts(counts)
        target = tuple(i * choose(m, i + 1) for i in range(1, e + 1))
        row = {"e": e, "m": m, "rho": m - 1,
               "hilbert": list(capped_hilbert(e, m)),
               "maxvar_generator_counts": list(counts),
               "raw": list(raw), "target": list(target)}
        require(row == item, (e, m, "independent values disagree with frozen profile"))
        reproduced.append(row)
        for i, (source, capacity) in enumerate(zip(raw, target), 1):
            require(source <= capacity, (e, m, i, source, capacity))
            margins.append({"e": e, "m": m, "rho": m - 1, "row": i,
                            "raw": source, "capacity": capacity,
                            "margin": capacity - source})
    canonical = json.dumps(reproduced, sort_keys=True, separators=(",", ":")) + "\n"
    digest = hashlib.sha256(canonical.encode()).hexdigest()
    require(digest == frozen["profile_sha256"], "canonical profile hash mismatch")
    require(len(reproduced) == 83 and len(margins) == 665, "wrong frozen coverage")
    minimum = min(margins, key=lambda entry: entry["margin"])
    require(minimum == frozen["minimum_scalar_margin"], "minimum margin mismatch")
    return {"profiles": len(reproduced), "comparisons": len(margins),
            "minimum_margin": minimum, "profile_sha256": digest,
            "o7_and_direct_minimal_generator_checks": len(reproduced)}


def sweep(max_m: int) -> dict:
    increments = 0
    comparisons = 0
    smallest_delta = None
    largest_first_delta = {e: {"value": -1} for e in range(5, 10)}
    base_rows = []
    zero_slots = 0
    for e in range(5, 10):
        previous = o10_counts(e, e + 10)
        base_betti = betti_from_counts(previous)
        targets = tuple(i * choose(e + 10, i + 1) for i in range(1, e + 1))
        require(all(source <= target for source, target in zip(base_betti, targets)),
                (e, "base Betti inequality failed"))
        base_rows.append({"e": e, "m": e + 10, "T": list(previous),
                          "B": list(base_betti), "target": list(targets),
                          "margins": [target - source for source, target in zip(base_betti, targets)]})
        for m in range(e + 10, max_m + 1):
            following = o10_counts(e, m + 1)
            delta_t = tuple(after - before for before, after in zip(previous, following))
            require(all(delta >= 0 for delta in delta_t), (e, m, delta_t, "negative delta T"))
            delta_b = betti_from_counts(delta_t)
            require(delta_b[0] <= m, (e, m, delta_b[0], "delta B1 exceeds m"))
            require(all(value <= choose(e - 1, i - 1) * delta_b[0]
                        for i, value in enumerate(delta_b, 1)),
                    (e, m, delta_b, "EK weight comparison failed"))
            if delta_b[0] > largest_first_delta[e]["value"]:
                largest_first_delta[e] = {"m": m, "value": delta_b[0]}
            candidate = min(delta_t)
            smallest_delta = candidate if smallest_delta is None else min(smallest_delta, candidate)
            zero_slots += sum(delta == 0 for delta in delta_t)
            increments += 1
            comparisons += e
            previous = following
    return {"m_range_inclusive": "e+10 through " + str(max_m),
            "e_values": list(range(5, 10)), "increments": increments,
            "slot_comparisons": comparisons,
            "minimum_delta_T": smallest_delta, "zero_delta_T_slots": zero_slots,
            "largest_delta_B1_by_e": largest_first_delta,
            "base_rows": base_rows}


def isolated_large_checks() -> list[dict]:
    result = []
    for m, claimed in ((1000, 24), (10000, 19)):
        before = o10_counts(9, m)
        after = o10_counts(9, m + 1)
        delta_t = tuple(b - a for a, b in zip(before, after))
        delta_b = betti_from_counts(delta_t)
        require(delta_b[0] == claimed, (9, m, claimed, delta_b, "reported increment mismatch"))
        require(all(value >= 0 for value in delta_t), (9, m, delta_t))
        require(delta_b[0] <= m, (9, m, delta_b))
        require(all(value <= choose(8, i - 1) * delta_b[0]
                    for i, value in enumerate(delta_b, 1)), (9, m, delta_b))
        result.append({"e": 9, "m": m, "T_at_m": list(before),
                       "T_at_m_plus_1": list(after), "delta_T": list(delta_t),
                       "delta_B": list(delta_b)})
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-m", type=int, default=200)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    require(args.max_m >= 19, "max-m must include all five bases")
    started = time.monotonic()
    result = {"status": "FINITE_REGRESSION_PASS",
              "frozen_manifest_files_verified": frozen_manifest_checks(),
              "primitive_complete_prefix_checks": primitive_checks(),
              "frozen_certificate": certificate_checks(),
              "sweep": sweep(args.max_m),
              "isolated_large_checks": isolated_large_checks(),
              "scope": "Exact finite integer checks only; no universal extrapolation.",
              "elapsed_seconds": round(time.monotonic() - started, 3)}
    serialized = json.dumps(result, indent=2) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(serialized)
    print(serialized, end="")


if __name__ == "__main__":
    main()
