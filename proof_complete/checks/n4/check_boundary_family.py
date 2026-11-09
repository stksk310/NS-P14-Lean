#!/usr/bin/env python3
"""Independent audit of <m,m+1,m+w-1,m+w>, 3 <= w <= 10.

The proof needs no Taylor rank calculation.  The optional old sixteen Taylor
cases are recomputed, compressed to ten lcm complexes, and recorded as an
additional audit.  No legacy checker is imported or executed.
"""
import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path


def require(test, message):
    if not test:
        raise RuntimeError(message)


def divides(a, b):
    return all(x <= y for x, y in zip(a, b))


def minimal(generators):
    ordered = sorted(set(map(tuple, generators)), key=lambda a: (sum(a), a))
    answer = []
    for a in ordered:
        if not any(divides(b, a) for b in answer):
            answer.append(a)
    return sorted(answer)


def core(t):
    return [(0, t, 0, 0), (0, 1, 1, 0)] + [
        (t - q, 0, q, 0) for q in range(2, t + 1)]


def columns(t):
    # (monomial b, its offset n_b, its degree c_b, optional x cap)
    return [((0, r, 0, 0), r, r, None) for r in range(t)] + [
        ((0, 0, q, 0), t * q, q, None if q == 1 else t - q)
        for q in range(1, t)]


def ceildiv(a, b):
    return -((-a) // b)


def actual_initial(t, m):
    """Formula proved in the accompanying note, using all relevant competitors."""
    w, maximum = t + 1, t * (t - 1)
    cutoff = (maximum - 1) // (m + w)
    period = w // math.gcd(m, w)
    generators = list(core(t))
    positive_count = 0
    for base, offset, degree, cap in columns(t):
        forbidden = []
        for j in range(1, cutoff + period + 1):
            r = (offset - j * m) % w
            kappa = (j * m + r - offset) // w
            anchor_degree = 1 if r == t else r
            delta = anchor_degree - degree - kappa - j
            forbidden.append((max(delta, 0), max(kappa, 0)))
            if delta > 0 and (cap is None or delta < cap):
                positive_count += 1
            if 2 <= r < t:
                require(delta - (r - 1) < 0, "short anchor has positive x threshold")
                forbidden.append((max(delta - r + 1, 0),
                                  max(kappa + t - r, 0)))
        for a, b in minimal(forbidden):
            generators.append(tuple(x + y for x, y in zip(base, (a, 0, 0, b))))
    return minimal(generators), positive_count


def small_initial(t, m):
    w = t + 1
    generators = list(core(t))
    for base, offset, degree, cap in columns(t):
        power = max(ceildiv(m - offset, w), 0)
        generators.append(tuple(x + y for x, y in zip(base, (0, 0, 0, power))))
    return minimal(generators)


def interval_betti(m, w):
    b0 = w - (m - 1) % w
    answer = [1]
    for i in range(1, w + 1):
        e = ((b0 + 1 - i) * math.comb(w, i - 1) if i <= b0
             else (i - b0) * math.comb(w, i))
        answer.append(i * math.comb(w, i + 1) + e if i < w else e)
    return answer


def w4_betti(m):
    if m == 6:
        return [1, 6, 8, 3, 0]
    residue = m % 4
    mu = 4 + (residue == 1) + (residue == 2) + (residue != 0) + (residue != 3)
    socle = 2 + (residue == 2) + (residue != 3) + (residue == 1)
    return [1, mu + 1, mu + socle + 2, socle + 3, 1]


def compressed(generators):
    """Strictly increasing coordinate relabeling preserves the whole lcm lattice."""
    rank = [{v: i for i, v in enumerate(sorted({0} | {g[j] for g in generators}))}
            for j in range(4)]
    return sorted(tuple(rank[j][g[j]] for j in range(4)) for g in generators)


def unit_elimination(rows, ncols):
    rows = {i: dict(r) for i, r in enumerate(rows) if r}
    live = set(range(ncols))
    pivots = []
    while True:
        choice = next(((i, j, r[j]) for i, r in sorted(rows.items())
                       for j in sorted(r) if j in live and abs(r[j]) == 1), None)
        if choice is None:
            break
        i, j, value = choice
        pivot = rows.pop(i)
        pivots.append([i, j, value])
        for r in rows.values():
            if j not in r:
                continue
            factor = r[j] * value  # value^{-1} = value for value = +/-1
            for k, a in pivot.items():
                updated = r.get(k, 0) - factor * a
                if updated:
                    r[k] = updated
                else:
                    r.pop(k, None)
        live.remove(j)
    residue = [[i, j, value] for i, r in sorted(rows.items())
               for j, value in sorted(r.items()) if j in live]
    return pivots, residue


def taylor(generators):
    n = len(generators)
    masks = [[s for s in range(1 << n) if s.bit_count() == i] for i in range(n + 1)]
    lcm = [(0, 0, 0, 0)] * (1 << n)
    for mask in range(1, 1 << n):
        bit = mask & -mask
        j = bit.bit_length() - 1
        lcm[mask] = tuple(max(a, b) for a, b in zip(lcm[mask ^ bit], generators[j]))
    ranks, all_pivots = [0], []
    for i in range(1, n + 1):
        index = {s: j for j, s in enumerate(masks[i - 1])}
        rows = [{} for _ in masks[i - 1]]
        for col, mask in enumerate(masks[i]):
            sign = 1
            for j in range(n):
                if mask & (1 << j):
                    face = mask ^ (1 << j)
                    if lcm[face] == lcm[mask]:
                        rows[index[face]][col] = sign
                    sign *= -1
        pivots, residue = unit_elimination(rows, len(masks[i]))
        require(not residue, f"Taylor boundary {i} has nonunit residual")
        ranks.append(len(pivots))
        all_pivots.append(pivots)
    ranks.append(0)
    betti = [len(masks[i]) - ranks[i] - ranks[i + 1] for i in range(n + 1)]
    require(all(b == 0 for b in betti[5:]), "nonzero Tor beyond four variables")
    return {"generators": generators, "ranks": ranks,
            "betti": (betti + [0] * 5)[:5], "unit_pivots": all_pivots,
            "zero_residual": True}


def exact_socle3(generators):
    bounds = []
    for j in range(3):
        powers = [g[j] for g in generators if g[j] and all(g[k] == 0 for k in range(3) if k != j)]
        require(powers, "quotient is not Artin")
        bounds.append(min(powers))
    basis = {a for a in itertools.product(*(range(b) for b in bounds))
             if not any(divides(g, a) for g in generators)}
    socle = sorted(a for a in basis if all(
        tuple(a[k] + (k == j) for k in range(3)) not in basis for j in range(3)))
    return socle


def all_degrees(d, count=4):
    if count == 1:
        yield (d,)
    else:
        for first in range(d + 1):
            for rest in all_degrees(d - first, count - 1):
                yield (first,) + rest


def actual_degree_regression(t, m, degree=5):
    generators, positive = actual_initial(t, m)
    weights = [m, m + 1, m + t, m + t + 1]
    limit = degree * max(weights)
    order = [-1] * (limit + 1)
    order[0] = 0
    for n in range(1, limit + 1):
        order[n] = max((order[n - g] + 1 for g in weights if n >= g and order[n - g] >= 0), default=-1)
    for d in range(degree + 1):
        normals = [sum(a * b for a, b in zip(mon, weights)) for mon in all_degrees(d)
                   if not any(divides(g, mon) for g in generators)]
        require(len(normals) == len(set(normals)), "duplicate normal monomial weight")
        require(set(normals) == {n for n, value in enumerate(order) if value == d},
                "actual semigroup maximal-order basis disagrees")
    return positive


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path)
    parser.add_argument("--legacy", type=Path)
    parser.add_argument("--regression", action="store_true")
    args = parser.parse_args()
    w4 = []
    for m in range(6, 11):
        ideal = small_initial(3, m)
        jprime = minimal(g[1:] for g in ideal if g[0] == 0)
        socle = exact_socle3(jprime)
        mu, tau = len(jprime), len(socle)
        derived = [1, mu, mu + tau - 1, tau, 0] if m == 6 else [1, mu + 1, mu + tau + 2, tau + 3, 1]
        require(derived == w4_betti(m), "w4 symbolic formula disagreement")
        target = interval_betti(m, 4)
        require(all(x <= y for x, y in zip(derived, target)), "w4 target failure")
        if m > 6:
            colon = minimal(tuple(max(g[j] - (2 if j == 1 else 0), 0) for j in range(3)) for g in jprime)
            theta = ceildiv(m - 6, 4)
            require(colon == sorted([(1, 0, 0), (0, 1, 0), (0, 0, theta)]), "w4 colon failure")
        w4.append({"m": m, "residue_mod_4": m % 4, "Jprime": jprime,
                   "socle_monomials": socle, "initial_quotient_betti": derived, "target": target})
    w5_bound = [1, 10, 22, 13, 2]
    w5_min = [min(interval_betti(m, 5)[i] for m in range(7, 12)) for i in range(5)]
    require(all(x <= y for x, y in zip(w5_bound, w5_min)), "w5 target failure")
    broad = []
    for t in range(5, 10):
        h = sum(max(t - 2 * j - 2, 0) for j in range(1, t))
        c = 3 * t - 3 + h
        upper = [1, 3 * t + h, 3 * c, 3 * c - 2 * (2 * t - 1), c - (2 * t - 1)]
        lower = [1, t * (t + 1) // 2 + 1] + [i * math.comb(t + 1, i + 1) for i in range(2, 5)]
        require(all(x <= y for x, y in zip(upper, lower)), "w6..10 target failure")
        broad.append({"w": t + 1, "H": h, "C": c, "source_upper": upper, "target_lower": lower})
    classes, old_rows = {}, []
    old = None
    if args.legacy:
        data = json.loads(args.legacy.read_text())
        old = {(a["t"], a["m"]): a for a in data["small_width_certificates"]}
    for t in (3, 4):
        for m in range(t + 3, t * (t - 1) + t + 2):
            ideal = small_initial(t, m)
            actual, positive = actual_initial(t, m)
            require(ideal == actual and positive == 0, "small-width actual-ideal disagreement")
            canonical = compressed(ideal)
            key = json.dumps(canonical)
            if key not in classes:
                cert = taylor(canonical)
                cert["class"] = len(classes) + 1
                classes[key] = cert
            cert = classes[key]
            target = interval_betti(m, t + 1)
            require(all(x <= y for x, y in zip(cert["betti"], target)), "Taylor target disagreement")
            if t == 3:
                require(cert["betti"] == w4_betti(m), "Taylor/mapping-cone disagreement")
            if old is not None:
                previous = old[(t, m)]
                require(ideal == list(map(tuple, previous["generators"])), "legacy ideal mismatch")
                require(cert["betti"] == previous["betti"], "legacy Betti mismatch")
                require(cert["ranks"] == previous["ranks"], "legacy rank mismatch")
            if m > t * (t - 1):
                shifted = minimal((a, b, c, d + (d > 0)) for a, b, c, d in ideal)
                require(shifted == small_initial(t, m + t + 1), "periodic ideal translation failure")
            old_rows.append({"t": t, "w": t + 1, "m": m, "class": cert["class"],
                             "betti": cert["betti"], "target": target})
    pivots, residual = unit_elimination([{0: 2}], 1)
    require(not pivots and residual == [[0, 0, 2]], "nonunit rank negative control accepted")
    regression_count = 0
    if args.regression:
        for t in range(3, 10):
            for m in range(t + 3, t * (t - 1) + t + 2):
                positive = actual_degree_regression(t, m)
                require(positive <= sum(max(t - 2 * j - 2, 0) for j in range(1, t)),
                        "positive-column counting bound disagreement")
                regression_count += 1
    result = {"status": "PASS", "scope": "all m >= w+2, all 3 <= w <= 10; arbitrary fields",
              "required_finite_rank_calculations": 0, "w3": "source equals target",
              "w4_mapping_cone_rows": w4, "w5_source_upper": w5_bound,
              "w5_target_minimum": w5_min, "w6_to_w10": broad,
              "optional_legacy_taylor_rows": old_rows,
              "optional_taylor_lcm_classes": list(classes.values()),
              "optional_taylor_class_count": len(classes),
              "legacy_comparison": "PASS" if old is not None else "NOT_REQUESTED",
              "actual_order_regressions": regression_count,
              "nonunit_negative_control": "REJECTED [2]"}
    encoded = json.dumps(result, sort_keys=True, ensure_ascii=False, indent=2) + "\n"
    if args.out:
        args.out.write_text(encoded)
    print(json.dumps({"status": "PASS", "required_finite_rank_calculations": 0,
                      "optional_taylor_cases": len(old_rows), "optional_taylor_classes": len(classes),
                      "legacy_comparison": result["legacy_comparison"],
                      "actual_order_regressions": regression_count,
                      "certificate_sha256": hashlib.sha256(encoded.encode()).hexdigest()}, sort_keys=True))


if __name__ == "__main__":
    main()
