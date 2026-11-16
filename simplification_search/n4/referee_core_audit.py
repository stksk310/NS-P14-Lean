#!/usr/bin/env python3
"""Independent endpoint-membership audit of the proposed N4 reduction.

This deliberately does not import the old or candidate certificate code.
All source counts concern the homogeneous offset core, never a sampled m.
"""

from collections import deque
from math import comb, gcd
import json


def core_antichains(a, b, w):
    # Independent alternative: prefix zero-sum deletion generates the core
    # over k[x,v] with internal words of length <=w-1. Take the Pareto minima
    # separately in every residue, then use coordinate multiplication.
    columns = [set() for _ in range(w)]
    for n in range(w):
        for j in range(n + 1):
            B = a * (n - j) + b * j
            r = B % w
            K = B // w
            L = n - K - int(r > 0)
            columns[r].add((L, K))
    minimal = set()
    for r, column in enumerate(columns):
        for L, K in column:
            if not any(l <= L and k <= K and (l, k) != (L, K)
                       for l, k in column):
                minimal.add((r, L, K))
    socle = 0
    for r, L, K in minimal:
        degree = L + K + int(r > 0)
        offset = r + K * w
        images = []
        for step in (a, b):
            B = offset + step
            s = B % w
            k = B // w
            l = degree + 1 - k - int(s > 0)
            images.append((s, l, k) in minimal)
        socle += not any(images)
    return len(minimal), socle, max(L for r, L, K in minimal)


def core(a, b, w):
    # S[n] contains every offset of an n-letter word in {0,a,b,w}.
    # A pure internal word survives mod (x,v) exactly when its offset
    # is neither in S[n-1] nor in w+S[n-1].
    previous = set()
    standard = set()
    for n in range(w):
        endpoint_offsets = previous | {w + s for s in previous}
        for j in range(n + 1):
            i = n - j
            if a * i + b * j not in endpoint_offsets:
                standard.add((i, j))
        current = {s + t for s in previous for t in (0, a, b, w)}
        if n == 0:
            current = {0}
        previous = current
    # The existing short-word lemma says no survivor has degree >= w-1.
    assert all(i + j <= w - 2 for i, j in standard)
    socle = sum(
        (i + 1, j) not in standard and (i, j + 1) not in standard
        for i, j in standard
    )
    hx = max(i + j - (a * i + b * j + w - 1) // w for i, j in standard)

    lengths = [None] * w
    lengths[0] = 0
    queue = deque([0])
    while queue:
        r = queue.popleft()
        for t in (a, b):
            s = (r + t) % w
            if lengths[s] is None:
                lengths[s] = lengths[r] + 1
                queue.append(s)
    assert all(n is not None for n in lengths)
    W = 1 + sum(lengths)
    Rhat = min(W - w, w * max(hx - 2, 0))
    P = len(standard)
    assert (P, socle, hx) == core_antichains(a, b, w)
    assert socle * (socle + 1) // 2 <= P
    assert P <= W <= 1 + w * w // 4
    return P, socle, W, hx, Rhat


def audit(limit):
    rows = []
    failures = []
    total = 0
    for w in range(3, limit + 1):
        count = 0
        worst = None
        worst_pairs = []
        for a in range(1, w):
            for b in range(a + 1, w):
                if gcd(gcd(a, b), w) != 1:
                    continue
                P, s, W, hx, Rhat = core(a, b, w)
                upper = P + s + 1 + Rhat
                target = comb(w, 2) + 1
                gap = target - upper
                if worst is None or gap < worst:
                    worst = gap
                    worst_pairs = [[a, b]]
                elif gap == worst:
                    worst_pairs.append([a, b])
                if gap < 0:
                    failures.append({"a": a, "b": b, "w": w, "P_C": P,
                                     "sigma_C": s, "W": W, "H_x": hx,
                                     "Rhat": Rhat, "upper": upper,
                                     "target_min": target})
                count += 1
        rows.append({"w": w, "pairs": count, "min_gap": worst,
                     "worst_pairs": worst_pairs})
        total += count
    return {"limit": limit, "primitive_pair_count": total,
            "failures": failures, "widths": rows}


def main():
    report = {"method": "independent complete-offset endpoint membership",
              "audits": [audit(12), audit(16)]}
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
