#!/usr/bin/env python3
"""Independent sanity checks for SMALL_WIDTH_SEARCH.md (not its paper proof)."""

from collections import deque
from itertools import combinations
from math import comb, gcd
from pathlib import Path
import json


ROOT = Path(__file__).resolve().parents[2]


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def exact_invariants(u, a, b):
    reachable = {0}
    standard = {(0, 0)}
    for n in range(1, u):
        for i in range(n + 1):
            j = n - i
            offset = a * i + b * j
            if offset not in reachable and offset - u not in reachable:
                require(n <= u - 2, (u, a, b, "cutoff"))
                standard.add((i, j))
        reachable = {v + c for v in reachable for c in (0, a, b, u)}
    sigma = sum((i + 1, j) not in standard
                and (i, j + 1) not in standard for i, j in standard)
    height = max(i + j - (a * i + b * j + u - 1) // u
                 for i, j in standard)
    distance = [None] * u
    distance[0] = 0
    queue = deque([0])
    while queue:
        r = queue.popleft()
        for c in (a, b):
            t = (r + c) % u
            if distance[t] is None:
                distance[t] = distance[r] + 1
                queue.append(t)
    require(None not in distance, (u, a, b, "reachability"))
    W = 1 + sum(distance)
    Rhat = min(W - u, u * max(height - 2, 0))
    return standard, dict(P_C=len(standard), sigma_C=sigma, Hx=height,
                          W=W, Rhat=Rhat,
                          U1=len(standard) + sigma + 1 + Rhat)


def circuit(u, a, b, lhs, rhs):
    """Exponent vectors are ordered x,y,z,v."""
    require(sum(lhs) == sum(rhs), (u, a, b, lhs, rhs, "degree"))
    offsets = (0, a, b, u)
    require(sum(i * j for i, j in zip(lhs, offsets))
            == sum(i * j for i, j in zip(rhs, offsets)),
            (u, a, b, lhs, rhs, "offset"))
    require(rhs[0] + rhs[3] > 0, (u, a, b, "endpoint"))


def check_small_cases(u, a, b, data):
    P, sigma, H = (data[k] for k in ("P_C", "sigma_C", "Hx"))
    k, h = u - b + a, u // 2
    E = comb(h - k + 2, 2) if k <= h else 0
    if u == 5:
        require(P <= 7 and sigma <= 3 and H <= 2, (u, a, b, data))
        upper = 11
    elif u == 6:
        if H <= 2:
            upper = 15
        else:
            require((a, b) == (1, 5), (u, a, b, "height forcing"))
            require(P <= 9 and sigma <= 2, (u, a, b, data))
            upper = 16
    elif u == 7:
        if k != 4:
            upper = 23 - k - E + min(4, k)
        elif (a, b) in ((1, 4), (3, 6)):
            require(P <= 7 and sigma <= 2, (u, a, b, data))
            upper = 16
        else:
            require((a, b) == (2, 5), (u, a, b, "gap class"))
            require(P <= 9 and sigma <= 2, (u, a, b, data))
            upper = 18
    elif u == 8:
        if k not in (4, 5, 6):
            upper = 31 - k - E + min(5, k)
        elif k == 4:
            require((a, b) in ((1, 5), (3, 7)), (u, a, b, "gap class"))
            require(P <= 14 and sigma <= 4, (u, a, b, data))
            upper = 28
        elif k == 5:
            require((a, b) in ((1, 4), (2, 5), (3, 6), (4, 7)),
                    (u, a, b, "gap class"))
            require(P <= 9 and sigma <= 2, (u, a, b, data))
            upper = 21
        elif (a, b) in ((1, 3), (5, 7)):
            require(P <= 14 and sigma <= 3, (u, a, b, data))
            upper = 27
        else:
            require((a, b) == (3, 5), (u, a, b, "gap class"))
            require(P <= 9 and sigma <= 2, (u, a, b, data))
            upper = 21
    else:
        return
    require(data["U1"] <= upper <= comb(u, 2) + 1,
            (u, a, b, data, upper))


def main():
    historical = json.loads((ROOT / "proof_integrated_v2/certificates/n4/"
                              "SHORTER_N4_CERTIFICATE.json").read_text())
    old_rows = {(r["w"], r["a"], r["b"]): r for r in historical["rows"]}
    checked = 0
    historical_checked = 0
    small_checked = 0
    counterexamples = []
    for u in range(3, 21):
        h = u // 2
        cap = 2 * u - 3 + comb(h - 1, 2)
        for a, b in combinations(range(1, u), 2):
            if gcd(gcd(a, b), u) != 1:
                continue
            checked += 1
            D, data = exact_invariants(u, a, b)
            k = u - b + a
            E = comb(h - k + 2, 2) if k <= h else 0
            require(all(i < b and j < u - a for i, j in D),
                    (u, a, b, "axis rectangle"))
            require(all(i < u - b or j < a for i, j in D),
                    (u, a, b, "mixed orthant"))
            require(data["P_C"] <= 2 * u - k - 1 + comb(h, 2) - E <= cap,
                    (u, a, b, "count", data))
            require(data["sigma_C"] <= min(h + 1, k),
                    (u, a, b, "socle", data))
            circuit(u, a, b, (0, b, 0, 0), (b - a, 0, a, 0))
            circuit(u, a, b, (0, 0, u - a, 0), (0, u - b, 0, b - a))
            circuit(u, a, b, (0, u - b, a, 0), (u - b, 0, 0, a))
            if 5 <= u <= 8:
                small_checked += 1
                check_small_cases(u, a, b, data)
            if (u, a, b) in old_rows:
                historical_checked += 1
                require(all(old_rows[u, a, b][key] == value
                            for key, value in data.items()),
                        (u, a, b, "historical disagreement"))
            if (u, a, b) in ((10, 1, 6), (12, 1, 7)):
                proposed = max(2 * u - 3, (u + 1) ** 2 // 8)
                require(data["P_C"] > proposed, (u, a, b, "counterexample"))
                counterexamples.append(dict(u=u, a=a, b=b,
                                            P_C=data["P_C"], proposed=proposed))
        upper = comb(h, 2) + u + 1 + u * u // 4
        doubled_gap = (h * (h - 5) if u % 2 == 0
                       else h * h - 3 * h - 2)
        require(2 * (comb(u, 2) + 1 - upper) == doubled_gap,
                (u, "gap identity"))
        if u >= 9:
            require(doubled_gap >= 0, (u, "global threshold"))

    # Every additional circuit explicitly used in the small-width prose.
    relations = [
        (6, 1, 5, (0, 1, 1, 0), (1, 0, 0, 1)),
        (6, 1, 5, (0, 5, 0, 0), (4, 0, 1, 0)),
        (6, 1, 5, (0, 0, 5, 0), (0, 1, 0, 4)),
        (7, 1, 4, (0, 4, 0, 0), (3, 0, 1, 0)),
        (7, 1, 4, (0, 0, 2, 0), (0, 1, 0, 1)),
        (7, 3, 6, (0, 2, 0, 0), (1, 0, 1, 0)),
        (7, 3, 6, (0, 0, 4, 0), (0, 1, 0, 3)),
        (7, 2, 5, (0, 1, 1, 0), (1, 0, 0, 1)),
        (8, 1, 5, (0, 5, 0, 0), (4, 0, 1, 0)),
        (8, 1, 5, (0, 0, 5, 0), (1, 1, 0, 3)),
        (8, 3, 7, (0, 5, 0, 0), (3, 0, 1, 1)),
        (8, 3, 7, (0, 0, 5, 0), (0, 1, 0, 4)),
        (8, 1, 4, (0, 0, 2, 0), (1, 0, 0, 1)),
        (8, 2, 5, (0, 0, 2, 0), (0, 1, 0, 1)),
        (8, 3, 6, (0, 2, 0, 0), (1, 0, 1, 0)),
        (8, 4, 7, (0, 2, 0, 0), (1, 0, 0, 1)),
        (8, 3, 5, (0, 1, 1, 0), (1, 0, 0, 1)),
    ]
    for args in relations:
        circuit(*args)
    require(historical_checked == 196, "all historical rows checked")
    print(json.dumps(dict(primitive_oriented_pairs_checked=checked,
                          widths=[3, 20], historical_rows_agree=historical_checked,
                          small_width_pairs_checked=small_checked,
                          additional_circuits_checked=len(relations),
                          conjecture_counterexamples=counterexamples), indent=2))


if __name__ == "__main__":
    main()
