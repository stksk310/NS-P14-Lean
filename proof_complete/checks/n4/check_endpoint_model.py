#!/usr/bin/env python3
"""Independent finite checks of the endpoint model; no R25 graph machinery."""
from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import deque
from pathlib import Path


def minimal(points):
    points = set(points)
    return sorted(p for p in points if not any(q != p and q[0] <= p[0] and q[1] <= p[1] for q in points))


def inside(point, generators):
    return any(g[0] <= point[0] and g[1] <= point[1] for g in generators)


def core(a, b, u):
    raw = [[] for _ in range(u)]
    for iy in range(u):
        for iz in range(u - iy):
            offset = iy * a + iz * b
            r, k = offset % u, offset // u
            raw[r].append((iy + iz - k - bool(r), k))
    return [minimal(points) for points in raw]


def competition(M, m, d, u, extra_periods=0):
    period = u // math.gcd(m, u)
    stop = (u - 2) // 2 + period
    raw = [[] for _ in range(u)]
    for j in range(1, stop + extra_periods * period + 1):
        for r in range(u):
            s = (r + j * m) % u
            carry = (r + j * m - s) // u
            for l, k in M[r]:
                raw[s].append((max(0, l - j * d - carry + bool(r) - bool(s)), k + carry))
    T = [minimal(points) for points in raw]
    N = [minimal((max(p[0], q[0]), max(p[1], q[1])) for p in M[r] for q in T[r]) for r in range(u)]
    return T, N, stop


def corners(gens):
    """Increasing x powers, decreasing v powers."""
    return [(gens[i + 1][0] - 1, gens[i][1] - 1) for i in range(len(gens) - 1)]


def sumsets(a, b, u, degree):
    levels = [{0}]
    for _ in range(degree):
        levels.append({old + step for old in levels[-1] for step in (0, a, b, u)})
    return levels


def numeric_order(generators, limit):
    order = [-1] * (limit + 1)
    order[0] = 0
    for weight in range(1, limit + 1):
        order[weight] = max((order[weight - g] + 1 for g in generators if weight >= g and order[weight - g] >= 0), default=-1)
    return order


def inspect(a, b, u, m, d, degree):
    M = core(a, b, u)
    T, N, stop = competition(M, m, d, u)
    T_more, N_more, _ = competition(M, m, d, u, extra_periods=3)
    assert T == T_more and N == N_more, ("finite stop", a, b, u, m, d)
    pc = sum(map(len, M))
    p = sum(not inside(g, N[r]) for r in range(u) for g in M[r])
    actual_corners = [(r, point) for r in range(u) for point in corners(N[r]) if inside(point, M[r])]
    R = len(actual_corners)

    levels = sumsets(a, b, u, max(u, degree + 1))
    Q = {(n, off) for n in range(len(levels)) for off in levels[n]
         if n == 0 or (off not in levels[n - 1] and off - u not in levels[n - 1])}
    modeled_Q = {(l + k + bool(r), r + u * k) for r in range(u) for l, k in M[r]}
    assert Q == modeled_Q, ("core Artin basis", a, b, u)
    sigma = sum((n + 1, off + a) not in Q and (n + 1, off + b) not in Q for n, off in Q)
    assert pc == len(Q)

    lengths = [None] * u
    lengths[0] = 0
    queue = deque([0])
    while queue:
        r = queue.popleft()
        for step in (a, b):
            s = (r + step) % u
            if lengths[s] is None:
                lengths[s] = lengths[r] + 1
                queue.append(s)
    W = 1 + sum(lengths)
    Hx = max(l for points in M for l, _ in points)
    rhat = min(W - u, u * max(Hx - 2, 0))
    assert pc <= W and R <= rhat, ("socle bound", a, b, u, m, d, pc, R, W, Hx)
    assert all(points[0][0] == 0 for points in T), ("pure v competitor", a, b, u, m, d)
    kappa = [min(k for _, k in points) for points in T]
    assert all(kappa[s] >= math.ceil((m - s) / u) for s in range(u))
    assert sum(math.ceil((m - s) / u) for s in range(u)) == m
    assert all(len(T[s]) - 1 <= l + k - kappa[s] for s in range(u) for l, k in T[s])

    degree_dp = max([degree] + [l + k + bool(r) + 1 for r, (l, k) in actual_corners])
    if degree_dp + 1 >= len(levels):
        levels = sumsets(a, b, u, degree_dp + 1)
    gens = (m, m + d * a, m + d * b, m + d * u)
    orders = numeric_order(gens, (degree_dp + 1) * (m + d * u))
    basis_checks = 0
    dp_socle = set()
    for n in range(degree_dp + 1):
        for off in levels[n]:
            r, k = off % u, off // u
            point = (n - k - bool(r), k)
            killed = inside(point, N[r])
            weight = n * m + d * off
            assert killed == (orders[weight] > n), ("actual order", a, b, u, m, d, n, off)
            basis_checks += 1
            if not killed and orders[weight + m] > n + 1 and orders[weight + m + d * u] > n + 1:
                dp_socle.add((r, point))
    assert dp_socle == set(actual_corners), ("endpoint socle DP", a, b, u, m, d, dp_socle, actual_corners)
    return {"a": a, "b": b, "u": u, "m": m, "d": d, "P_C": pc, "P": p,
            "R": R, "sigma": sigma, "W": W, "H_x": Hx, "R_hat": rhat,
            "stop": stop, "basis_checks": basis_checks, "degree_checked": degree_dp}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-u", type=int, default=10)
    parser.add_argument("--max-d", type=int, default=3)
    parser.add_argument("--m-excess", type=int, default=5)
    parser.add_argument("--degree", type=int, default=12)
    args = parser.parse_args()
    count = 0
    basis_checks = 0
    max_R = None
    max_sigma = None
    examples = []
    for u in range(3, args.max_u + 1):
        for a, b in itertools.combinations(range(1, u), 2):
            if math.gcd(math.gcd(a, b), u) != 1:
                continue
            for d in range(1, args.max_d + 1):
                for m in range(d * u + 1, d * u + args.m_excess + 1):
                    if math.gcd(m, d) != 1:
                        continue
                    row = inspect(a, b, u, m, d, args.degree)
                    count += 1
                    basis_checks += row["basis_checks"]
                    if max_R is None or row["R"] > max_R["R"]:
                        max_R = row
                    if max_sigma is None or row["sigma"] > max_sigma["sigma"]:
                        max_sigma = row
                    if (a, b, u, m, d) in [(1, 4, 5, 7, 1), (1, 2, 3, 4, 1)]:
                        examples.append(row)
    result = {"scope": vars(args), "sources_checked": count, "numeric_basis_checks": basis_checks,
              "max_R_example": max_R, "max_sigma_example": max_sigma, "named_examples": examples,
              "status": "PASS", "logical_role": "finite regression only; universal claims use the written proof"}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
