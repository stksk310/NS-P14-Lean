#!/usr/bin/env python3
"""Independent primitive-four high-row certificate, from maximum orders.

No historical code or precomputed endpoint table is imported.  Integer values
are counts of actual tangent-cone monomials; no field-rank specialization is
used.  The accompanying proof establishes the finite cutoff and stable tail.
"""
from fractions import Fraction
from hashlib import sha256
from heapq import heappop, heappush
from itertools import combinations
from math import comb, gcd, prod
from pathlib import Path
import argparse
import json
import sys


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def binomial(n, i):
    return comb(n, i) if 0 <= i <= n else 0


def actual_order_function(generators):
    """Return exact ord on all integers, a finite x-socle search bound, and DP.

    For each residue mod m, Dijkstra finds the least offset b in <a,b,w>,
    breaking ties by the shortest number ell of nonzero offsets.  At weights
    n >= b + m*ell, ord(n)=(n-b)/m; below the largest such threshold we use
    elementary maximum-length dynamic programming in the original generators.
    """
    m = generators[0]
    offsets = tuple(g - m for g in generators[1:])
    dist = [None] * m
    dist[0] = (0, 0)
    queue = [(0, 0, 0)]
    while queue:
        value, length, residue = heappop(queue)
        if dist[residue] != (value, length):
            continue
        for offset in offsets:
            new_residue = (residue + offset) % m
            candidate = (value + offset, length + 1)
            if dist[new_residue] is None or candidate < dist[new_residue]:
                dist[new_residue] = candidate
                heappush(queue, (*candidate, new_residue))
    require(all(d is not None for d in dist), "all residues reached")
    thresholds = [value + m * length for value, length in dist]
    stop = max(thresholds)
    orders = [-1] * (stop + 1)
    orders[0] = 0
    for n in range(1, stop + 1):
        orders[n] = max((orders[n-g] + 1 for g in generators
                         if n >= g and orders[n-g] >= 0), default=-1)

    def order(n):
        if n < 0:
            return -1
        residue = n % m
        if n >= thresholds[residue]:
            return (n - dist[residue][0]) // m
        return orders[n]

    require(all(order(n) == orders[n] for n in range(stop + 1)),
            "all finite overlaps of order formula and DP agree")
    return order, stop, orders


def actual_invariants(a, b, w, m):
    require(0 < a < b < w < m and gcd(gcd(a, b), w) == 1,
            "primitive narrow source scope")
    generators = (m, m+a, m+b, m+w)
    order, stop, orders = actual_order_function(generators)
    words = []
    # The extra d=w-1 layer is a regression for the proven shortened bound.
    for degree in range(w):
        for u in range(degree + 1):
            z = degree - u
            n = u*(m+a) + z*(m+b)
            if order(n) != degree:
                continue
            if degree and (order(n-m) == degree-1 or
                           order(n-m-w) == degree-1):
                continue
            require(degree <= w-2, "shortened internal-word bound")
            words.append((u, z))
    standard = set(words)
    require(all(u == 0 or (u-1, z) in standard for u, z in words),
            "Q standard words are closed under y divisors")
    require(all(z == 0 or (u, z-1) in standard for u, z in words),
            "Q standard words are closed under z divisors")
    socle = [(u, z) for u, z in words
             if (u+1, z) not in standard and (u, z+1) not in standard]
    # Every x-socle element is below its own threshold, hence below stop.
    endpoint_socle = [n for n, degree in enumerate(orders)
                      if degree >= 0 and order(n+m) > degree+1
                      and order(n+m+w) > degree+1]
    P, R, sigma = len(words), len(endpoint_socle), len(socle)
    require(P <= comb(w, 2) and sigma <= w-1, "P and sigma bounds")
    require(R <= max(w-4, 0)+(w-1)*max(w-5, 0), "R corner bound")
    return dict(a=a, b=b, w=w, m=m, P=P, R=R, sigma=sigma,
                U2=2*P+3*R+sigma, Q_words=words, Q_socle=socle,
                endpoint_socle_weights=endpoint_socle)


def stable_invariants(a, b, w):
    """Direct homogeneous-offset enumeration, without competition ideals."""
    reachable = [{0}]
    for degree in range(1, w):
        reachable.append({n+offset for n in reachable[-1]
                          for offset in (0, a, b, w)})
    words = []
    pairs = [set() for _ in range(w)]
    for degree in range(w):
        for u in range(degree+1):
            z = degree-u
            n = u*a+z*b
            residue, K = n % w, n // w
            L = degree-K-int(residue > 0)
            require(L >= 0, "offset coordinate nonnegativity")
            pairs[residue].add((L, K))
            if degree and (n in reachable[degree-1] or
                           n-w in reachable[degree-1]):
                continue
            require(degree <= w-2, "stable core word length")
            words.append((u, z))
    minimal = [[p for p in sorted(row)
                if not any(q != p and q[0] <= p[0] and q[1] <= p[1]
                           for q in row)] for row in pairs]
    require(len(words) == sum(map(len, minimal)), "core word/ideal equality")
    for residue, row in enumerate(minimal):
        for L, K in row:
            require(L+K <= w-3 if residue else (L, K) == (0, 0),
                    "minimal core coordinate bound")
    standard = set(words)
    socle = [(u, z) for u, z in words
             if (u+1, z) not in standard and (u, z+1) not in standard]
    P, sigma = len(words), len(socle)
    return dict(a=a, b=b, w=w, m_from=w*(w-2), P=P, R=0,
                sigma=sigma, U2=2*P+sigma, Q_words=words, Q_socle=socle,
                minimal_core_coordinates=minimal)


def target_row(m, w, i):
    B = w-((m-1) % w)
    return i*binomial(w, i+1) + ((B+1-i)*binomial(w, i-1)
                                if i <= B else (i-B)*binomial(w, i))


def add(p, q):
    return [((p[i] if i < len(p) else 0) +
             (q[i] if i < len(q) else 0)) for i in range(max(len(p), len(q)))]


def scale(p, factor):
    return [factor*x for x in p]


def multiply(p, q):
    out = [Fraction(0)] * (len(p)+len(q)-1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i+j] += x*y
    return out


def choose_polynomial(shift, k):
    out = [Fraction(1)]
    for j in range(k):
        out = scale(multiply(out, [shift-j, 1]), Fraction(1, j+1))
    return out


def symbolic_capacities():
    # Coefficients in u, computed by exact polynomial arithmetic.
    w = [11, 1]
    source2 = add(add(scale(multiply(w, w), 4), scale(w, -15)), [2])
    target2 = add(scale(choose_polynomial(11, 3), 2), w)
    second = scale(add(target2, scale(source2, -1)), 3)
    w = [5, 1]
    source3_twice = add(add(scale(multiply(w, w), 7), scale(w, -31)), [6])
    target3 = add(scale(choose_polynomial(5, 4), 3), choose_polynomial(5, 2))
    third = add(scale(target3, 8), scale(source3_twice, -4))
    source4 = add(add(multiply(w, w), scale(w, -5)), [1])
    fourth = scale(add(scale(choose_polynomial(5, 5), 4), scale(source4, -1)), 30)
    expected = ([60, 83, 18, 1], [96, 34, 47, 14, 1],
                [90, 124, 195, 85, 15, 1])
    actual = tuple([int(c) if c.denominator == 1 else str(c) for c in p]
                   for p in (second, third, fourth))
    require(actual == expected, "exact capacity polynomial coefficients")
    return dict(second_u_w_minus_11=actual[0], third_u_w_minus_5=actual[1],
                fourth_u_w_minus_5=actual[2])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    finite, tails, summary = [], [], []
    for w in range(4, 11):
        pairs = [(a, b) for a, b in combinations(range(1, w), 2)
                 if gcd(gcd(a, b), w) == 1]
        min_target = min(target_row(m, w, 2) for m in range(w+1, 2*w+1))
        require(min_target == 2*comb(w, 3)+w, "periodic target minimum")
        current = []
        for a, b in pairs:
            tail = stable_invariants(a, b, w)
            require(tail['U2'] <= min_target, "infinite stable tail pays")
            tails.append(tail)
            onset = actual_invariants(a, b, w, w*(w-2))
            require((onset['Q_words'], onset['P'], onset['R'], onset['sigma']) ==
                    (tail['Q_words'], tail['P'], 0, tail['sigma']),
                    "actual-order onset agrees with homogeneous stable core")
            for m in range(w+1, w*(w-2)):
                inv = actual_invariants(a, b, w, m)
                require(inv['U2'] <= min_target, "finite point pays")
                finite.append(inv)
                current.append(inv)
        maximum = max(x['U2'] for x in current + tails if x['w'] == w)
        summary.append(dict(w=w, primitive_pairs=len(pairs), finite_points=len(current),
                            true_narrow_finite_points=sum(x['m'] >= w+2 for x in current),
                            max_U2=maximum, min_target_second=min_target,
                            slack=min_target-maximum))
    require(len(finite) == 4824 and len(tails) == 108, "full finite/tail counts")
    require(sum(row['true_narrow_finite_points'] for row in summary) == 4716,
            "requested true-narrow finite count")
    controls = []
    for a, b, w, m, expected in ((1,4,5,7,(5,0,2)), (1,4,5,9,(6,0,2)),
                                (12,24,37,121,(37,7,2)),
                                (25,75,101,526,(101,17,2))):
        inv = actual_invariants(a, b, w, m)
        require(tuple(inv[key] for key in ('P','R','sigma')) == expected,
                "non-CM and low-width invariant controls")
        controls.append(inv)
    payload = dict(schema="N4_HIGHER_ROWS_DIRECT_ORDER_V1", finite=finite, tails=tails,
                   summary=summary, controls=controls, polynomials=symbolic_capacities(),
                   qualification="Definitions plus proved cutoff/tail; counts use no field-rank assumptions.")
    encoded = json.dumps(payload, sort_keys=True, separators=(',', ':')).encode()
    out = dict(status="PASS", optimized=sys.flags.optimize,
               code_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
               mathematical_payload_sha256=sha256(encoded).hexdigest(), math=payload)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, sort_keys=True, indent=2)+'\n')
    print(json.dumps({key:out[key] for key in ('status','optimized','code_sha256',
                     'mathematical_payload_sha256')} | dict(finite=len(finite), tails=len(tails),
                     true_narrow_finite=4716, summary=summary), sort_keys=True))


if __name__ == '__main__':
    main()
