#!/usr/bin/env python3
"""Independent finite AP head Koszul ranks; experiments, not a general proof."""
from collections import defaultdict
from heapq import heappop, heappush
from itertools import combinations
from math import comb, gcd
from pathlib import Path
import hashlib
import json


def choose(n, i):
    return comb(n, i) if 0 <= i <= n else 0


def rank(columns, prime):
    pivots = {}
    for original in columns:
        col = {i: x % prime for i, x in original.items() if x % prime}
        while col:
            pivot = min(col)
            if pivot not in pivots:
                inv = pow(col[pivot], -1, prime)
                pivots[pivot] = {i: x * inv % prime for i, x in col.items()}
                break
            scale = col[pivot]
            for i, x in pivots[pivot].items():
                col[i] = (col.get(i, 0) - scale * x) % prime
                if not col[i]:
                    del col[i]
    return len(pivots)


def actual_head(m, d, v):
    # Dijkstra computes the least semigroup value in each residue, without
    # using the AP Apery, order, multiplication or Betti formulas under audit.
    atoms = [m + j * d for j in range(v + 1)]
    dist = [None] * m
    dist[0] = 0
    queue = [(0, 0)]
    while queue:
        h, r = heappop(queue)
        if dist[r] != h:
            continue
        for a in atoms:
            nr = (r + a) % m
            nh = h + a
            if dist[nr] is None or nh < dist[nr]:
                dist[nr] = nh
                heappush(queue, (nh, nr))
    assert all(h is not None for h in dist)
    apery = set(dist)
    bound = max(apery) + max(atoms)
    order = [-1] * (bound + 1)
    order[0] = 0
    for h in range(1, bound + 1):
        terms = [order[h-a] + 1 for a in atoms if a <= h and order[h-a] >= 0]
        if terms:
            order[h] = max(terms)
    # Independently check regular-x order on the complete Apéry window.
    assert all(order[h+m] == order[h] + 1 for h in apery)
    action = {}
    for h in apery:
        for j, a in enumerate(atoms[1:]):
            action[h, j] = h+a if h+a in apery and order[h+a] == order[h]+1 else None
    # The independently constructed actual actions must commute and generate
    # the entire finite head from its constant, before any ranks are used.
    for h in apery:
        for i in range(v):
            for j in range(v):
                a, b = action[h, i], action[h, j]
                assert (None if a is None else action[a, j]) == (
                    None if b is None else action[b, i])
    reached, pending = {0}, [0]
    while pending:
        h = pending.pop()
        for j in range(v):
            dest = action[h, j]
            if dest is not None and dest not in reached:
                reached.add(dest)
                pending.append(dest)
    assert reached == apery
    return atoms[1:], apery, action


def actual_betti(m, d, v, primes):
    variables, apery, action = actual_head(m, d, v)
    slots = [list(combinations(range(v), i)) for i in range(v+1)]
    blocks = [defaultdict(list) for _ in range(v+1)]
    for i in range(v+1):
        for h in sorted(apery):
            for wedge in slots[i]:
                weight = h + sum(variables[j] for j in wedge)
                blocks[i][weight].append((h, wedge))
    ranks = {p: [0] * (v+2) for p in primes}
    for i in range(1, v+1):
        for weight, sources in blocks[i].items():
            rows = {a: j for j, a in enumerate(blocks[i-1].get(weight, []))}
            columns = []
            for h, wedge in sources:
                col = {}
                for pos, j in enumerate(wedge):
                    dest = action[h, j]
                    if dest is not None:
                        target = (dest, wedge[:pos]+wedge[pos+1:])
                        col[rows[target]] = (-1)**pos
                columns.append(col)
            for p in primes:
                ranks[p][i] += rank(columns, p)
    return {p: [m*choose(v, i)-ranks[p][i]-ranks[p][i+1]
                for i in range(v+1)] for p in primes}


def main():
    primes = [2, 3, 101]
    records = []
    residue_endpoints = set()
    for m in range(2, 16):
        for v in range(1, min(m, 7)):
            for d in range(1, 6):
                if gcd(m, d) != 1:
                    continue
                defect = v-(m-1) % v
                expected = [1] + [i*choose(v, i+1) + (
                    (defect+1-i)*choose(v, i-1) if i <= defect
                    else (i-defect)*choose(v, i)) for i in range(1, v+1)]
                actual = actual_betti(m, d, v, primes)
                for p in primes:
                    assert actual[p] == expected, (m, d, v, p, actual[p], expected)
                residue_endpoints.add((v, defect))
                records.append(dict(m=m, d=d, v=v, defect=defect,
                                    betti=expected, verified_characteristics=primes))
    result = dict(status='PASS_FINITE_INDEPENDENT_KOSZUL_CHECKS',
                  limitation='Finite AP examples only; not a proof of all parameters.',
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  cases=len(records), field_checks=len(records)*len(primes),
                  characteristics=primes, residue_endpoints=sorted(residue_endpoints),
                  records=records)
    target = Path(__file__).with_name('ap_koszul_checks.json')
    target.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
    print(result['status'], result['cases'], 'APs,', result['field_checks'], 'field checks')


if __name__ == '__main__':
    main()
