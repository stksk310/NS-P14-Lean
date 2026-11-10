#!/usr/bin/env python3
"""Independent finite DP checks of actual semigroup numerical coordinates."""
from itertools import combinations
from functools import reduce
from math import gcd
from pathlib import Path
import json

models = {(1,), (3, 4), (6, 7, 15), (4, 5, 11)}
for m in range(2, 9):
    models.add(tuple(range(m, 2 * m)))
    for g in range(m + 1, m + 11):
        if gcd(m, g) == 1:
            models.add((m, g))
    for g in range(m + 1, m + 7):
        for h in range(g + 1, m + 11):
            if reduce(gcd, (m, g, h)) == 1:
                models.add((m, g, h))

counts = {"models": 0, "membership_and_atomic_order_values": 0,
          "positive_element_vs_atomic_order_values": 0,
          "apery_elements": 0, "apery_decompositions": 0,
          "terminal_head_checks": 0, "live_jump_checks": 0,
          "models_with_redundant_input_generators": 0,
          "live_base_without_live_head": 0, "live_head_without_live_base": 0}
anchors = {}
N = 600
for generators in sorted(models):
    assert reduce(gcd, generators) == 1 and all(g > 0 for g in generators)
    m = min(generators)
    reachable = [False] * (N + 1)
    reachable[0] = True
    for x in range(1, N + 1):
        reachable[x] = any(x >= g and reachable[x - g] for g in generators)
    conductor = next(c for c in range(N - m + 2) if all(reachable[c:c + m]))
    # m consecutive reachable numbers and closure under +m prove cofiniteness.
    assert all(reachable[conductor:])
    apery = [next(x for x in range(conductor + m) if reachable[x] and x % m == r)
             for r in range(m)]
    aset = set(apery)
    assert len(aset) == m and 0 in aset and m not in aset
    atom_bound = max(m, conductor + m - 1)
    atoms = [x for x in range(1, atom_bound + 1) if reachable[x]
             and not any(reachable[u] and reachable[x - u] for u in range(1, x))]
    e = len(atoms)
    deficit = m - e
    assert 0 < e <= m and set(atoms).issubset(generators) and m in atoms
    assert set(atoms) - {m} <= aset
    if len(atoms) < len(generators):
        counts["models_with_redundant_input_generators"] += 1
    atomic_order = [None] * (N + 1)
    atomic_order[0] = 0
    for x in range(1, N + 1):
        lengths = [atomic_order[x - a] + 1 for a in atoms
                   if x >= a and atomic_order[x - a] is not None]
        if lengths:
            atomic_order[x] = max(lengths)
        assert (atomic_order[x] is not None) == reachable[x]
        if reachable[x]:
            assert atomic_order[x] * m <= x
            assert (atomic_order[x] == 1) == (x in atoms)
        counts["membership_and_atomic_order_values"] += 1
    order = [v if v is not None else 0 for v in atomic_order]
    limit = max(160, max(apery) + m + max(generators))
    assert limit + m + 3 * m <= N
    # A second DP uses every positive semigroup element, not the atom list.
    positive_order = [None] * (limit + 1)
    positive_order[0] = 0
    for x in range(1, limit + 1):
        lengths = [positive_order[x - u] + 1 for u in range(1, x + 1)
                   if reachable[u] and positive_order[x - u] is not None]
        if lengths:
            positive_order[x] = max(lengths)
        assert positive_order[x] == atomic_order[x]
        counts["positive_element_vs_atomic_order_values"] += 1
    for x in range(limit + 1):
        if reachable[x]:
            w = apery[x % m]
            assert w <= x and (x - w) % m == 0
            q = (x - w) // m
            assert x == w + q * m
            assert (x in aset) == (not (x >= m and reachable[x - m]))
            counts["apery_decompositions"] += 1
    assert {w for w in apery if order[w] == 0} == {0}
    assert {w for w in apery if order[w] == 1} == set(atoms) - {m}
    high = {w for w in apery if order[w] >= 2}
    assert len(high) == deficit
    assert len([w for w in apery if order[w] == 2]) <= deficit
    nu = max(order[w] for w in apery)
    assert set(order[w] for w in apery) == set(range(nu + 1))
    assert nu <= deficit + 1
    for w in apery:
        assert order[w] <= deficit + 1
        if order[w] > 0:
            assert any(w >= a and w - a in aset and order[w - a] == order[w] - 1 for a in atoms)
        counts["apery_elements"] += 1

    def terminal(x):
        return reachable[x] and order[x + m] > order[x] + 1

    def nonapery_head(y):
        return reachable[y] and y not in aset and not (
            y >= m and reachable[y - m] and order[y] == order[y - m] + 1)

    terminals = []
    for x in range(limit + 1):
        assert terminal(x) == nonapery_head(x + m)
        if terminal(x):
            assert x > 0 and order[x + m] - order[x] >= 2 and order[x + m] >= 3
            assert (x + m) - m == x
            terminals.append(x)
        if nonapery_head(x):
            assert x >= m and terminal(x - m)
        counts["terminal_head_checks"] += 1
        if not reachable[x]:
            continue
        for g in range(3 * m + 1):
            if not reachable[g]:
                continue
            j0 = order[x + m] - order[x]
            j1 = order[x + g + m] - order[x + g]
            assert j0 >= 1 and j1 >= 1
            assert order[x + g] >= order[x] + order[g]
            base_live = order[x + g] == order[x] + order[g]
            head_live = order[x + g + m] == order[x + m] + order[g]
            if base_live:
                assert j0 <= j1
            if head_live:
                assert j1 <= j0
            if j0 == j1:
                assert base_live == head_live
            if base_live and not head_live:
                counts["live_base_without_live_head"] += 1
            if head_live and not base_live:
                counts["live_head_without_live_base"] += 1
            counts["live_jump_checks"] += 1
    if generators in {(1,), (3, 4), (6, 7, 15), (4, 5, 11), tuple(range(8, 16))}:
        anchors[','.join(map(str, generators))] = {
            "multiplicity": m, "least_conductor": conductor, "atoms": atoms,
            "embedding_dimension": e, "deficit": deficit, "apery_by_residue": apery,
            "apery_orders": [order[w] for w in apery], "max_apery_order": nu,
            "terminal_labels_within_checked_prefix": terminals, "prefix_limit": limit}
    if generators == (4, 5, 11):
        assert order[1] == 0 and not reachable[1]
        assert (order[11], order[15], order[19]) == (1, 3, 4)
        assert order[11] == order[0] + order[11]
        assert order[15] != order[4] + order[11]
        assert order[15] != order[11] + order[4]
        assert order[19] == order[15] + order[4]
    counts["models"] += 1
assert counts["models_with_redundant_input_generators"] > 0
assert counts["live_base_without_live_head"] > 0 and counts["live_head_without_live_base"] > 0
assert anchors['1']['multiplicity'] == anchors['1']['embedding_dimension'] == 1
assert anchors['3,4']['apery_by_residue'] == [0, 4, 8]
assert anchors['6,7,15']['least_conductor'] == 24
record = {"status": "PASS", "counts": counts, "anchors": anchors,
          "scope": "Exact finite dynamic programs, including independent maximal positive-element and maximal atomic decomposition lengths. These are supplementary checks; general results are proved in Lean. Live conditions here are numerical and do not construct module actions."}
Path(__file__).with_name('semigroup_finite_checks.json').write_text(json.dumps(record, indent=2) + '\n')
print('PASS:', counts)
