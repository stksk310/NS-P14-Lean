#!/usr/bin/env python3
"""Independent shortest paths, longest words, actual multiplication and GF(16) cuts.

Finite experiments supplement the Lean proofs. No production implementation or
submitted numerical outputs are imported.
"""
from pathlib import Path
from itertools import product, combinations
from fractions import Fraction
from heapq import heappush, heappop
from math import gcd, comb
import json
import random


def mul(a, b):
    z = 0
    while b:
        if b & 1:
            z ^= a
        a <<= 1
        if a & 16:
            a ^= 19  # GF(16), t^4+t+1
        b >>= 1
    return z


MUL = [[mul(a, b) for b in range(16)] for a in range(16)]
INV = {a: next(b for b in range(1, 16) if MUL[a][b] == 1) for a in range(1, 16)}


def rank_cols(cols, rows):
    a = [list(row) for row in zip(*cols)] if cols else [[] for _ in range(rows)]
    r = 0
    for c in range(len(cols)):
        s = next((j for j in range(r, rows) if a[j][c]), None)
        if s is None:
            continue
        a[r], a[s] = a[s], a[r]
        inv = INV[a[r][c]]
        a[r] = [MUL[x][inv] for x in a[r]]
        for j in range(rows):
            if j != r:
                k = a[j][c]
                a[j] = [x ^ MUL[k][y] for x, y in zip(a[j], a[r])]
        r += 1
        if r == rows:
            break
    return r


def candidates(n):
    for i in range(n):
        yield tuple(int(i == j) for j in range(n))
    rng = random.Random(72410+n)
    for _ in range(128):
        yield tuple(rng.randrange(16) for _ in range(n))
    yield from product(range(16), repeat=n)


def green_cut(n, a, mu):
    p = 0
    while comb(p+2, 2) <= a:
        p += 1
    b = a-comb(p+1, 2)
    assert 0 <= b <= p and p <= n
    e = [tuple(int(i == j) for j in range(n)) for i in range(n)]
    assert rank_cols([mu(x, y) for x in e for y in e], a) == a
    forms, images, prefix = [], [], [a]
    for s in range(1, p+1):
        bound = comb(p+1-s, 2)+max(b-s, 0)
        for v in candidates(n):
            if rank_cols(forms+[v], n) != s:
                continue
            cols = [mu(v, x) for x in e]
            remaining = a-rank_cols(images+cols, a)
            if remaining <= bound:
                forms.append(v)
                images += cols
                prefix.append(remaining)
                break
        else:
            raise AssertionError('No Green step')
    if n >= 2:
        for v in e:
            if len(forms) >= max(2, p):
                break
            if rank_cols(forms+[v], n) > len(forms):
                forms.append(v)
    assert rank_cols(forms, n) == len(forms)
    assert rank_cols([mu(v, x) for v in forms for x in e], a) == a
    return forms, p, prefix


def shortest_residues(m, weights):
    dist = [(10**12, 10**12)]*m
    pred = [None]*m
    dist[0] = (0, 0)
    queue = [(0, 0, 0)]
    while queue:
        d, length, r = heappop(queue)
        if (d, length) != dist[r]:
            continue
        for w in weights:
            s = (r+w) % m
            alt = (d+w, length+1)
            if alt < dist[s]:
                dist[s] = alt
                pred[s] = (r, w)
                heappush(queue, (*alt, s))
    assert all(x[0] < 10**12 for x in dist)
    return dist, pred


def choose(n, j):
    return comb(n, j) if 0 <= j <= n else 0


def model(gens):
    m = min(gens)
    apery = [x[0] for x in shortest_residues(m, gens)[0]]
    limit = max(apery)+max(gens)*m+8*m
    order = [-1]*(limit+1)
    order[0] = 0
    for x in range(1, limit+1):
        options = [order[x-g]+1 for g in gens if g <= x and order[x-g] >= 0]
        order[x] = max(options, default=-1)
    atoms = [g for g in gens if order[g] == 1]
    assert atoms and atoms[0] == m
    e = len(atoms)
    nonx = atoms[1:]
    if m == 1:
        dist, pred = [(0, 0)], [None]
    else:
        dist, pred = shortest_residues(m, [g-m for g in nonx])
    offsets = [x[0] for x in dist]
    lengths = [x[1] for x in dist]
    levels = [(w-b)//m for w, b in zip(apery, offsets)]
    assert all(w >= b and (w-b) % m == 0 for w, b in zip(apery, offsets))
    ranks = {b: i for i, b in enumerate(sorted(offsets))}
    deficit = m-e
    terminal = []
    decreasing_prefix = None
    for r in range(m):
        b, length, level, w = offsets[r], lengths[r], levels[r], apery[r]
        if r:
            assert 1 <= order[w] <= level <= length < m
        else:
            assert b == length == level == w == 0
        assert max(level-1, 0) <= min(deficit, max(ranks[b]-1, 0))
        for q in range(length+7):
            x = w+q*m
            if q+level >= length:
                assert order[x] == level+q
            if order[x+m] > order[x]+1:
                terminal.append(x)
                assert q < length
        assert sum(order[x+m]-order[x]-1 for x in terminal if x % m == r) == level-order[w]
        if r:
            path, at = [r], r
            while at:
                at, _ = pred[at]
                path.append(at)
            path.reverse()
            for s, t in zip(path, path[1:]):
                if levels[t] < levels[s]:
                    decreasing_prefix = [s, t, levels[s], levels[t]]
    assert len(set(terminal)) == len(terminal)
    heads = sorted(apery+[x+m for x in terminal])
    top = max(order[x] for x in heads)
    nu = max(order[x] for x in apery)
    a = sum(order[x] == 2 for x in apery)
    h = [0]*(top+4)
    for x in apery:
        for t in range(max(order[x]-1, 0)):
            h[t] += 1
    for x in terminal:
        for t in range(order[x], order[x+m]-1):
            h[t] += 1
    alive = lambda s, x: x in apery or order[x]-order[x-m] > s-1
    for t in range(len(h)):
        direct = sum(alive(s, x) and order[x] == s+t
                     for s in range(2, nu+1) for x in heads)
        assert h[t] == direct
        residues = [x % m for x in heads if any(alive(s, x) and order[x] == s+t for s in range(2, nu+1))]
        assert len(residues) == len(set(residues))
        assert not residues or 0 not in residues
        assert h[t] <= m-1
    ell = sum(order[x] == 1 for x in terminal)
    assert h[0] == deficit
    assert h[1]+a == deficit+ell and ell <= e-1
    assert h[1]+a <= m-1
    mass = sum(h)
    assert mass == sum(max(x-1, 0) for x in levels)
    volume = Fraction(e)+Fraction(deficit, 2)-Fraction(3, 2)
    assert mass <= deficit*volume
    maximal = a == choose(e, 2)
    if maximal:
        low = [0]+nonx
        pair_residues = {}
        for i, x in enumerate(low):
            for j, y in enumerate(low[i:], i):
                z = x+y
                assert z == apery[z % m]
                assert z % m not in pair_residues
                pair_residues[z % m] = (i, j)
        assert m >= e*(e-1)+1 and deficit >= (e-1)**2
    cut_data = None
    action_checks = 0
    if e >= 3:
        n = e-1
        quadratic = [x for x in heads if order[x] == 2]
        assert len(quadratic) == a
        qi = {x: j for j, x in enumerate(quadratic)}
        def mu(v, w):
            result = [0]*a
            for i, x in enumerate(nonx):
                for j, y in enumerate(nonx):
                    row = qi.get(x+y)
                    if row is not None:
                        result[row] ^= MUL[v[i]][w[j]]
            return result
        forms, p, prefix = green_cut(n, a, mu)
        r = max(2, p)
        assert len(forms) == r <= e-1 and h[1] <= r*deficit
        if r >= 3:
            assert choose(r+1, 2) <= a
            assert h[1] <= m-1-choose(r+1, 2)
        for j in range(1, r+1):
            row = Fraction(0)
            for t, count in enumerate(h):
                if j == 1:
                    weight = Fraction(r-1) if t == 0 else Fraction(r+1, 2) if t == 1 else Fraction(r-1, t+1)
                else:
                    weight = Fraction(choose(r-1, j)) if t == 0 else Fraction(j*choose(r-1, j), t+j)+Fraction((j-1)*choose(r-1, j-1), t+j-2)
                row += weight*count
            lower = (e-1)*choose(r-1, j)-choose(r-1, j+1)
            target = (e-r+j)*choose(deficit+r-1, j)+j*choose(deficit+r-1, j+1)
            assert lower+row <= target
        head_set = set(heads)
        def action(form, x, available):
            out = {}
            for coefficient, g in zip(form, nonx):
                y = x+g
                if coefficient and y in head_set and y in available and order[y] == order[x]+1:
                    out[y] = out.get(y, 0) ^ coefficient
            return {x: c for x, c in out.items() if c}
        for s in range(1, nu+2):
            stage = [x for x in heads if alive(s, x)]
            next_stage = [x for x in heads if alive(s+1, x)]
            kernel = set(stage)-set(next_stage)
            assert all(order[x] >= s+1 for x in kernel)
            for degree in range(1, top+1):
                source = [x for x in stage if order[x] == degree]
                target = [x for x in stage if order[x] == degree+1]
                columns = []
                for form in forms:
                    for x in source:
                        v = action(form, x, set(stage))
                        columns.append([v.get(y, 0) for y in target])
                        if x in kernel:
                            assert set(v) <= kernel
                        else:
                            assert {y: c for y, c in v.items() if y in next_stage} == action(form, x, set(next_stage))
                        action_checks += 1
                assert rank_cols(columns, len(target)) == len(target)
            mlabels = [x for x in stage if order[x] >= s+1]
            xnext = [x for x in next_stage if order[x] >= s+1]
            assert len(mlabels) == len(kernel)+len(xnext)
        cut_data = dict(rank=r, green_prefix_dimensions=prefix, maximal_cut_without_maximal_Q2=r == e-1 and not maximal)
    return dict(atoms=atoms, multiplicity=m, deficit=deficit, q2=a, top=nu,
                terminal_count=len(terminal), resources=h, mass=mass,
                sharp_volume_equality=mass == deficit*volume,
                offset_level_decrease=decreasing_prefix, maximal_Q2=maximal,
                cut=cut_data, action_checks=action_checks)


def run():
    for a, b, c in product(range(16), repeat=3):
        assert MUL[a][b ^ c] == MUL[a][b] ^ MUL[a][c]
        assert MUL[a][MUL[b][c]] == MUL[MUL[a][b]][c]
    groups = {(1,), (6, 7, 11), (8, 9, 11), (13, 14, 17, 19), (9, 10, 15, 26), (5, 6, 13)}
    for m in range(2, 26):
        groups.add(tuple(range(m, 2*m)))
    rng = random.Random(20261110)
    for _ in range(480):
        m = rng.randrange(3, 26)
        tail = sorted(rng.sample(range(m+1, 3*m+1), rng.randrange(2, min(m, 6))))
        if gcd(m, *tail) == 1:
            groups.add((m, *tail))
    records, seen = [], set()
    for group in sorted(groups):
        result = model(group)
        key = tuple(result['atoms'])
        if key not in seen:
            records.append(result)
            seen.add(key)
    assert any(x['cut'] and x['cut']['maximal_cut_without_maximal_Q2'] for x in records)
    assert any(x['multiplicity'] % 2 == 0 and x['maximal_Q2'] and len(x['atoms']) >= 3 for x in records)
    assert any(x['cut'] and x['cut']['rank'] >= 3 and x['maximal_Q2'] for x in records)
    summary = dict(status='PASS', semigroups=len(records), characteristic=2, field='GF(16)',
                   same_cut_tower_action_checks=sum(x['action_checks'] for x in records),
                   nonzero_terminal_models=sum(x['terminal_count'] > 0 for x in records),
                   nonzero_tail_models=sum(any(x['resources'][2:]) for x in records),
                   nontrivial_volume_equalities=sum(x['deficit'] > 0 and x['sharp_volume_equality'] for x in records),
                   maximal_quadratic_models=sum(x['maximal_Q2'] for x in records),
                   level_decrease_models=sum(x['offset_level_decrease'] is not None for x in records),
                   records=records)
    Path(__file__).with_name('finite_models.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'records'}, indent=2))


if __name__ == '__main__':
    run()
