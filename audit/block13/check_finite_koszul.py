#!/usr/bin/env python3
"""Independent exterior-basis matrices, Gaussian homology and actual connecting ranks.

Finite experiments supplement, and do not replace, the Lean proofs. No project
matrix implementation or submitted numerical output is imported.
"""
from itertools import combinations, product
from math import comb
from pathlib import Path
import json


def rref(a, cols, p):
    a = [[x % p for x in row] for row in a]
    pivots, r = [], 0
    for c in range(cols):
        s = next((s for s in range(r, len(a)) if a[s][c]), None)
        if s is None:
            continue
        a[r], a[s] = a[s], a[r]
        inv = pow(a[r][c], -1, p)
        a[r] = [x*inv % p for x in a[r]]
        for j in range(len(a)):
            if j != r:
                t = a[j][c]
                a[j] = [(x-t*y) % p for x, y in zip(a[j], a[r])]
        pivots.append(c)
        r += 1
        if r == len(a):
            break
    return a, pivots


def rank(a, cols, p):
    return len(rref(a, cols, p)[1])


def kernel(a, cols, p):
    reduced, pivots = rref(a, cols, p)
    out = []
    for c in range(cols):
        if c not in pivots:
            v = [0]*cols
            v[c] = 1
            for row, pivot in enumerate(pivots):
                v[pivot] = -reduced[row][c] % p
            out.append(v)
    return out


def labels(n, basis, i):
    return [(w, m) for w in combinations(range(n), i) for m in basis]


def differential(n, basis, i):
    source = labels(n, basis, i)
    target = labels(n, basis, i-1) if i else []
    idx = {x: j for j, x in enumerate(target)}
    out = [[0]*len(source) for _ in target]
    for c, (w, m) in enumerate(source):
        for j, x in enumerate(w):
            exponent = tuple(v+(t == x) for t, v in enumerate(m))
            row = idx.get((w[:j]+w[j+1:], exponent))
            if row is not None:
                out[row][c] += (-1)**j
    return out


def betti(n, basis, p):
    ds = [differential(n, basis, i) for i in range(n+2)]
    dims = [len(labels(n, basis, i)) for i in range(n+2)]
    ranks = [rank(d, dims[i], p) for i, d in enumerate(ds)]
    for i in range(2, n+2):
        for row in ds[i-1]:
            for col in range(dims[i]):
                assert sum(row[j]*ds[i][j][col] for j in range(dims[i-1])) % p == 0
    b = [dims[i]-ranks[i]-ranks[i+1] for i in range(n+1)]
    assert all(x >= 0 for x in b)
    assert b[0] == 1
    assert sum((-1)**i*x for i, x in enumerate(b)) == (1 if n == 0 else 0)
    socle = sum(all(tuple(v+(j == x) for j, v in enumerate(m)) not in basis
                    for x in range(n)) for m in basis)
    assert b[n] == socle
    return b


def mul4(a, b):
    out = 0
    while b:
        if b & 1:
            out ^= a
        a <<= 1
        if a & 4:
            a ^= 7  # t²+t+1
        b >>= 1
    return out


def rank4(matrix, cols):
    a = [row[:] for row in matrix]
    r = 0
    for c in range(cols):
        s = next((s for s in range(r, len(a)) if a[s][c]), None)
        if s is None:
            continue
        a[r], a[s] = a[s], a[r]
        inv = next(t for t in range(1, 4) if mul4(a[r][c], t) == 1)
        a[r] = [mul4(x, inv) for x in a[r]]
        for j in range(len(a)):
            if j != r:
                t = a[j][c]
                a[j] = [x ^ mul4(t, y) for x, y in zip(a[j], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def connecting(n, b_basis, a_basis, p):
    """For 0→A→B→C→0, lift actual cycles in C and differentiate in B."""
    c_basis = sorted(set(b_basis)-set(a_basis))
    delta = [0]*(n+1)
    for i in range(1, n+1):
        al = labels(n, a_basis, i-1)
        bl = labels(n, b_basis, i)
        cl = labels(n, c_basis, i)
        bt = labels(n, b_basis, i-1)
        bi = {x: j for j, x in enumerate(bl)}
        ai = {x: j for j, x in enumerate(al)}
        db = differential(n, b_basis, i)
        dc = differential(n, c_basis, i)
        images = []
        for z in kernel(dc, len(cl), p):
            lift = [0]*len(bl)
            for j, label in enumerate(cl):
                lift[bi[label]] = z[j]
            dz = [sum(v*w for v, w in zip(row, lift)) % p for row in db]
            image = [0]*len(al)
            for label, value in zip(bt, dz):
                if label not in ai:
                    assert value == 0
                else:
                    image[ai[label]] = value
            images.append(image)
        da = differential(n, a_basis, i)
        boundary_cols = len(labels(n, a_basis, i))
        combined = [row+[v[j] for v in images] for j, row in enumerate(da)]
        delta[i] = rank(combined, boundary_cols+len(images), p)-rank(da, boundary_cols, p)
    ba, bb, bc = (betti(n, basis, p) for basis in (a_basis, b_basis, c_basis))
    # A is a submodule with shifted generators, so its H0 need not be one.
    return ba, bb, bc, delta


def run():
    for a, b, c in product(range(4), repeat=3):
        assert mul4(a, b ^ c) == (mul4(a, b) ^ mul4(a, c))
        assert mul4(a, mul4(b, c)) == mul4(mul4(a, b), c)
    for a in range(1, 4):
        assert any(mul4(a, b) == 1 for b in range(1, 4))
    records = []
    for n in range(4):
        box = list(product(range(2), repeat=n))
        for mask in range(1, 1 << len(box)):
            basis = [x for j, x in enumerate(box) if mask >> j & 1]
            if any(any(all(x <= y for x, y in zip(a, b)) and a not in basis for a in box)
                   for b in basis):
                continue
            fields = {}
            for p in (2, 3, 5, 7):
                fields[str(p)] = betti(n, basis, p)
            for i in range(n+2):
                d = differential(n, basis, i)
                cols = len(labels(n, basis, i))
                extended = [[x % 2 for x in row] for row in d]
                # Non-prime-field basis scalars exercise genuine GF(4) arithmetic.
                scaled = [[mul4(mul4(x, 1+j % 3), 1+c % 3)
                           for c, x in enumerate(row)] for j, row in enumerate(extended)]
                assert rank4(extended, cols) == rank4(scaled, cols) == rank(d, cols, 2)
            records.append(dict(n=n, basis=basis, betti=fields))
    for n in range(1, 4):
        basis = list(product(range(3), repeat=n))
        for p in (2, 3, 5, 7):
            assert betti(n, basis, p) == [comb(n, i) for i in range(n+1)]
    assert betti(2, [(0, 0), (1, 0), (0, 1)], 2) == [1, 3, 2]
    assert betti(2, [(0, 0), (1, 0), (0, 1), (0, 2)], 2) == [1, 3, 2]
    sequences = []
    for n in (1, 2, 3):
        basis = list(product(range(2), repeat=n))
        socle = [(1,)*n]
        for p in (2, 3, 5, 7):
            ba, bb, bc, delta = connecting(n, basis, socle, p)
            for i in range(n+1):
                incoming = delta[i+1] if i < n else 0
                assert bb[i]+delta[i]+incoming == ba[i]+bc[i]
            assert delta[1] > 0
            sequences.append(dict(n=n, characteristic=p, beta_A=ba, beta_B=bb,
                                  beta_C=bc, delta_from_degree=delta))
    result = dict(status='PASS', coefficient_fields=[2, 3, 5, 7],
                  scalar_extension='GF(2) -> GF(4), all tested differentials',
                  downset_quotients=len(records), complete_intersections=12,
                  short_exact_sequences=sequences, quotient_results=records)
    Path(__file__).with_name('finite_koszul.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'quotient_results'}, indent=2))


if __name__ == '__main__':
    run()
