#!/usr/bin/env python3
"""Independent finite EH checks using actual semigroup-order Koszul matrices.

No production Python/Lean coordinate routine is imported. These are finite
cross-checks, not a substitute for the universal Lean proofs.
"""
from collections import deque
from fractions import Fraction
from itertools import combinations
from math import comb, gcd
from pathlib import Path
import hashlib
import json

PRIMES = [2, 3, 101]


def choose(n, i):
    return comb(n, i) if 0 <= i <= n else 0


def rank(columns, prime):
    pivots = {}
    for col in columns:
        col = {i: v % prime for i, v in col.items() if v % prime}
        while col:
            pivot = min(col)
            if pivot not in pivots:
                inv = pow(col[pivot], -1, prime)
                pivots[pivot] = {i: v*inv % prime for i, v in col.items()}
                break
            c = col[pivot]
            for i, v in pivots[pivot].items():
                col[i] = (col.get(i, 0)-c*v) % prime
                if not col[i]:
                    del col[i]
    return len(pivots)


def minima(points):
    points = sorted(set(points))
    out, lowest = [], float('inf')
    for a, b in points:
        if b < lowest:
            out.append((a, b))
            lowest = b
    return out


def above(point, generators):
    return any(a <= point[0] and b <= point[1] for a, b in generators)


def order_table(atoms, limit):
    order = [-1]*(limit+1)
    order[0] = 0
    for h in range(1, limit+1):
        candidates = [order[h-g]+1 for g in atoms if h >= g and order[h-g] >= 0]
        if candidates:
            order[h] = max(candidates)
    return order


def full_tangent_betti(atoms, order):
    """Compute all rows by numerical-weight blocks of the actual full Koszul.

    A finite interval of length max(atoms) certifies eventual x-order
    stability by induction in the max-plus decomposition recurrence. Beyond
    N+sum(atoms), the x pairing contracts each numerical-weight complex.
    """
    m, largest = atoms[0], max(atoms)
    last_bad = max(h for h in range(len(order)-m)
                   if order[h] < 0 or order[h+m] != order[h]+1)
    start = last_bad+1
    assert start+largest+m < len(order)
    assert all(order[h] >= 0 and order[h+m] == order[h]+1
               for h in range(start, start+largest))
    bound = start+sum(atoms)
    assert bound+largest < len(order)
    e = len(atoms)
    # Verify commutation of actual degree-one actions before interpreting
    # the signed matrices as a Koszul complex.
    for h in range(bound+1):
        if order[h] < 0:
            continue
        for a in atoms:
            for b in atoms:
                if h+a+b < len(order):
                    left = order[h+a] == order[h]+1 and order[h+a+b] == order[h]+2
                    right = order[h+b] == order[h]+1 and order[h+a+b] == order[h]+2
                    assert left == right
    wedges = [list(combinations(range(e), i)) for i in range(e+1)]
    sums = {w: sum(atoms[j] for j in w) for row in wedges for w in row}
    betti = {p: [0]*(e+1) for p in PRIMES}
    for weight in range(bound+1):
        basis = [[w for w in row if weight >= sums[w] and order[weight-sums[w]] >= 0]
                 for row in wedges]
        ranks = {p: [0]*(e+2) for p in PRIMES}
        for i in range(1, e+1):
            rows = {w: j for j, w in enumerate(basis[i-1])}
            columns = []
            for w in basis[i]:
                h = weight-sums[w]
                col = {}
                for pos, j in enumerate(w):
                    if order[h+atoms[j]] == order[h]+1:
                        col[rows[w[:pos]+w[pos+1:]]] = (-1)**pos
                columns.append(col)
            for p in PRIMES:
                ranks[p][i] = rank(columns, p)
        for p in PRIMES:
            for i in range(e+1):
                dim = len(basis[i])-ranks[p][i]-ranks[p][i+1]
                assert dim >= 0
                betti[p][i] += dim
    assert all(b[0] == 1 for b in betti.values())
    return betti, start, bound


def finite_core_betti(basis, internal):
    idx = {point: i for i, point in enumerate(basis)}
    q, size = len(internal), len(basis)
    action = {(i, j): idx.get((n+1, b+a))
              for i, (n, b) in enumerate(basis) for j, a in enumerate(internal)}
    for i in range(size):
        for j in range(q):
            for k in range(q):
                a, b = action[i, j], action[i, k]
                assert (None if a is None else action[a, k]) == (
                    None if b is None else action[b, j])
    ranks = {p: [0]*(q+2) for p in PRIMES}
    for degree in range(1, q+1):
        source = list(combinations(range(q), degree))
        target = list(combinations(range(q), degree-1))
        rows = {w: i for i, w in enumerate(target)}
        columns = []
        for w in source:
            for i in range(size):
                col = {}
                for pos, j in enumerate(w):
                    dest = action[i, j]
                    if dest is not None:
                        col[rows[w[:pos]+w[pos+1:]]*size+dest] = (-1)**pos
                columns.append(col)
        for p in PRIMES:
            ranks[p][degree] = rank(columns, p)
    betti = {p: [size*choose(q, i)-ranks[p][i]-ranks[p][i+1] for i in range(q+1)]
             for p in PRIMES}
    sigma = sum(all(action[i, j] is None for j in range(q)) for i in range(size))
    return betti, sigma


def check(m, d, internal, u):
    assert len(internal) >= 2 and 0 < min(internal) < max(internal) < u < m
    assert gcd(m, d) == gcd(gcd(*internal), u) == 1
    offsets = [0, *internal, u]
    atoms = [m+d*a for a in offsets]
    lmax, kmax = u+1, m+u+2
    numeric_limit = max(4*m*max(atoms),
                        (lmax+kmax+1)*m+d*(u*kmax+u-1))+sum(atoms)+max(atoms)
    order = order_table(atoms, numeric_limit)
    assert all(order[g] == 1 for g in atoms)
    # Enumerate the literal degree/offset monoid, including endpoints.
    sums = [{0}]
    for _ in range(lmax+kmax+3):
        sums.append({b+a for b in sums[-1] for a in offsets})
    points = [[] for _ in range(u)]
    for n in range(u):
        for b in sums[n]:
            r, k = b % u, b // u
            points[r].append((n-k-int(r > 0), k))
    minimal = [minima(row) for row in points]
    assert all(row for row in minimal)
    # A finite closure certificate: the proposed E-generators are real core
    # words, contain the unit, and their E-span is closed under every
    # internal generator. Thus the enumeration is not just a guessed cutoff.
    assert minimal[0] == [(0, 0)]
    for r, row in enumerate(minimal):
        for l, k in row:
            for a in internal:
                b = r+u*k+a
                s, new_k = b % u, b // u
                new_l = l+k+int(r > 0)+1-new_k-int(s > 0)
                assert new_l >= 0 and above((new_l, new_k), minimal[s])
    assert order[m*atoms[-1]] > m
    pc = sum(map(len, minimal))
    period, start = u//gcd(m, u), (u-2)//2
    forbidden = [[] for _ in range(u)]
    for j in range(1, start+period+1):
        for r, row in enumerate(minimal):
            s, carry = (r+j*m) % u, (r+j*m)//u
            for l, k in row:
                forbidden[s].append((max(0, l-j*d-carry+int(r > 0)-int(s > 0)), k+carry))
    forbidden = [minima(row) for row in forbidden]

    def in_core(r, l, k):
        return l >= 0 and k >= 0 and r+u*k in sums[l+k+int(r > 0)]

    def live(r, l, k):
        if not in_core(r, l, k):
            return False
        n, b = l+k+int(r > 0), r+u*k
        return order[n*m+d*b] == n

    endpoint_homology = [0, 0, 0]
    tested = 0
    for r in range(u):
        for l in range(lmax+1):
            for k in range(kmax+1):
                inside = in_core(r, l, k)
                assert inside == above((l, k), minimal[r])
                if inside:
                    assert (not live(r, l, k)) == above((l, k), forbidden[r])
                    tested += 1
                c0 = int(live(r, l, k))
                c1 = int(live(r, l-1, k))+int(live(r, l, k-1))
                c2 = int(live(r, l-1, k-1))
                rank1, rank2 = int(bool(c0 and c1)), int(bool(c2 and c1))
                dims = [c0-rank1, c1-rank1-rank2, c2-rank2]
                assert all(n >= 0 for n in dims)
                if l == lmax or k == kmax:
                    assert dims == [0, 0, 0]
                endpoint_homology = [a+b for a, b in zip(endpoint_homology, dims)]
    pg, middle, socle = endpoint_homology
    assert pg == sum(live(r, l, k) for r, row in enumerate(minimal) for l, k in row)
    assert middle == pg+socle
    distance = [None]*u
    distance[0] = 0
    pending = deque([0])
    while pending:
        r = pending.popleft()
        for a in internal:
            s = (r+a) % u
            if distance[s] is None:
                distance[s] = distance[r]+1
                pending.append(s)
    volume = 1+sum(distance)
    height = max(l for row in minimal for l, k in row)
    rhat = min(volume-u, u*max(height-2, 0))
    assert pc <= volume and socle <= rhat
    core_basis = sorted((l+k+int(r > 0), r+u*k)
                        for r, row in enumerate(minimal) for l, k in row)
    core_betti, sigma = finite_core_betti(core_basis, internal)
    full_betti, stable, last_weight = full_tangent_betti(atoms, order)
    q = len(internal)
    weighted = Fraction(q)+sum(Fraction(q-1, n+1) for n, _ in core_basis if n >= 1)
    general_rows = [1, pc+int(weighted)+rhat]+[
        pc*choose(q+1, i)+rhat*choose(q+1, i-1)-choose(q+1, i+1)
        for i in range(2, q+3)]
    for p in PRIMES:
        assert all(x >= 0 for x in general_rows)
        assert all(b <= cap for b, cap in zip(full_betti[p], general_rows))
        for i, b in enumerate(full_betti[p]):
            core = core_betti[p][i] if i <= q else 0
            cap = core+(pc*choose(q, i-1)+socle*choose(q+1, i-1) if i >= 1 else 0)
            assert b <= cap
        assert full_betti[p][-1] <= socle
        if q == 2:
            assert core_betti[p] == [1, sigma+1, sigma]
            caps = [1, pc+sigma+1+socle, 2*pc+sigma+3*socle, pc+3*socle, socle]
            assert all(b <= cap for b, cap in zip(full_betti[p], caps))
    return dict(m=m, d=d, internal=internal, u=u, atoms=atoms, PC=pc, PG=pg, R=socle,
                endpoint_homology=endpoint_homology, W=volume, Hx=height, Rhat=rhat,
                sigma=sigma if q == 2 else None, kernel_points_checked=tested,
                order_stable_from=stable, full_tor_max_weight=last_weight,
                full_actual_betti=full_betti, QC_betti=core_betti)


def main():
    cases = [(6, 1, [1, 3], 4), (7, 2, [1, 3], 4), (7, 1, [1, 5], 6),
             (9, 1, [2, 3, 4], 7), (8, 1, [1, 2], 5), (8, 1, [3, 4], 5),
             (6, 1, [1, 2], 3), (9, 2, [1, 2], 3),
             (9, 1, [1, 2, 4, 5], 6)]
    for u in range(3, 7):
        for internal in combinations(range(1, u), 2):
            if gcd(gcd(*internal), u) != 1:
                continue
            for d in [1, 2]:
                m = u+2
                if gcd(m, d) == 1:
                    cases.append((m, d, list(internal), u))
    unique = list(dict.fromkeys((m, d, tuple(a), u) for m, d, a, u in cases))
    records = [check(m, d, list(a), u) for m, d, a, u in unique]
    assert [(r['PC'], r['PG'], r['R']) for r in records[:3]] == [(5, 4, 0), (5, 5, 0), (9, 6, 1)]
    result = dict(status='PASS_FINITE_ACTUAL_TOR_CROSS_CHECKS',
                  scope='Finite EH cases only; no universal proof claim.',
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  cases=len(records), field_checks=len(records)*len(PRIMES),
                  kernel_points_checked=sum(r['kernel_points_checked'] for r in records),
                  characteristics=PRIMES, records=records)
    Path(__file__).with_name('actual_tor_checks.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], result['cases'], 'EH cases;', result['field_checks'], 'field checks;',
          result['kernel_points_checked'], 'kernel points')


if __name__ == '__main__':
    main()
