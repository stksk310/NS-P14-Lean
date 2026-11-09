#!/usr/bin/env python3
"""Audit the proved structural N4 reduction; never samples m or d.

The mathematical proof is in ../UNIFORM_SEARCH.md. Existing exact core rows
are used only to cross-check the new inequalities on the old 196-row audit.
No authoritative V02 file is modified.
"""
from collections import Counter
from itertools import combinations
from math import comb, gcd
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[2]
CERTIFICATE = ROOT / 'proof_integrated_v2/certificates/n4/SHORTER_N4_CERTIFICATE.json'


def envelope_bounds(u, a, b):
    h = u // 2
    p, q = u - b, a
    k = p + q
    forbidden_mixed = comb(h - k + 2, 2) if k <= h else 0
    point_bound = 2*u-k-1+comb(h, 2)-forbidden_mixed
    uniform_point_bound = 2*u-h-2+comb(h, 2)
    socle_bound = min(h+1, k)
    assert point_bound <= uniform_point_bound
    return point_bound, uniform_point_bound, socle_bound


def covered_uniformly(u):
    h = u // 2
    pc = 2*u-h-2+comb(h, 2)
    sigma = h+1
    r = 0 if u <= 5 else 1+u*u//4-u
    bound = pc+sigma+1+r
    capacity = comb(u, 2)+1
    return bound <= capacity, bound, capacity


def main():
    old = json.loads(CERTIFICATE.read_text())
    rows = old['rows']
    assert len(rows) == 196
    for row in rows:
        u, a, b = row['w'], row['a'], row['b']
        pc_pair, pc_uniform, sigma_pair = envelope_bounds(u, a, b)
        assert row['P_C'] <= pc_pair, (row, pc_pair)
        assert row['sigma_C'] <= sigma_pair, (row, sigma_pair)
        assert row['P_C'] <= pc_uniform

    # Independent checks of the elementary integer optimization. These do
    # not replace the all-h proof of k+Q >= h+1 in the companion document.
    for h in range(1, 200):
        for k in range(2, 2*h+2):
            q = comb(h-k+2, 2) if k <= h else 0
            assert k+q >= h+1

    # Verify the two symbolic gap formulas as exact integer identities.
    for h in range(1, 200):
        for u, gap in ((2*h, h*(h-5)//2),
                       (2*h+1, (h*h-3*h-2)//2)):
            if u < 3:
                continue
            pc = 2*u-h-2+comb(h, 2)
            rhs = pc+(h+1)+1+(1+u*u//4-u)
            assert comb(u, 2)+1-rhs == gap

    eliminated = [r for r in rows if covered_uniformly(r['w'])[0]]
    residual = [r for r in rows if not covered_uniformly(r['w'])[0]]
    assert Counter(r['w'] for r in eliminated) == {5: 6, 9: 27, 10: 30, 11: 45, 12: 42}
    assert len(eliminated) == 150
    assert len(residual) == 46
    assert Counter(r['w'] for r in residual) == {3: 1, 4: 3, 6: 9, 7: 15, 8: 18}
    result = {
        'old_offset_rows': len(rows),
        'uniformly_eliminated_rows': len(eliminated),
        'remaining_offset_rows': len(residual),
        'remaining_width_counts': dict(sorted(Counter(r['w'] for r in residual).items())),
        'uniform_widths': 'u=5, all odd u>=9, all even u>=10',
        'multiplicities_enumerated': 0,
        'status': 'proved inequalities; exact old core rows used as regression checks only',
    }
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
