#!/usr/bin/env python3
"""Exact offset certificate for the proposed shorter N4 proof.

Standard library only; imports no historical checker or certificate.  This
evaluates a proved all-m endpoint bound, not a finite multiplicity sample.
See ../N4_SEARCH.md for every universal step and the two retained exceptions.
"""

from collections import deque
from itertools import combinations
from math import comb, gcd
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def offset_invariants(a, b, w):
    # Exact homogeneous fibers: degree d contains precisely these offsets.
    reachable = [{0}]
    for degree in range(1, w):
        reachable.append({n + step for n in reachable[-1]
                          for step in (0, a, b, w)})
    standard = set()
    for degree in range(w):
        for s in range(degree + 1):
            t = degree - s
            n = a*s + b*t
            endpoint = degree and (n in reachable[degree - 1]
                                  or n-w in reachable[degree - 1])
            if not endpoint:
                require(degree <= w-2, "proved internal-word cutoff")
                standard.add((s, t))
    require(all(s == 0 or (s-1, t) in standard for s, t in standard),
            "y divisor closure")
    require(all(t == 0 or (s, t-1) in standard for s, t in standard),
            "z divisor closure")
    P = len(standard)
    sigma = sum((s+1, t) not in standard and (s, t+1) not in standard
                for s, t in standard)
    Hx = max(s+t-(a*s+b*t)//w-int((a*s+b*t) % w > 0)
             for s, t in standard)

    # Breadth-first search gives the shortest internal word in every residue.
    lengths = [None]*w
    lengths[0] = 0
    queue = deque([0])
    while queue:
        r = queue.popleft()
        for step in (a, b):
            dest = (r+step) % w
            if lengths[dest] is None:
                lengths[dest] = lengths[r]+1
                queue.append(dest)
    require(all(value is not None for value in lengths), "primitive reachability")
    W = 1+sum(lengths)
    Rhat = min(W-w, w*max(Hx-2, 0))
    U1 = P+sigma+1+Rhat
    capacity = comb(w, 2)+1

    # These are consistency checks of independently proved general lemmas.
    h = w//2
    require(W <= 1+w*w//4, "Kneser distance-sum bound")
    require(P <= W, "endpoint generator count")
    require(P <= comb(h, 2)+2*w-3, "Savchev-Chen standard-word count")
    require(comb(sigma+1, 2) <= P, "two-variable antichain bound")
    require(sigma <= h+2, "derived socle bound")
    require(all(s+t <= h for s, t in standard if s and t),
            "mixed standard-word bound")
    return dict(a=a, b=b, w=w, P_C=P, sigma_C=sigma, Hx=Hx,
                W=W, Rhat=Rhat, U1=U1, F1_min=capacity,
                slack=capacity-U1)


def multiply(left, right):
    result = [0]*(len(left)+len(right)-1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i+j] += a*b
    return result


def shifted_polynomial(coefficients, shift):
    result = [0]*len(coefficients)
    power = [1]
    for coefficient in coefficients:
        for i, value in enumerate(power):
            result[i] += coefficient*value
        power = multiply(power, [shift, 1])
    return result


def main():
    rows, by_width = [], []
    for w in range(3, 13):
        local = [offset_invariants(a, b, w)
                 for a, b in combinations(range(1, w), 2)
                 if gcd(gcd(a, b), w) == 1]
        rows.extend(local)
        worst = min(local, key=lambda row: row['slack'])
        by_width.append(dict(w=w, count=len(local),
                             min_slack=worst['slack'],
                             worst=[worst['a'], worst['b']]))
    failures = [[row['w'], row['a'], row['b']]
                for row in rows if row['slack'] < 0]
    require(len(rows) == 196, "finite offset count")
    require(failures == [[3, 1, 2], [4, 1, 3]], "exact exception list")

    # Exact identities, coefficients in increasing powers of z.
    identities = {
        '12*(F2_lower-U2_upper), w=6+z':
            shifted_polynomial([-48, 44, -27, 4], 6),
        '8*(F3_lower-U3_upper), w=5+z':
            shifted_polynomial([-32, 14, 7, -6, 1], 5),
        '60*(F4_lower-U4_upper), w=5+z':
            shifted_polynomial([-60, 108, -115, 70, -20, 2], 5),
    }
    require(identities['12*(F2_lower-U2_upper), w=6+z']
            == [108, 152, 45, 4], "second-row polynomial")
    require(identities['8*(F3_lower-U3_upper), w=5+z']
            == [88, 134, 67, 14, 1], "third-row polynomial")
    require(all(value > 0 for values in identities.values() for value in values),
            "all higher-row gap coefficients positive")

    result = dict(schema='SHORTER_N4_SEARCH_V1', offset_count=len(rows),
                  finite_widths=[3, 12], multiplicities_enumerated=0,
                  higher_row_finite_points=0, higher_row_tail_certificates=0,
                  exceptions=failures, by_width=by_width,
                  polynomial_coefficients=identities, rows=rows,
                  qualification='Exact finite evaluation of a proved all-m bound; '
                                'universal arguments are in N4_SEARCH.md.')
    destination = Path(__file__).with_name('SHORTER_N4_CERTIFICATE.json')
    destination.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'rows'},
                     ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
