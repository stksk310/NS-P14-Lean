#!/usr/bin/env python3
"""Independent exact R27-A01 finite proof component.

No author checker import and no congruence candidate list.  Core membership is
decided directly in each degree/offset fiber by a shortest-word dynamic program.
The paper proof of the finite bounds and the all-m estimate accompanies this
file in PRIMITIVE_FIRST_ROW_AUDIT_JA.md.
"""

from hashlib import sha256
from math import gcd
from pathlib import Path
import gzip
import json


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def divides(left, right):
    return all(x <= y for x, y in zip(left, right))


def minima(monomials):
    result = []
    for item in sorted(set(monomials), key=lambda e: (sum(e), e)):
        if not any(divides(old, item) for old in result):
            result.append(item)
    return result


def calculate(a, b, w):
    p = min(b // gcd(a, b), w // gcd(a, w))
    q = min((w - a) // gcd(w - a, w - b), w // gcd(b, w))
    limit = a * p + b * q
    infinity = limit + 1
    shortest = [infinity] * (limit + 1)
    shortest[0] = 0
    for n in range(1, limit + 1):
        shortest[n] = min(
            (shortest[n - c] + 1 for c in (a, b, w) if c <= n),
            default=infinity,
        )

    def endpoint_with_v(n):
        return shortest[n - w] + 1 if n >= w else infinity

    def internal_forbidden(s, t):
        d, n = s + t, a * s + b * t
        return shortest[n] < d or endpoint_with_v(n) <= d

    # A pure internal monomial is nonstandard iff its fiber has a word with x
    # or v.  At fixed degree/offset two pure internal words must coincide.
    candidates = [
        (0, s, t)
        for s in range(p + 1)
        for t in range(q + 1)
        if internal_forbidden(s, t)
    ]
    # For x^X z^t, a competing no-v word has positive y exponent and is larger
    # in lex, so it cannot be the normal form.  Exactly a word using v can be
    # smaller.  Its least total length is 1+shortest(bt-w).
    for t in range(1, q):
        least = endpoint_with_v(b * t)
        if least < infinity:
            candidates.append((max(0, least - t), 0, t))
    core = minima(candidates)
    p0 = min(s for X, s, t in core if X == 0 and t == 0)
    q0 = min(t for X, s, t in core if X == 0 and s == 0)
    D = [
        (s, t)
        for s in range(p)
        for t in range(q)
        if not internal_forbidden(s, t)
    ]
    require(
        all(
            internal_forbidden(s, t)
            == any(divides(g, (0, s, t)) for g in core)
            for s in range(p + 1)
            for t in range(q + 1)
        ),
        "core and direct internal fiber membership disagree",
    )
    B, K0 = len(D), len(core)
    M = max((w - a) * s + (w - b) * t for s, t in D)
    A0 = max(0, (M - 2 * w - 1) // w)
    Ly = sum(max(0, (r * (w - a) - 2 * w + b) // (2 * w + 1))
             for r in range(1, p0))
    Lz = sum(max(0, (r * (w - b) - 2 * w + a) // (2 * w + 1))
             for r in range(1, q0))
    U = K0 + B + q0 - 1 + A0 + Ly + Lz
    capacity = w * (w - 1) // 2 + 1
    require(2 <= p0 <= p <= w - 1 and 2 <= q0 <= q <= w - 1,
            "pure power bounds")
    require(all(s + t <= w // 2 for s, t in D if s and t),
            "mixed degree bound")
    require(all(s + t <= w - 2 for s, t in D), "internal degree bound")
    require(B <= (w // 2) * (w // 2 - 1) // 2 + p0 + q0 - 1,
            "basis count")
    require(K0 <= 2 * q0, "core generator bound")
    require(4 * (Ly + Lz) <= w * w, "triple-support count")
    return dict(a=a, b=b, w=w, p=p, q=q, p0=p0, q0=q0,
                core=core, D=D, B=B, K0=K0, M=M, A0=A0,
                Ly=Ly, Lz=Lz, U=U, capacity=capacity, slack=capacity-U)


def main():
    rows, exceptions, by_width = [], [], []
    for w in range(3, 48):
        local = []
        for a in range(1, w - 1):
            for b in range(a + 1, w):
                if gcd(gcd(a, b), w) != 1:
                    continue
                row = calculate(a, b, w)
                rows.append(row)
                local.append(row)
                if row['slack'] < 0:
                    exceptions.append([a, b, w])
        worst = min(local, key=lambda r: r['slack'])
        by_width.append(dict(w=w, count=len(local), min_slack=worst['slack'],
                             worst=[worst['a'], worst['b']],
                             U=worst['U'], capacity=worst['capacity']))
    require(len(rows) == 13921, "offset count")
    require(exceptions == [[1, w-1, w] for w in range(3, 11)],
            "exception list")
    # Direct integer calculation of each width count, independent of the
    # enumeration filter, by Mobius inversion on common divisors.
    def mobius(d):
        factors, p = 0, 2
        while p * p <= d:
            if d % p == 0:
                d //= p
                if d % p == 0:
                    return 0
                factors += 1
            while d % p == 0:
                d //= p
            p += 1
        return (-1) ** (factors + (d > 1))
    for row in by_width:
        w = row['w']
        count = sum(mobius(d) * ((w // d - 1) * (w // d - 2) // 2)
                    for d in range(1, w + 1) if w % d == 0)
        require(row['count'] == count, "Mobius width count")
    payload = dict(schema='N4_PRIMITIVE_FIRST_DIRECT_FIBER_V1',
                   offset_count=len(rows), exceptions=exceptions,
                   by_width=by_width, rows=rows,
                   interpretation='Exact finite evaluation of proved all-m U; no finite m extrapolation.')
    normalized = json.dumps(payload, ensure_ascii=False, sort_keys=True,
                            separators=(',', ':')).encode()
    output = Path(__file__).with_name('independent_offset_certificate.json.gz')
    encoded = json.dumps(dict(payload=payload, sha256=sha256(normalized).hexdigest()),
                         ensure_ascii=False, separators=(',', ':')).encode()
    output.write_bytes(gzip.compress(encoded, mtime=0))
    print(json.dumps(dict(offset_count=len(rows), exceptions=exceptions,
                          by_width=by_width,
                          certificate_sha256=sha256(normalized).hexdigest()),
                     ensure_ascii=False))


if __name__ == '__main__':
    main()
