#!/usr/bin/env python3
"""Exact algebra checks for WIDTH_SEARCH.md; no source-core enumeration.

Uses SymPy, already installed in this workspace. These identities supplement
the paper arguments in the report; they are not a replacement for them.
"""

from fractions import Fraction
from math import comb

import sympy as sp


def choose(n: int, k: int) -> int:
    return comb(n, k) if 0 <= k <= n else 0


u, z, e, q, P, h2 = sp.symbols("u z e q P h2")

# C(5.1), retaining h_2 and replacing the n >= 3 weights by (q-1)/4.
incidence = (
    q + (q - 1) * q / 2 + (q - 1) * h2 / 3
    + (q - 1) * (P - 1 - q - h2) / 4
)
incidence_bound = (q - 1) * P / 4 + (q + 1) * (q + 2) * (q + 3) / 24
assert sp.expand(
    incidence.subs(h2, q * (q + 1) / 2) - incidence_bound
) == 0
assert sp.expand(sp.diff(incidence, h2) - (q - 1) / 12) == 0

expected = {
    6: z**2 / 24 + 43 * z / 24 + sp.Rational(1, 2),
    7: 2 * z + 1,
    8: 3 * z**2 / 32 + 63 * z / 16 + sp.Rational(211, 32),
    9: z**2 / 16 + 17 * z / 4 + sp.Rational(29, 4),
}
target = u * (u - 1) / 2 + 1
for embedding_dimension, expected_gap in expected.items():
    s = embedding_dimension // 2
    a = embedding_dimension - 1
    B_cap = (
        u + (u - a)**2 / sp.Integer(2 * s)
        + (u - a) / 2 + sp.Rational((s * s) // 4, 2 * s)
    )
    U1 = (
        sp.Rational(embedding_dimension + 5, 4) * B_cap - u
        + sp.Rational(
            (embedding_dimension - 1) * embedding_dimension
            * (embedding_dimension + 1), 24
        )
    )
    gap = sp.expand((target - U1).subs(u, 2 * embedding_dimension - 2 + z))
    assert sp.expand(gap - expected_gap) == 0
    assert all(coefficient >= 0 for coefficient in sp.Poly(gap, z).all_coeffs())
    assert gap.subs(z, 0) > 0
    print(f"e={embedding_dimension}: B_cap={sp.factor(B_cap)}; gap={gap}")

# Generic e >= 10 identity. Multiplication removes every denominator first.
old_U1 = (e + 3) * u**2 / (3 * (e - 1)) - u + e * (e - 1) / 6
generic_gap = (
    (e - 1) * (e - 10) / 2 + 1
    + (4 * e - 33) * z / 6
    + (e - 9) * z**2 / (6 * (e - 1))
)
assert sp.expand(sp.cancel(
    6 * (e - 1)
    * ((target - old_U1).subs(u, 2 * e - 2 + z) - generic_gap)
)) == 0
print("e>=10: generic gap identity verified exactly")

# The optional q=3 small-width replacement uses only these four upper bounds.
for width, length_cap, socle_cap in ((6, 8, 0), (7, 10, 3)):
    uppers = (
        5 * length_cap + 4 * socle_cap,
        4 * length_cap + 6 * socle_cap - 1,
        length_cap + 4 * socle_cap,
        socle_cap,
    )
    capacities = tuple(
        i * choose(width, i + 1)
        + min(choose(width, i - 1), choose(width, i))
        for i in range(2, 6)
    )
    assert all(upper <= capacity for upper, capacity in zip(uppers, capacities))
    print(f"q=3,u={width}: rows 2..5 upper={uppers}; capacity={capacities}")

assert Fraction(2, 3) * 8 + Fraction(10, 3) < 9
assert 6 + Fraction(2, 3) * 6 - Fraction(1, 6) < 10
print("All exact identity and capacity checks passed.")
