#!/usr/bin/env python3
"""Exact sanity checks for INCREMENT_LEMMA_AUDIT.md; no third-party packages."""

from fractions import Fraction
from math import comb


def digit_k(e: int, d: int, m: int) -> int:
    """The lowest digit in the degree-d binomial expansion of rank m - 1."""
    if comb(e + d - 1, d) < m:
        return 0
    remainder = m - 1
    upper = e + d - 2
    for q in range(d, 0, -1):
        lo, hi = q - 1, upper
        while lo < hi:
            middle = (lo + hi + 1) // 2
            if comb(middle, q) <= remainder:
                lo = middle
            else:
                hi = middle - 1
        remainder -= comb(lo, q)
        upper = lo - 1
        if q == 1:
            assert remainder == 0
            return lo
        if remainder == 0:
            return 0
    raise AssertionError("Unreachable")


def lex_k(e: int, d: int, m: int) -> int:
    """Unrank directly by successive X_1, ..., X_e exponent blocks."""
    if comb(e + d - 1, d) < m:
        return 0
    degree, rank, last_used = d, m, 0
    for variable in range(1, e):
        remaining_variables = e - variable
        for exponent in range(degree + 1):
            block = comb(degree - exponent + remaining_variables - 1,
                         remaining_variables - 1)
            if rank > block:
                rank -= block
            else:
                if exponent:
                    last_used = variable
                degree -= exponent
                break
        else:
            raise AssertionError("Rank not found")
    if degree:
        last_used = e
    assert rank == 1
    return e - last_used


def main() -> None:
    coefficient = sum((Fraction(1, comb(r + 2, 3)) for r in range(2, 9)),
                      Fraction())
    constant = sum((Fraction(comb(r + 2, 3) - comb(r + 2, 2),
                             comb(r + 2, 3)) for r in range(2, 9)),
                   Fraction())
    assert coefficient == Fraction(7, 15)
    assert constant == Fraction(517, 280)
    assert constant - Fraction(3, 2) == Fraction(97, 280)
    assert Fraction(11, 30) > Fraction(97, 280)

    cases = degrees = 0
    tightest_slack = None
    for e in range(5, 10):
        for m in range(e + 10, 121):
            delta = 0
            for d in range(2, m - 1):
                k = lex_k(e, d, m)
                assert k == digit_k(e, d, m), (e, d, m, k)
                if k:
                    assert m >= 2 * d + 1, (e, d, m, k)
                for r in range(2, k + 1):
                    assert comb(d + r, r) <= m, (e, d, m, k, r)
                delta += k
                degrees += 1
            assert delta <= Fraction(29 * m, 30) + Fraction(97, 280)
            assert delta <= m - 1
            slack = (m - delta, e, m, delta)
            tightest_slack = min(tightest_slack, slack) if tightest_slack else slack
            cases += 1
    print(f"Exact rational identities: passed")
    print(f"Independent unranking agreement: {degrees} degree cases")
    print(f"Increment checks: {cases} (e,m) cases; all passed")
    print(f"Smallest m - delta: {tightest_slack}")


if __name__ == "__main__":
    main()
