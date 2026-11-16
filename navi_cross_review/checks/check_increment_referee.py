#!/usr/bin/env python3
"""Small independent enumeration sanity checks for INCREMENT_REFEREE.md.

No existing checker, certificate, or unranking routine is imported.  The
infinite statement is proved in the accompanying report, not by this sweep.
"""

from fractions import Fraction
from functools import lru_cache
from itertools import islice
from math import comb


def words(e, degree):
    if e == 1:
        yield (degree,)
        return
    for first in range(degree + 1):
        for suffix in words(e - 1, degree - first):
            yield (first,) + suffix


@lru_cache(None)
def prefix(e, degree, length):
    return tuple(islice(words(e, degree), length))


def largest(word):
    return max(j for j, exponent in enumerate(word, 1) if exponent)


def totals(e, m):
    result = list(range(1, e + 1))
    result[-1] -= m - 1
    for degree in range(2, m - 1):
        for word in prefix(e, degree, m - 1):
            for j in range(largest(word) + 1, e + 1):
                result[j - 1] += 1
    return result


def main():
    slope = sum((Fraction(1, comb(r + 2, 3)) for r in range(2, 9)), Fraction())
    intercept = sum((1 - Fraction(comb(r + 2, 2), comb(r + 2, 3))
                     for r in range(2, 9)), Fraction())
    assert (slope, intercept) == (Fraction(7, 15), Fraction(517, 280))
    assert Fraction(11, 30) - Fraction(97, 280) == Fraction(17, 840)

    rank_cases = 0
    for e in range(3, 8):
        for degree in range(2, 7):
            layer = tuple(words(e, degree))
            no_final = [rank for rank, word in enumerate(layer, 1) if word[-1] == 0]
            assert no_final[:2] == [degree + 1, 2 * degree + 1]
            for r in range(1, e):
                pure = (0,) * (e - r - 1) + (degree,) + (0,) * r
                assert layer.index(pure) + 1 == comb(degree + r, r)
                rank_cases += 1

    base_values = []
    increment_cases = 0
    for e in range(5, 10):
        initial = totals(e, e + 10)
        first = sum(initial)
        assert first <= comb(e + 10, 2)
        for i in range(1, e + 1):
            row = sum(comb(j - 1, i - 1) * initial[j - 1]
                      for j in range(i, e + 1))
            assert row <= i * comb(e + 10, i + 1)
        base_values.append((e, e + 10, first, comb(e + 10, 2)))
        for m in range(e + 10, 41):
            before, after = totals(e, m), totals(e, m + 1)
            delta = [right - left for left, right in zip(before, after)]
            direct = [0] * e
            levels = [0] * (e - 1)
            for degree in range(2, m - 1):
                layer = prefix(e, degree, m)
                if len(layer) == m:
                    a = largest(layer[-1])
                    k = e - a
                    for j in range(a + 1, e + 1):
                        direct[j - 1] += 1
                    if k:
                        assert m >= 2 * degree + 1
                    for r in range(1, k + 1):
                        levels[r - 1] += 1
                        assert comb(degree + r, r) <= m
            assert delta == direct
            assert all(value >= 0 for value in delta)
            assert sum(delta) == sum(levels)
            assert sum(delta) <= Fraction(29 * m, 30) + Fraction(97, 280)
            assert sum(delta) <= m - 1
            increment_cases += 1

    # The optional dimension-free pair bound, checked independently of lex.
    for n in range(1, 301):
        pairs = sum(comb(d + r, d) <= n
                    for d in range(2, n + 1)
                    for r in range(2, n + 1))
        assert pairs <= n // 2

    print('Exact rational identities: passed')
    print('Pure-word rank identities checked:', rank_cases)
    print('O10 endpoint and layer checks:', increment_cases)
    print('Five first-row bases:', base_values)
    print('Dimension-free pair-count sanity cases: 300')


if __name__ == '__main__':
    main()
