#!/usr/bin/env python3
"""Small, independent regression for COLEX_BOUND_SEARCH.md; no dependencies."""

from math import comb, isqrt


def lowest_digit(n: int, degree: int) -> int:
    """Greedily unrank n in the degree-d combinatorial number system."""
    remainder = n
    upper = n + degree
    for i in range(degree, 0, -1):
        lower = i - 1
        while lower < upper:
            middle = (lower + upper + 1) // 2
            if comb(middle, i) <= remainder:
                lower = middle
            else:
                upper = middle - 1
        remainder -= comb(lower, i)
        upper = lower - 1
        if i == 1:
            assert remainder == 0
            return lower
    raise AssertionError("Positive degree required")


def interior_count(n: int) -> int:
    count = 0
    # If both arguments are >=2, C(d+k,d) >= C(d+2,2).
    for d in range(2, isqrt(2 * n) + 1):
        k = 2
        while comb(d + k, d) <= n:
            count += 1
            k += 1
    return count


def main() -> None:
    largest_ratio = (0.0, 0, 0)
    for n in range(1, 301):
        total = 0
        for degree in range(2, n):
            digit = lowest_digit(n, degree)
            if 2 * degree > n:
                assert digit == 0, (n, degree, digit)
            for k in range(1, digit + 1):
                assert comb(degree + k, degree) <= n + 1
            total += digit
        k_count = interior_count(n + 1)
        assert 2 * k_count <= n + 1, (n, k_count)
        assert total <= n - 1, (n, total)
        if n >= 4:
            assert total <= n // 2 - 1 + k_count
        largest_ratio = max(largest_ratio, (total / n, n, total))
    print("PASS: all digit and Pascal-count inequalities for 1 <= n <= 300")
    ratio, n, total = largest_ratio
    print(f"Largest observed digit-sum/n: {total}/{n} = {ratio:.6f}")


if __name__ == "__main__":
    main()
