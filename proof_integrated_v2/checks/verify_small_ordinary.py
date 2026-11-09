"""Exact 83 maximal-first-hit envelopes and five infinite-tail anchors.
Universal source reduction is proved in NS_P14_INTEGRATED_PROOF_JA.md section 15.
No legacy data, stored PASS values, or other checker is imported.
"""
from functools import lru_cache
from fractions import Fraction
from math import comb
from pathlib import Path
import argparse, hashlib, json

def need(condition, message):
    if not condition:
        raise ValueError(message)


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


@lru_cache(None)
def standard_prefix(variables, degree, length):
    """Enumerate only the requested lex-smallest exponent vectors."""
    need(0 <= length <= choose(variables + degree - 1, degree),
         (variables, degree, length, 'impossible prefix size'))
    answer = []

    def append_blocks(prefix, remaining, positions):
        if len(answer) == length:
            return
        if positions == 1:
            answer.append(tuple(prefix + [remaining]))
            return
        for exponent in range(remaining + 1):
            append_blocks(prefix + [exponent], remaining - exponent,
                          positions - 1)
            if len(answer) == length:
                return

    append_blocks([], degree, variables)
    need(len(answer) == length, 'prefix enumeration stopped early')
    return tuple(answer)


@lru_cache(None)
def support_counts(variables, degree, length):
    """S_j = number of standard monomials supported in X1,...,Xj."""
    histogram = [0] * (variables + 1)
    for monomial in standard_prefix(variables, degree, length):
        largest = max(j + 1 for j, exponent in enumerate(monomial) if exponent)
        histogram[largest] += 1
    result = [0]
    for j in range(1, variables + 1):
        result.append(result[-1] + histogram[j])
    need(result[-1] == length, 'wrong support total')
    return tuple(result)


def capped_values(e, m, rho):
    """Hilbert values through the terminal degree rho+1."""
    return (1, e) + tuple(
        m if degree >= rho else min(m - 1, choose(e + degree - 1, degree))
        for degree in range(2, rho + 2))


def envelope(e, m, rho):
    values = capped_values(e, m, rho)
    # Telescoping total counts for lex generators of largest variable j.
    totals = list(range(1, e + 1))
    for degree in range(2, rho + 2):
        supports = support_counts(e, degree, values[degree])
        for j in range(1, e + 1):
            totals[j - 1] += supports[j - 1]
            if degree == rho + 1:
                totals[j - 1] -= supports[j]
    upper = tuple(sum(totals[j - 1] * choose(j - 1, i - 1)
                      for j in range(1, e + 1))
                  for i in range(1, e + 1))
    return values, tuple(totals), upper


def macaulay_growth(value, degree):
    """Independent integer binomial expansion, also checks admissibility."""
    remaining = value
    ceiling = value + degree + 1
    result = 0
    for denominator in range(degree, 0, -1):
        numerator = denominator - 1
        while numerator + 1 < ceiling and choose(numerator + 1, denominator) <= remaining:
            numerator += 1
        term = choose(numerator, denominator)
        remaining -= term
        result += choose(numerator + 1, denominator + 1)
        ceiling = numerator
    need(remaining == 0, ('Macaulay expansion failed', value, degree))
    return result


def tail_certificates():
    """Exact anchors for the five independently proved infinite tails."""
    result = []
    for e, start in ((5, 16), (6, 24), (7, 32), (8, 42), (9, 54)):
        def first_gap(m):
            harmonic = sum((Fraction(1, j) for j in range(1, m + 1)), Fraction())
            upper = (e - 1) * m * harmonic - Fraction((3 * e - 1) * m, 2) + Fraction(e * (e + 1), 2)
            return Fraction(choose(m, 2)) - upper

        def second_gap(m):
            px = Fraction(m * m - 3 * m + 6, 2)
            return 2 * choose(m, 3) - px * choose(e, 2) + m * (e - 1)

        h = sum((Fraction(1, j) for j in range(1, start + 1)), Fraction())
        d1 = first_gap(start)
        delta_d1 = start + Fraction(e + 1, 2) - (e - 1) * h
        need(first_gap(start + 1) - d1 == delta_d1, 'first-gap difference identity')
        need(first_gap(start + 2) - 2 * first_gap(start + 1) + d1
             == 1 - Fraction(e - 1, start + 1), 'first-gap second difference')
        d2 = second_gap(start)
        delta_d2 = start * start - (1 + Fraction(e * (e - 1), 2)) * start + Fraction((e - 1) * (e + 2), 2)
        delta2_d2 = 2 * start - Fraction(e * (e - 1), 2)
        need(second_gap(start + 1) - d2 == delta_d2, 'second-row difference identity')
        need(second_gap(start + 2) - 2 * second_gap(start + 1) + d2 == delta2_d2,
             'second-row second difference identity')
        need(second_gap(start + 3) - 3 * second_gap(start + 2)
             + 3 * second_gap(start + 1) - d2 == 2, 'second-row third difference identity')
        need(all(value > 0 for value in (d1, delta_d1, d2, delta_d2, delta2_d2)),
             (e, start, 'unpaid infinite-tail anchor'))
        result.append({'e': e, 'start_m': start, 'first_row_gap': str(d1),
                       'first_row_forward_difference': str(delta_d1),
                       'first_row_second_difference_at_start': str(1 - Fraction(e - 1, start + 1)),
                       'second_row_gap': str(d2), 'second_row_forward_difference': str(delta_d2),
                       'second_row_second_difference': str(delta2_d2),
                       'second_row_third_difference': '2'})
    return result


def maximal_residual_certificate():
    """Only 83 (e,m) pairs; global last-first-hit lemma is proved on paper."""
    rows = []
    margins = []
    for e, tail in ((5, 16), (6, 24), (7, 32), (8, 42), (9, 54)):
        for m in range(e + 10, tail):
            rho = m - 1
            values, counts, upper = envelope(e, m, rho)
            for degree in range(1, rho + 1):
                need(values[degree + 1] <= macaulay_growth(values[degree], degree),
                     (e, m, degree, 'maximal capped sequence inadmissible'))
            target = tuple(i * choose(m, i + 1) for i in range(1, e + 1))
            for i, (bound, capacity) in enumerate(zip(upper, target), 1):
                need(bound <= capacity, (e, m, i, 'unpaid maximal-first-hit row'))
                margins.append({'e': e, 'm': m, 'rho': rho, 'row': i,
                                'raw': bound, 'capacity': capacity, 'margin': capacity - bound})
            rows.append({'e': e, 'm': m, 'rho': rho, 'hilbert': values,
                         'maxvar_generator_counts': counts, 'raw': upper, 'target': target})
    need(len(rows) == 83 and len(margins) == 665, 'wrong maximal-first-hit coverage')
    canonical = json.dumps(rows, sort_keys=True, separators=(',', ':')) + '\n'
    return {'status': 'EXACT_83_MAXIMAL_FIRST_HIT_PROFILES_AND_FIVE_TAIL_ANCHORS_PAID',
            'scope': 'e=5,...,9 and m>=e+10, ordinary target; final first-hit maximum is proved on paper.',
            'profiles': rows, 'profile_count': len(rows), 'scalar_comparisons': len(margins),
            'profiles_by_e': {e: sum(row['e'] == e for row in rows) for e in range(5, 10)},
            'raw_shortfalls': 0, 'minimum_scalar_margin': min(margins, key=lambda item: item['margin']),
            'profile_sha256': hashlib.sha256(canonical.encode()).hexdigest(),
            'tail_anchors': tail_certificates(),
            'scope_note': 'No MED, D1, D2, legacy graph, or historical approval is used. This is exact arithmetic, not Lean verification.'}



def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path(__file__).resolve().parents[1]/'certificates/small_ordinary.json')
    args=parser.parse_args()
    result=maximal_residual_certificate()
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='profiles'},ensure_ascii=False,indent=2))


if __name__=='__main__':main()
