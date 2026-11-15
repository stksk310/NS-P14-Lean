#!/usr/bin/env python3
"""Exact transcription checks for ordinary proof identities.

This checks rational polynomial identities and five explicit coefficient rows.
It does not prove the actual semigroup/tower/Tor constructions or the theorem.
Requires Python 3 and SymPy; uses no floating-point arithmetic.
"""

from fractions import Fraction as Q
import sympy as sp


def assert_zero(name, expression):
    assert sp.cancel(expression) == 0, name
    print(f"PASS {name}")


r, n, H, e0, shift_e, shift_d, e, d, j = sp.symbols(
    "r n H e0 shift_e shift_d e d j"
)
a = r * (r + 1) / 2
alpha = (r - 1) / (n + 1)
beta = 1 - alpha
c = (r + 1) / 2 - alpha
tail = (r - 1) * (H - sp.Rational(3, 2)) - (n - 2) * alpha


def volume(embedding, deficit):
    return embedding + deficit / 2 - sp.Rational(3, 2)


def upper(embedding, deficit):
    M = embedding + deficit - 1
    return (
        alpha * deficit * volume(embedding, deficit)
        + (r - 1 - alpha) * deficit
        + c * (M - a)
        + M * tail
    )


def gap(embedding, deficit):
    return deficit * (volume(embedding, deficit) + 1) - upper(embedding, deficit)


g = gap(e0, a)
A = a - 1 - (r - 1) * (H - 2 + (a + 2) / (n + 1))
b = gap(e0, a + 1) - g
assert_zero("O17 arbitrary-base cutoff identity", gap(e0 + shift_e, a + shift_d)
            - g - shift_e * A - shift_d * b
            - beta * (shift_d * (shift_d - 1) / 2 + shift_e * shift_d))
assert_zero("small-rank forward difference", b.subs(e0, r + 1) - A - 2
            + alpha * (r - 1))

# Pascal reduces the target first difference to this polynomial identity.
# Here X = C(d+r-1,j-1), and j*C(d+r-1,j) = (d+r-j)*X.
X = sp.symbols("X")
assert_zero("O12 first difference after Pascal",
            (e - r + j) * X + (d + r - j) * X - (e + d) * X)
assert_zero("O12 capacity first difference",
            (d + 1) * (volume(e, d + 1) + 1)
            - d * (volume(e, d) + 1) - e - d)

# The harmonic barrier and continuous floor identities used by the large branch.
B = lambda rank: rank / 4 + 1 + sp.Rational(9, 2) / rank
x = r - 10
assert_zero("OL4 positive quartic identity", B(r + 1) - B(r) - (r + 2) / (a + 3)
            - (x**4 + 34*x**3 + 385*x**2 + 1472*x + 112)
            / (4*r*(r+1)*(r*r+r+6)))
T = (a*(a+22-r)/(2*(r-1)*(a+9)) + (2*r-3)/(r-1)
     - (a*(a+21)+36)/(2*(n+1)*(a+9)))
Tlow = (a*(a+22-r)/(2*(r-1)*(a+9)) + (2*r-3)/(r-1)
        - (a*(a+21)+36)/((a+3)*(a+9)))
assert_zero("OL5 seed-threshold identity", gap(10, a)-(r-1)*(a+9)*(T-H))
assert_zero("OL6 positive threshold gap", Tlow-B(r)
            - (r**3*((r-10)*(2*r+15)+2)+r*(111*(r-10)+210)+972)
            / (2*r*(r-1)*(r*r+r+6)*(r*r+r+18)))
C = a*(-a*(n-r+2)-n*(r-4)+3)/(2*(n+1))
large_b = gap(10, a+1)-gap(10, a)
assert_zero("OL7 seed-slope identity", gap(10,a)-(a+9)*A-C)
assert_zero("OL7 step identity", large_b-A-11+r+8*alpha)
F = -C/(a+9)+11-r-8*alpha
Fmin = (a/2-3*r/2+sp.Rational(11,2)
        +3*(5*r+31)/(2*(a+9))-17*(r-1)/(a+3))
assert_zero("OL8 continuous floor comparison", F-Fmin
            -(2*n-a-1)*(r-1)*(a*a+17*a+144)/(2*(a+9)*(n+1)*(a+3)))
assert_zero("OL9 rational quadrant identity", gap(10+shift_e,a+shift_d)-gap(10,a)
            -shift_e*A-shift_d*(large_b-beta/2)
            -beta*(shift_d**2/2+shift_e*shift_d))


def exact_gap(rank, cutoff, embedding, deficit):
    tri = rank*(rank+1)//2
    al = Q(rank-1,cutoff+1)
    cc = Q(rank+1,2)-al
    vv = Q(embedding)+Q(deficit,2)-Q(3,2)
    mm = embedding+deficit-1
    tw = sum((Q(rank-1,k+1)-al for k in range(2,cutoff)), Q())
    uu = al*deficit*vv+(rank-1-al)*deficit+cc*(mm-tri)+mm*tw
    return deficit*(vv+1)-uu


rows = [
    (4,7,280,2443,762,1007),
    (5,10,6930,39380,28429,32209),
    (6,13,72072,-7479,424147,439591),
    (7,17,2042040,-12196485,17076937,17076937),
    (8,21,739024,-5070732,8418651,8250691),
]
for rank, cutoff, denominator, gg, aa, bb in rows:
    tri = rank*(rank+1)//2
    gg_actual = exact_gap(rank,cutoff,rank+1,tri)
    aa_actual = exact_gap(rank,cutoff,rank+2,tri)-gg_actual
    bb_actual = exact_gap(rank,cutoff,rank+1,tri+1)-gg_actual
    assert (gg_actual*denominator, aa_actual*denominator, bb_actual*denominator) == (gg,aa,bb)
    assert aa_actual > 0 and bb_actual > 0 and Q(rank-1,cutoff+1) < 1
    assert gg_actual > 0 or (gg_actual+aa_actual > 0 and gg_actual+bb_actual > 0)
    print(f"PASS exact small-rank row {rank}")

H28 = sum((Q(1,k) for k in range(1,29)), Q())
assert Q(79,20)-H28 == Q(1833472237,80313433200)
assert exact_gap(9,23,10,45) == Q(5845533,7436429)
print("PASS two exact large-rank anchors")
print("All transcription checks passed; universal mathematical coverage is in the proof.")
