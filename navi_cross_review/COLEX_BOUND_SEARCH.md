# An unrestricted colex lowest-digit bound

The proposed unrestricted bound has an elementary proof, independent of the
number of variables. In fact the following slightly stronger statement holds.

**Proposition.** Let (n\ge1), and write its degree-(d) combinatorial number
representation as

\[
n=\sum_{i=1}^{d}\binom{a_i}{i},\qquad
0\le a_1<a_2<\cdots<a_d,\quad a_i\ge i-1.
\]

Set (z(n,d)=a_1), equivalently the first entry of the corresponding weakly
increasing colex tuple. Then

\[
\boxed{\displaystyle\sum_{d=2}^{n-1}z(n,d)\le n-1.}
\]

Empty sums are zero. This proves both requested bounds (\le n) and
(\le n+1). The argument below is a mathematical proof; the accompanying
small computation is only a regression check.

## 1. Two restrictions on a positive lowest digit

If (z(n,d)\ge k\ge1), strict increase gives (a_i\ge k+i-1). Therefore
the hockey-stick identity gives

\[
n\ge\sum_{i=1}^{d}\binom{k+i-1}{i}
 =\binom{d+k}{d}-1. \tag{1}
\]

Also,

\[
z(n,d)=0\quad\text{if }n/2<d<n. \tag{2}
\]

Indeed, (d+1\le n<2d<\binom{d+2}{d}), so the greedy leading term is
(\binom{d+1}{d}=d+1). Its remainder is
(r=n-d-1<d-1). A positive lowest digit in degree (d-1) would, by (1)
with (k=1), require (r\ge d-1), a contradiction.

## 2. Counting small interior binomial coefficients

Define

\[
K(N)=\#\{(d,k)\in\mathbb Z_{\ge2}^2:
                    \binom{d+k}{d}\le N\}.
\]

We claim

\[
K(N)\le N/2. \tag{3}
\]

For (N<6), the set is empty. Otherwise let (t\ge4) be the largest
integer with (\binom t2\le N). Pairs with (\min(d,k)=2) number exactly
(2t-7): there are (t-3) in each of the two orientations, with
((2,2)) counted twice. Since (t) is an integer,

\[
\binom t2-3(2t-7)=\frac{(t-6)(t-7)}2\ge0.
\]

Thus these pairs number at most (N/3).

Pairs with (d,k\ge3) exist only for (N\ge20). In that case let
(u\ge6) be largest with (\binom u3\le N). Unimodality of a binomial
row implies

\[
\binom{d+k}{3}\le\binom{d+k}{d}\le N,
\]

so (d+k\le u). There are (\binom{u-4}{2}) integer pairs
(d,k\ge3) with this sum restriction. Put (v=u-6\ge0). Vandermonde's
identity gives

\[
\binom u3-6\binom{u-4}{2}
 =\binom v3+3v+14\ge0,
\]

where (\binom v3=0) for (v<3). Consequently this second class has at
most (N/6) pairs. For (6\le N<20) it is empty. Adding the two classes
proves (3).

## 3. Completing the digit bound

For (n\ge4), (2) leaves at most (\lfloor n/2\rfloor-1) possible
degrees. Express each digit as its first unit plus its further units. Each
further unit is indexed by a distinct pair ((d,k)), with (d,k\ge2) and
(k\le z(n,d)); (1) sends it into the set counted by (K(n+1)). Hence

\[
\begin{aligned}
\sum_{d=2}^{n-1}z(n,d)
&\le\lfloor n/2\rfloor-1+K(n+1)\\
&\le\lfloor n/2\rfloor-1+\lfloor(n+1)/2\rfloor\\
&=n-1.
\end{aligned}
\]

For (n=1,2,3) the sum is zero (for (n=3), (z(3,2)=0)), so the same
bound holds.

## Application to the first-hit increment

Under the colex-reversal identification supplied in the review task,
(n=m-1), and the increment is a sum of selected nonnegative terms
(z(n,d)) with (2\le d\le m-2=n-1). Therefore

\[
\Delta B_1(e,m)\le m-2
\]

whenever that identification and degree range apply. This conclusion does
not need the restriction (e\le9). The colex-reversal identification itself
is outside this subtask; it should be checked by the lex-geometry reviewer.

## Verification

`python navi_cross_review/checks/check_colex_digit_bound.py` checks the
independent greedy-unranking formula, support restriction, layer restriction,
Pascal counting bound, and final inequality for (1\le n\le300). It does
not replace the proof above and deliberately avoids a large quadratic run.
