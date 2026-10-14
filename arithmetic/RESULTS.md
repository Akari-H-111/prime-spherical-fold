# Prime sampling, fold recurrence, and arithmetic filling cost

Date: 2026-10-14 (Asia/Taipei).
Status: written prime conclusions with explicit classical inputs; exact model
bridges and conditional Diophantine transfer are Lean checked. No new bound
in prime-distribution theory or proof of RH is claimed.

## Defined arithmetic object

For a prime p define

\[
 F(p)=(p\sin p\cos p,p\sin^2p,p\cos p),\quad
 O_p=(z_p,y_p)=(p\cos p,p\sin^2p),\quad b_p=y_p/p=\sin^2p.
\]

The project now has an explicit `PrimeIndex` type and `primeObservation`.
The intrinsic cylinder point is `primeLift`; its radius and circle angle
are both the same positive integer p. The established A--E geometry remains
in the parent project and is not changed by this continuation.

For the one-dimensional arithmetic local system of the HMR Information
Topology manuscript, choose the fixed character alpha=1/pi and scale q=p:

\[
 v_p=e^{2\pi i p\alpha}-1=e^{2ip}-1,\qquad
 C_p=\inf\{|c|:v_pc=1\}.
\]

Every positive integer has nonzero sine and cosine: a zero of sine would
make a nonzero integer multiple of pi an integer; a zero of cosine would
make sine of twice that integer zero. Thus all prime samples are regular
observation points and are outside the surface double line. In particular
v_p is nonzero, and the filler is uniquely c=v_p^{-1}. Consequently

\[
 |v_p|=2|\sin p|,\qquad C_p=\frac1{2|\sin p|},\qquad
 \boxed{b_pC_p^2=\frac14}.                                      \tag{1}
\]

This is the direct theorem-level map to HMR's filling model. It preserves
its Euclidean/absolute-value norm convention; it is not an inference from
matching pictures or dimensions. The Lean `finiteFillingCost` is only the
finite branch of this cost. Its interpretation as a filling minimum is
proved under nonzero holonomy, which holds for every prime. At a zero
holonomy, HMR's extended filling cost is infinity, not real inverse zero.

## The main prime conclusion: a polynomial approach subsequence

**CLASSICAL-DERIVED, unconditional.** For every 0<epsilon<1/3, there are
infinitely many primes p such that

\[
 \boxed{0<b_p<\pi^2p^{-2/3+2\epsilon}},\qquad
 \boxed{C_p>\frac{p^{1/3-\epsilon}}{2\pi}}.                       \tag{2}
\]

In raw observation coordinates this also gives

\[
 0<y_p<\pi^2p^{1/3+2\epsilon}.                                  \tag{3}
\]

Proof. The number alpha=1/pi is irrational. Theorem 1, p.267, of
[Matomaki, *The distribution of alpha p modulo one*, 2009](https://users.utu.fi/ksmato/wp-content/uploads/sites/1432/2025/04/alphapmod1.pdf)
gives infinitely many primes with distance ||p/pi|| to the nearest integer
less than p^{-1/3+epsilon}. For the nearest integer k,

\[
 |\sin p|=|\sin(p-k\pi)|\le |p-k\pi|
 =\pi\|p/\pi\|<\pi p^{-1/3+\epsilon}.
\]

Squaring proves the first inequality of (2); (1) gives the second, and
multiplication by p gives (3). Positivity follows from pi irrationality.
The input is the published homogeneous theorem (beta=0). No corresponding
inhomogeneous exponent is assumed for the half-period double-line target.

The exact transfer for an arbitrary positive window delta(p) is proved in
Lean as `infinite_prime_fold_approach_of_diophantine`. Its infinite-prime
Diophantine hypothesis is an explicit argument. Matomaki's deep theorem is
an external classical input, not a new axiom and not re-proved in Lean here.
The exponent in (2) is the squared form of the published exponent, not a
new improvement in prime approximation.

## Fixed-scale prime laws and a divergent filling average

**CLASSICAL-DERIVED, unconditional.** Let P(X) count primes at most X.
Vinogradov's prime equidistribution theorem, applied to alpha=1/(2*pi),
says that the phases p modulo 2*pi have uniform limiting angular measure.
This input is recalled explicitly on p.1 of
[Champagne--Le--Liu--Wooley, *Well-distribution modulo one and the primes*](https://www.math.purdue.edu/~twooley/publ/20240627welldist.pdf).
That paper also distinguishes prefix equidistribution from the stronger
uniform-in-starting-index notion; the stronger property is not used here.

For every fixed 0<e<1, the preimage of sin^2 u<=e has angular length
4*arcsin(sqrt(e)), so

\[
 \boxed{\lim_{X\to\infty}\frac{\#\{p\le X:b_p\le e\}}{P(X)}
 =\frac2\pi\arcsin\sqrt e}.                                    \tag{4}
\]

The limiting density is 1/(pi*sqrt(e*(1-e))). Near the fold, the limiting
mass is (2/pi)*sqrt(e)+O(e^{3/2}). This is a statement with X tending to
infinity first and e then tending to zero; it is not a shrinking-window
asymptotic.

For the normalized surface a(p)=F(p)/p and the double-line direction
l=(0,1,0), direct algebra gives |a(p)-l|^2=2*cos^2 p. Thus, for fixed
0<d<sqrt(2), the prime fraction in its full three-dimensional d-tube tends
to (2/pi)*arcsin(d/sqrt(2)), which is (sqrt(2)/pi)*d+O(d^3).
This separates the fold's quadratic observed height from the full-space
transverse double-line distance.

For every fixed T>=1/2, (1) and (4) give

\[
 \boxed{\lim_{X\to\infty}\frac{\#\{p\le X:C_p>T\}}{P(X)}
 =\frac2\pi\arcsin\frac1{2T}\sim\frac1{\pi T}}.                  \tag{5}
\]

In particular

\[
 \boxed{\frac1{P(X)}\sum_{p\le X}C_p\longrightarrow+\infty}.      \tag{6}
\]

Proof of (6). For each fixed M>=1/2, min(C(u),M), assigned the value M at
sine zeros, is continuous and bounded on the circle. Equidistribution
therefore gives convergence of its prime average to

\[
 E\min(C,M)=\frac{2M}{\pi}a-\frac1\pi\log\tan(a/2),\qquad
 a=\arcsin(1/(2M)).
\]

This tends to infinity, asymptotic to (log(4M)+1)/pi. Since C_p dominates
each fixed truncation, the untruncated averages tend to infinity. No rate
is asserted. Integrability of a limiting fractional moment with exponent
below one would not, by itself, prove convergence of its untruncated prime
averages; such a claim would need uniform integrability.

## An exact and stable decoder for the prime index

**PROVED, exact identity Lean checked; stability proved in writing.**
Define on the entire real observation plane

\[
 R(z,y)=\frac{y+\sqrt{y^2+4z^2}}2.
\]

Then R(O_p)=p, so the prime observation map is injective. The circle
observation loses a phase sign at a fixed radius; it does not lose the
prime index along this diagonal sampling. The Lean source proves the
identity for every positive radius and every real angle.

In Euclidean norm, R has the sharp global Lipschitz constant 2/sqrt(3).
Indeed

\[
 R(z,y)=\max_{a^2+b^2=1}\left(az+\frac{1+b}2y\right),\qquad
 a^2+\frac{(1+b)^2}4
 =\frac43-\frac34(b-1/3)^2\le\frac43.
\]

Cauchy--Schwarz bounds the difference of every displayed linear functional,
and hence their maximum, by (2/sqrt(3))*the Euclidean input difference.
Sharpness follows from R(sqrt(2),1)=2 and norm(sqrt(2),1)=sqrt(3).
Therefore, if the Euclidean error of an observation known to originate
from O_p is less than sqrt(3)/4, nearest-integer rounding of the decoded
radius recovers p exactly. This is a model error bound, not a claim about
unmeasured hardware or unknown data.

## Discrepancy transfer, negative control, and remaining question

Let D_circ(X) be the normalized supremum discrepancy over connected circle
arcs for the prime phases. The event in (4) is a union of two disjoint
circle arcs, hence its error at every e is at most 2*D_circ(X). The same
bound holds for (5) and the double-line tube. It follows that a shrinking
fold threshold e(X) has the expected relative asymptotic whenever
D_circ(X)/sqrt(e(X)) tends to zero. A shrinking double-line radius d(X)
requires D_circ(X)/d(X) tending to zero. These are explicit sufficient
conditions; a quantitative prime discrepancy theorem is not manufactured
from qualitative equidistribution.

All positive integers have the same uniform angular limiting law, by the
classical irrational rotation argument: for each nonzero integer h, the
geometric sum of exp(i*h*n), 1<=n<=N, has absolute value at most
2/abs(1-exp(i*h)), independently of N. Its denominator is nonzero by pi
irrationality. Dividing by N and applying Weyl's criterion gives the same
uniform angular measure as for the primes. Thus (4), (5), and the normalized
surface limit cannot alone certify primality, RH, independence of
consecutive prime phases, or a prime-gap assertion. The retained integer
control tests this exact comparison, rather than fitting a different
baseline.

The stronger absolute-caustic question is OPEN in this work:

\[
 \liminf_{p\to\infty,\ p\in\mathbb P}p\sin^2p=0\ ?
\]

Writing d_p=||p/pi||, the elementary bounds 2*d_p<=|sin p|<=pi*d_p
show that this is equivalent to liminf sqrt(p)*d_p=0. The exponent 1/3
input used in (2) does not establish this 1/2-scale question. The finite
witness p=833719 has b_p approximately 5.3495962270e-12 and
C_p approximately 216177.00835, but a finite witness cannot settle the
liminf. No bulk asymptotic at a polynomially shrinking threshold is claimed.
