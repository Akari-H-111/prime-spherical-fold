# Arithmetic claim ledger

| ID | Claim | Status | Hypotheses and dependency | Evidence |
| --- | --- | --- | --- | --- |
| P1 | Recover the prime index exactly from the two observed coordinates; observation is injective | PROVED / LEAN | Positive radius, original trigonometric observation; no asymptotic input | `recoverRadius_observation`, `primeObservation_recovery`, `primeObservation_injective` |
| P2 | No prime sample is an actual fold point or a surface double-line point | PROVED / LEAN | Prime positive integer, pi irrationality; the stronger nonvanishing lemmas hold for all positive integers | `prime_never_critical`, `prime_has_no_surface_partner` |
| P3 | HMR scalar minimum filling cost equals 1/(2*abs(sin p)); fold height times its square is 1/4 | PROVED / LEAN | Explicit character 1/pi, prime scale, nonzero holonomy, absolute-value norm | `holonomy_norm`, `filling_minimum`, `fold_filling_identity` |
| P4 | Infinitely many primes have b_p < pi^2*p^(-2/3+2*epsilon) and growing C_p | CLASSICAL-DERIVED / WRITTEN; MODEL TRANSFER LEAN | 0<epsilon<1/3; Matomaki Theorem 1, homogeneous shift only | `RESULTS.md` (2); `infinite_prime_fold_approach_of_diophantine` has its input as an explicit hypothesis |
| P5 | Fixed-scale folded prime CDF is the arcsine law, with a square-root mass near zero | CLASSICAL-DERIVED / WRITTEN | Fixed threshold, prime equidistribution for 1/(2*pi) | `RESULTS.md` (4); numerical comparisons are supplemental only |
| P6 | Fixed filling tail is asymptotic to 1/(pi*T), and prime average cost tends to infinity | CLASSICAL-DERIVED / WRITTEN | Prime equidistribution plus fixed bounded truncations; no unsupported uniform-integrability step | `RESULTS.md` (5)--(6) |
| P7 | Decoder is globally Euclidean Lipschitz with sharp constant 2/sqrt(3) | PROVED / WRITTEN, ALGEBRA CHECKED; NOT LEAN | Explicit support-function formula on the whole observation plane | `RESULTS.md`; exact symbolic coefficient identity in the verifier |
| P8 | Two-arc discrepancy gives uniform absolute error at most twice circular discrepancy | PROVED / WRITTEN | Definition of circular arc discrepancy; shrinking relative laws require the additional stated rate conditions | `RESULTS.md`; finite discrepancy diagnostics |
| P9 | All integers share the same angular limiting laws, so those laws alone do not detect primality or RH | CLASSICAL-DERIVED / WRITTEN; NUMERICAL CONTROL | Irrational rotation / Weyl criterion; no consecutive-phase independence | `RESULTS.md`, integer-control rows in the numerical result |
| O1 | Absolute caustic height has liminf zero along primes | OPEN IN THIS WORK | Equivalent to a 1/2-scale prime Diophantine approximation condition; not implied by the cited 1/3 result | Open question in `RESULTS.md`; finite witness 833719 is not a proof |

## Claim diff from the geometry-only checkpoint

The former checkpoint had no defined prime-sampling object or arithmetic
conclusion. This continuation adds P1--P9 with the dependency distinctions
above. It does not upgrade a finite computation to an infinite theorem,
add an inhomogeneous 1/3 claim, prove an RH error rate, or change the
hypotheses or source files of the completed A--E geometry.

## Counterexample search and falsification

- Comparing all positive integers with primes exposes the failure of a proposed angular-only primality discriminator. Their limiting folded CDFs coincide; finite discrepancies differ.
- The composite integer 355 is an exceptionally close finite phase return. Large filling cost alone is not a primality certificate.
- Fixed-scale equidistribution does not justify replacing the threshold by an arbitrary function tending to zero. The discrepancy conditions make the missing rate explicit.
- A divergent untruncated mean is proved by lower bounds from every fixed truncation. No convergence claim is made for untruncated fractional moments solely from the limiting density.
- Any failure of the exact decoder, scalar norm identity, or branch conditions would invalidate the corresponding model bridge. Lean and independent symbolic/high-precision checks cover those claims within their stated domains.
- The sine-zero branch has infinite HMR filling cost and is outside the real-valued finite-branch interpretation. Every positive integer sample is proved to avoid it.

The next substantive strengthening would be a quantitative prime discrepancy
bound adequate for a specified shrinking window, or a theorem at the absolute
caustic's 1/2 scale. The current results do not establish either strengthening.
