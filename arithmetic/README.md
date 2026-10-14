# Arithmetic continuation

Read [RESULTS.md](RESULTS.md) and [CLAIM_LEDGER.md](CLAIM_LEDGER.md) for the
statements, complete written arguments, assumptions, and open boundaries.
The model bridge is self-contained: nonzero scalar holonomy `exp(2*i*p)-1`
has the unique filler `1/(exp(2*i*p)-1)` and minimum norm `1/(2*abs(sin(p)))`.
No private manuscript is required to verify this identity.

From the repository root, after installing the pinned Lean toolchain:

```sh
lake exe cache get
lake build
lake env lean arithmetic/PrimeSampling.lean
```

The default build is geometry only. The standalone command is required for
arithmetic and audits all 35 arithmetic declarations. The infinite-prime
transfer takes its Diophantine input as an explicit hypothesis. Matomaki's
homogeneous approximation theorem and classical prime equidistribution are
external inputs to the written corollaries, not Lean axioms.

For the optional numerical replay, follow the pinned Python setup in the root
README and run:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv/bin/python -B arithmetic/verify_prime_sampling.py
```

The unchanged verifier compares the frozen evidence JSON exactly, including
Python build metadata. This is a deliberately strict replay of the recorded
environment, not a cross-platform tolerance test. The finite/numerical record
does not prove equidistribution, infinitely many prime approximations, or RH.
