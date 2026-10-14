# Prime Spherical Fold

Formalized positive-radius fold geometry and explicitly scoped prime-sampling
corollaries. Author: A. Hayami.

For `r > 0` and a circle phase represented by `u`, the surface and observation are

```text
G(r,u) = (r sin(u) cos(u), r sin(u)^2, r cos(u))
O(r,u) = (r cos(u), r sin(u)^2).
```

The Lean development uses the standard smooth cylinder `(0, infinity) x Circle`.
It proves immersion, exhaustive double fibers with transverse branches,
centered Whitney fold normal forms, smooth diagonal embedding, and an explicit
global diffeomorphism to the punctured plane. The integrated theorem is
`PrimeSphericalFold.complete_geometry`.

The arithmetic continuation sets `r = u = p` for a prime `p`. It proves an exact
radius decoder, avoidance of the fold and double line, and the scalar identity
`sin(p)^2 * C_p^2 = 1/4`, where `C_p = 1/(2*abs(sin(p)))`.
Written infinite-prime and distribution conclusions invoke published classical
theorems; those external inputs are not proved in Lean. This project claims
neither a new prime-approximation exponent nor an RH proof.

## Read the results

- [Geometry definitions and theorem map](docs/GEOMETRY.md).
- [Arithmetic results and written proofs](arithmetic/RESULTS.md).
- [Arithmetic claim ledger and open questions](arithmetic/CLAIM_LEDGER.md).
- [Arithmetic replay instructions](arithmetic/README.md).
- [References and admission boundaries](docs/REFERENCES.md).
- [Public export review](docs/PUBLICATION_REVIEW.md).
- [Export provenance and source hashes](evidence/PROVENANCE.json).

The absolute-height question `liminf p*sin(p)^2 = 0` along primes remains open
in this work. Fixed-scale angular laws also hold for all positive integers;
they do not supply a primality test or an RH criterion.

## Replay

Install Lean through [elan](https://github.com/leanprover/elan). The committed
`lean-toolchain` and `lake-manifest.json` pin Lean 4.33.1 and all nine dependency
revisions. From this repository root:

```sh
git config core.hooksPath .githooks
lake exe cache get
lake build
lake env lean arithmetic/PrimeSampling.lean
```

The geometry build audits all 228 companion declarations; the arithmetic
command audits all 35 arithmetic declarations. Both transitively permit only
`propext`, `Classical.choice`, and `Quot.sound`. No placeholder proof or external
arithmetic axiom is admitted.

The optional numerical replay requires Python 3.14.6 with the pinned packages:

```sh
python3.14 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv/bin/python -B arithmetic/verify_prime_sampling.py
```

Run without optimization: assertions are part of verification. The verifier
checks 10 symbolic identities, trial division through 10,000, 78,498 primes
through 1,000,000, integer controls, and 29 high-precision rows. Its strict
frozen-JSON comparison includes the original Python build string and floating
results; another platform or Python build may fail exact replay. Such a
failure is not a mathematical counterexample. See the verification record
for the environment actually tested.

## Repository organization

- Root `PrimeSphericalFold*.lean`: geometry sources and axiom audit.
- `arithmetic/`: exact arithmetic Lean interface, results, and finite verifier.
- `docs/`: theorem map, references, public review, and verification scope.
- `evidence/`: provenance and new public verification receipts.
- `.githooks/`, `scripts/check_english.py`: English publication checks.

This repository is independent of RH/BigBridge and the Prime Dimensionality
Reconstruction manuscript. It does not require their private sources.
Historical research snapshots and failed development logs remain preserved
in the author's private archive and are outside this public export.

## Rights and dependencies

Publicly visible source is provided with all rights reserved; no MIT, Apache,
or other open-source license is granted for original project content.
See [LICENSE](LICENSE) and [third-party notices](THIRD_PARTY_NOTICES.md).
Third-party dependencies retain their own licenses. Reference PDFs are linked,
not redistributed. GitHub viewing and forking rights under its terms are
unaffected.
