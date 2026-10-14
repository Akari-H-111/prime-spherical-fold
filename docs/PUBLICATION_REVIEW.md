# Public export review: 2026-10-14

## Publication scope

This is an independent public repository authorized by the author on
2026-10-14. It contains only the Prime Spherical Fold geometry and arithmetic
companion, not the RH or HMR repositories and not their Git histories.
All shared prose, filenames, commit messages, and publication receipts are
English. Commits use the owner's GitHub no-reply address.

The original seven geometry proof modules, arithmetic Lean source, build pins,
arithmetic results, claim ledger, and numerical verifier were exported without
byte changes. Their 14 hashes are in `evidence/PROVENANCE.json`. New reader
navigation and references replace private working-directory instructions.
Historical local sources, frozen snapshots, and failed logs remain preserved
separately; they were not rewritten to create this export.

## Rights review

No pre-existing project-level reuse license was identified in the source
companion. The public project therefore retains all rights to original content
rather than assigning an unrequested MIT, Apache, or Creative Commons license.
GitHub viewing and forking rights under its terms remain applicable. This is a
publicly visible research repository, not an open-source license grant.
See [GitHub's licensing documentation](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/licensing-a-repository).

Mathlib and Lean are referenced as dependencies with their upstream licenses.
Their source trees and binaries are not redistributed here. Reference papers
are cited and linked; downloaded PDFs and private manuscript excerpts are
excluded. The model interface is defined and proved in the published sources,
so no private HMR manuscript is needed to replay it. This is an inventory and
publication-scope review, not an external legal opinion or originality audit.

## Validation before the first push

- `lake build`: PASS; 228 geometry declarations audited, no warnings.
- `lake env lean arithmetic/PrimeSampling.lean`: PASS; 35 arithmetic declarations
  audited, no warnings. Only `propext`, `Classical.choice`, and `Quot.sound`
  are allowed by the transitive audits.
- Pinned Python numerical replay: PASS with exact frozen-JSON comparison;
  10 symbolic identities, 10,001 trial-division cross-checks, 78,498 primes,
  and 29 high-precision diagnostic rows.
- A new Python 3.14.6 virtual environment installed `requirements.txt` from the
  package index and independently passed the same frozen numerical replay.
- All 14 exported source hashes matched the preserved research checkpoint.
- Candidate inventory was checked for local home paths, private email,
  credential patterns, symlinks, binaries, caches, and unrelated research.
  The English gate self-test passed; candidate/index checks and manual prose
  review are required before committing and are enforced by Git hooks.

The new project had no previous project build artifacts. Lean dependency
sources and compiled dependency caches were copied independently from the
existing manifest-matched local cache. No network installation of Lean/Mathlib
on a clean machine is certified. Raw verification output is in `evidence/`.
The numerical verifier remains strict about Python build metadata and floating
results; another platform may fail exact replay without contradicting a theorem.

## Research boundaries

Geometry is Lean checked on the standard positive-radius cylinder; the
radius-zero vertex is excluded. Arithmetic model identities and the conditional
Diophantine transfer are Lean checked. Infinite-prime and limiting-distribution
corollaries use explicitly cited classical results in written proofs.
Numerical diagnostics establish no infinite statement. The prime exponent is
not a new improvement. Absolute caustic liminf zero, general shrinking-window
laws, and RH remain unproved in this work. No external peer review or claim of
novelty, optimality, or complete clean-machine portability is supplied.
