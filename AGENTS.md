# Repository guidance

Use English for all committed, pushed, and shared content. Keep the configured
Git hooks active: `git config core.hooksPath .githooks`.

Preserve proof provenance and frozen evidence. Distinguish Lean proofs,
explicit hypotheses, written corollaries of external classical theorems,
finite exact checks, numerical diagnostics, and open claims. RH remains open.

Run `lake build`, `lake env lean arithmetic/PrimeSampling.lean`, and the pinned
numerical verifier for affected research changes. Before a commit, run
`python3 -B scripts/check_english.py --candidates` and review staged prose.
Before an authorized push, verify this repository's intended public identity,
branch, outgoing scope, and remote SHA. After a push, verify the remote SHA
and replay from a fresh clone. Do not publish unrelated private research.
