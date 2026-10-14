# Third-party notices

- Lean: https://github.com/leanprover/lean4, Apache-2.0.
- Mathlib: https://github.com/leanprover-community/mathlib4, Apache-2.0.
  The manifest pins commit `0df444a360eaa60ab8c11dca51a86af692955474`.
- Transitive Lean packages are identified by upstream URL and exact revision
  in `lake-manifest.json`. Their source, caches, and binaries are not vendored.
- Optional numerical dependencies are NumPy, SymPy, and mpmath, pinned in
  `requirements.txt`; each retains its upstream license.
- Referenced research papers remain the property of their respective rights
  holders. Only citations, links, and reference-file hashes are included.

Original Lean files import upstream declarations and use Mathlib tactics.
No dependency source tree or downloaded reference PDF is included in the
public export. No third-party ownership or license is superseded by the
project's rights notice.
