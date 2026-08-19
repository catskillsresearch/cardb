# CARDB

The number of distinct topological bases of a finite set of size \(N\).
Formalized in Lean 4 / Mathlib; Mathlib is the only Lake dependency.

For a finite set \(S\) with \(\lvert S\rvert = N\),

\[
\#(N) = \sum_{\mathcal{T} \in \operatorname{Top}(S)} 2^{\lvert\mathcal{T}\rvert - \lvert\mathcal{M}_{\mathcal{T}}\rvert},
\]

where \(\mathcal{M}_{\mathcal{T}}\) is the canonical minimal basis of minimal
open neighborhoods (`nhdsKer` on a finite Alexandrov space). Bases generating
\(\mathcal{T}\) are exactly the families with
\(\mathcal{M}_{\mathcal{T}} \subseteq \mathcal{B} \subseteq \mathcal{T}\).

This repository was split from
[`scott_models/CARDB`](https://github.com/catskillsresearch/scott_models/tree/main/CARDB).

## Files

| File | Role |
|---|---|
| `CARDB.md` | Paper (identity, fiber lemma, small-\(N\) table) — the source of truth |
| `CARDB.lean` | Sorry-free formalization of the sum identity |
| `CARDB.pdf` | Built paper (committed deliverable) |
| `build_pdf.py` | `CARDB.md` → `CARDB.tex` → `CARDB.pdf`, Lean source inlined as an appendix |
| `scripts/tex_preamble_arxiv.tex` | Listings / unicode preamble used by the PDF build |
| `LICENSE` | Apache License 2.0 |
| `NOTICE` | Copyright and third-party attribution |

`CARDB.tex` is generated and git-ignored. The title page lists the author,
Catskills Research Company, and
<https://github.com/catskillsresearch/cardb>.

## Build the Lean

Requires [elan](https://github.com/leanprover/elan) (or an equivalent Lean 4
install). The pin is `leanprover/lean4:v4.30.0`.

```bash
lake build
```

Open `CARDB.lean` in this repository so the Lean server uses this package's
`lakefile.toml`.

## Build the paper

Needs `pandoc` and `latexmk`.

```bash
python3 build_pdf.py
```

## License

Copyright 2026 Lars Warren Ericson. Licensed under the Apache License,
Version 2.0. See `LICENSE` and `NOTICE`.
