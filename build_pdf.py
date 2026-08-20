#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson.
# Licensed under the Apache License, Version 2.0. See LICENSE and NOTICE.
"""Build CARDB.tex and CARDB.pdf from CARDB.md.

Adapted from the scott_models CARDB / LRSODInCIC PDF pipeline:

  1. lift the `# ...` title and Abstract paragraph into \\title and `abstract`;
  2. pandoc the body, demoting headings by one so `##` sections become \\section;
  3. render fenced code with `listings` in the shared `leanbox` style;
  4. reuse scripts/tex_preamble_arxiv.tex, plus glyphs this note uses that the
     original arxiv paper does not;
  5. compile with latexmk.

The generated `.tex` lives in this directory. `CARDB.tex` is git-ignored;
`CARDB.pdf` is the committed deliverable.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "CARDB.md"
LEAN = HERE / "CARDB.lean"
LEAN_SMALLN = HERE / "CARDB" / "SmallN.lean"
LEAN_ASYMP = HERE / "CARDB" / "Asymptotics.lean"
OUT_TEX = HERE / "CARDB.tex"
OUT_PDF = HERE / "CARDB.pdf"
PREAMBLE = HERE / "scripts" / "tex_preamble_arxiv.tex"

AUTHOR = "Lars Warren Ericson"
COMPANY = "Catskills Research Company"
GITHUB_URL = r"https://github.com/catskillsresearch/cardb"
ORCID = "0000-0001-8299-9361"
EMAIL = "lars.ericson@catskillsresearch.com"

EXTRA_LITERATE = r"""    {ä}{{\"{a}}}1
    {é}{{\'{e}}}1
    {∑}{{\ensuremath{\sum}}}1
    {‹}{{`}}1
    {›}{{'}}1
    {∈}{{\ensuremath{\in}}}1
    {·}{{\ensuremath{\cdot}}}1
"""

EXTRA_UNICODECHAR = r"""
% --- Glyphs specific to this document ---
\newunicodechar{ä}{\"{a}}
\newunicodechar{é}{\'{e}}
\newunicodechar{∑}{\ensuremath{\sum}}
\newunicodechar{‹}{`}
\newunicodechar{›}{'}
\newunicodechar{∈}{\ensuremath{\in}}
\newunicodechar{·}{\ensuremath{\cdot}}
\newunicodechar{⦃}{\textbraceleft\textbraceleft}
\newunicodechar{⦄}{\textbraceright\textbraceright}
"""

FENCE_RE = re.compile(r"^```[^\n]*\n(.*?)^```[ \t]*$", re.M | re.S)
PLACEHOLDER = "CARDBCODEBLOCK{}ENDBLOCK"


def extract_fences(md: str) -> tuple[str, list[str]]:
    blocks: list[str] = []

    def take(match: re.Match[str]) -> str:
        blocks.append(match.group(1).rstrip("\n"))
        return PLACEHOLDER.format(len(blocks) - 1)

    return FENCE_RE.sub(take, md), blocks


def splice_fences(latex: str, blocks: list[str]) -> str:
    for i, code in enumerate(blocks):
        listing = "\\begin{lstlisting}\n" + code + "\n\\end{lstlisting}"
        token = PLACEHOLDER.format(i)
        if token not in latex:
            raise RuntimeError(f"code placeholder {i} vanished during conversion")
        latex = latex.replace(token, listing)
    return latex


def pandoc(markdown: str, shift: bool) -> str:
    cmd = [
        "pandoc",
        "-f",
        "markdown+tex_math_dollars+raw_tex+smart",
        "-t",
        "latex",
        "--wrap=preserve",
    ]
    if shift:
        cmd.append("--shift-heading-level-by=-1")
    proc = subprocess.run(cmd, input=markdown, text=True, capture_output=True, check=False)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise RuntimeError("pandoc failed")
    return proc.stdout


def split_front_matter(md: str) -> tuple[str, str, str]:
    """Return (title_md, abstract_md, body_md)."""
    lines = md.splitlines()
    title = ""
    front: list[str] = []
    body_start = 0
    for i, line in enumerate(lines):
        if line.startswith("# ") and not title:
            title = line[2:].strip()
            continue
        if line.strip() == "---":
            body_start = i + 1
            break
        front.append(line)
    abstract = "\n".join(front).strip()
    abstract = re.sub(r"^\*\*Abstract\.\*\*\s*", "", abstract)
    body = "\n".join(lines[body_start:]).lstrip("\n")
    return title, abstract, body


def break_texttt_paths(latex: str) -> str:
    def fix(match: re.Match[str]) -> str:
        inner = match.group(1)
        if "/" not in inner:
            return match.group(0)
        return "\\texttt{" + inner.replace("/", "/\\allowbreak{}") + "}"

    return re.sub(r"\\texttt\{([^{}]*)\}", fix, latex)


def tidy(latex: str) -> str:
    latex = latex.replace("\\pandocbounded{", "{")
    latex = re.sub(r"\\tightlist\n", "", latex)
    return break_texttt_paths(latex)


def build_preamble() -> str:
    text = PREAMBLE.read_text(encoding="utf-8")
    if "literate=\n" not in text:
        raise RuntimeError("could not find the `literate=` table in the shared preamble")
    text = text.replace("literate=\n", "literate=\n" + EXTRA_LITERATE, 1)
    return text + EXTRA_UNICODECHAR + "\n\\providecommand{\\passthrough}[1]{#1}\n"


def build_title_page(title_tex: str, abstract_tex: str) -> str:
    return "\n".join(
        [
            r"\title{\textbf{" + title_tex + "}}",
            "",
            r"\author[1]{\textbf{" + AUTHOR + "}}",
            r"\affil[1]{" + COMPANY + "}",
            r"\affil[1]{\url{" + GITHUB_URL + "}}",
            r"\affil[1]{\texttt{" + EMAIL + "}}",
            "",
            r"\date{\today}",
            "",
            r"\begin{document}",
            r"\maketitle",
            "",
            r"\begin{center}",
            r"  \small",
            r"  \textbf{ORCID:} " + ORCID,
            r"\end{center}",
            "",
            r"\begin{abstract}",
            abstract_tex,
            r"\end{abstract}",
        ]
    )


def listing_block(path: Path, caption: str) -> str:
    rel = path.relative_to(HERE).as_posix()
    n_lines = len(path.read_text(encoding="utf-8").splitlines())
    return "\n".join(
        [
            f"\\subsection{{\\texttt{{{rel}}}}}",
            "",
            f"{caption} ({n_lines} lines).",
            "",
            r"\lstinputlisting{" + rel + "}",
        ]
    )


def build_appendix() -> str:
    return "\n".join(
        [
            r"\appendix",
            r"\section{Complete Lean source}",
            "",
            r"Checked by \texttt{lake build} against Lean 4 and Mathlib. "
            r"\texttt{\#print axioms} on each compared theorem reports "
            r"$\{\mathtt{propext},\ \mathtt{Classical.choice},\ \mathtt{Quot.sound}\}$.",
            "",
            listing_block(
                LEAN,
                r"The fiber lemma and the sum identity of Section~3",
            ),
            "",
            listing_block(
                LEAN_SMALLN,
                r"Kernel-reducible enumeration of the small-$N$ table",
            ),
            "",
            listing_block(
                LEAN_ASYMP,
                r"The sandwich bound and discrete dominance for $N\ge 10$",
            ),
        ]
    )


def main() -> int:
    title_md, abstract_md, body_md = split_front_matter(SRC.read_text(encoding="utf-8"))

    title_tex = tidy(pandoc(title_md, shift=False)).strip()
    abstract_tex = tidy(pandoc(abstract_md, shift=False)).strip()

    stripped_body, blocks = extract_fences(body_md)
    body_tex = splice_fences(tidy(pandoc(stripped_body, shift=True)), blocks)

    document = "\n".join(
        [
            build_preamble(),
            build_title_page(title_tex, abstract_tex),
            "",
            r"\tableofcontents",
            r"\newpage",
            "",
            body_tex,
            "",
            build_appendix(),
            "",
            r"\end{document}",
            "",
        ]
    )
    OUT_TEX.write_text(document, encoding="utf-8")
    print(f"wrote {OUT_TEX.name} ({OUT_TEX.stat().st_size:,} bytes)")

    proc = subprocess.run(
        ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", OUT_TEX.name],
        cwd=HERE,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    if proc.returncode != 0 or not OUT_PDF.is_file():
        log = OUT_TEX.with_suffix(".log")
        sys.stderr.write(proc.stdout[-2000:])
        if log.is_file():
            sys.stderr.write("\n--- tail of LaTeX log ---\n")
            sys.stderr.write("\n".join(log.read_text(errors="replace").splitlines()[-40:]))
        return 1

    pages = subprocess.run(
        ["pdfinfo", OUT_PDF.name], cwd=HERE, capture_output=True, text=True, check=False
    ).stdout
    n_pages = next((l.split()[1] for l in pages.splitlines() if l.startswith("Pages:")), "?")
    print(f"wrote {OUT_PDF.name} ({OUT_PDF.stat().st_size:,} bytes, {n_pages} pages)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
