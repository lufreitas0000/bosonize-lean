---
trigger: glob
globs: "**/*.tex, **/*.bib, **/*.sty, **/*.cls"
description: LaTeX monograph/labbook macros, warm-parchment typography, and % SOURCE [STATUS] citation rules.
---
<!-- @CANONICAL-RULE: DO NOT EDIT DIRECTLY. MANAGED BY project-governance -->
# Pack: LaTeX Design System, Modular Compilation & Figure Pipeline

## 1. Shared Preamble, Macro Library & Theme Toggle
- All LaTeX documents in a repository (`doc/labbook/` and `doc/manuscript/`) must import a single shared macro and preamble library located in `doc/shared/macros.tex` and `doc/shared/preamble.tex` so mathematical notation never drifts between fronts.
- Use the canonical `\newif\ifwarmtheme` switch in `doc/shared/preamble.tex`:
  - **Warm Screen / Labbook Mode (`\warmthemetrue`):** Soft parchment background (`#FAF6EE`), dark charcoal ink (`#2B2B2B`), deep navy accents/links (`#1A365D`), and warm stone rules (`#D1C7B7`). Default for `doc/labbook/` (`memoir`, 11pt, A4, 28mm margins).
  - **Print / Journal Mode (`\warmthemefalse`):** Crisp white background (`#FFFFFF`) and black ink (`#000000`). Default for `doc/manuscript/`.

## 2. Modular Section-Owned Sources & Build Hygiene
- Standard compiler: `latexmk` (`-pdf -interaction=nonstopmode -halt-on-error`).
- For standalone technical notes (`doc/notes/<note>/`), keep only `<note>.tex`, `<note>_<version>.pdf`, `figures/`, `archive_builds/`, and `aux/` at the top level, placing `Makefile`, `refs_*.bib`, and compiler temporaries inside `aux/` via:
  ```makefile
  BIBINPUTS=aux: latexmk -pdf -jobname=$(DOC)_$(VERSION) -auxdir=aux -emulate-aux-dir \
    -interaction=nonstopmode -halt-on-error $(DOC).tex
  ```
  and archive superseded `<note>_v*.pdf` files into `archive_builds/` on rebuild or version bump.
- Structure multi-chapter documents (`doc/labbook/` and `doc/manuscript/`) using chapter- or section-owned `.tex` files (`chapters/ch_*.tex` or `sections/sec_*.tex` via `\include`, `\input`, or `subfiles`) so individual sections can be compiled, reviewed, and passed to LLM agents without touching the entire book.
- Keep all auxiliary files (`.aux`, `.log`, `.fls`, `.fdb_latexmk`, `.out`, `.toc`, `.bbl`, `.blg`) and TikZ externalization caches (`build/figures/` or `cache_tikz/`) out of Git history. Provide a `make clean-build` or `make clean` target.

## 3. Editorial & Provenance Source Comments
- Every numbered `\section` (and independent `\subsection`) must be preceded by `% EDITORIAL QUESTION: <question>` and answer that question in its closing paragraph.
- Every externally sourced formula or theorem must include `% SOURCE [VERIFIED|UNVERIFIED]: <edition, section/equation locator, claim>`.
- Every project claim promoted from Front 1 (`doc/rnd/`) must include `% CLAIM: <ID> (note: ..., test: ..., data: ...)`.

## 4. Reproducible Data-to-Figure Pipeline (`.dat` $\to$ `pgfplots` / TikZ)
- Never embed raster screenshots or untracked plot images.
- Compute scripts export compact ASCII `.dat` or `.csv` tables (`< 100 KB`) into `data/processed/benchmarks/` with `#` provenance headers (`git_sha`, `timestamp`, script path, physical parameters).
- Author figures and benchmark tables in `doc/figures/fig_*.tex` (or directly in chapters) using `pgfplots`, `pgfplotstable`, and `tikz` (with `tikz-cd` for commutative diagrams) reading directly from `data/processed/benchmarks/*.dat`.
