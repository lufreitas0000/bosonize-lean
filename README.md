# Bosonize-Lean: Exact Lattice AQFT Bosonization in Lean 4

[![Build LaTeX Monograph](https://github.com/lufreitas0000/bosonize-lean/actions/workflows/latex.yml/badge.svg)](https://github.com/lufreitas0000/bosonize-lean/actions/workflows/latex.yml)
[![Download Monograph PDF](https://img.shields.io/badge/PDF-Download%20Monograph-blue?logo=adobe-acrobat-reader)](https://github.com/lufreitas0000/bosonize-lean/releases/download/latest/bosonize-monograph.pdf)

Bosonize-Lean develops exact algebraic results for one-dimensional lattice bosonization. The formalization distinguishes finite-dimensional fermionic CAR spaces from uncompressed polynomial CCR carriers and states exactly where finite-band, energy-budget, charge-sector, and projection hypotheses apply. Formal power series are coefficientwise constructions; analytic limits and continuum interpretations require separate arguments.

## Current status

| Scope | Status | Evidence and limits |
| --- | --- | --- |
| CH01–18 and implemented support | Phase C complete; promoted and frozen | See the chapter records under `docs/webllm/chapters/` and the [adaptive roadmap](adaptative_roadmap.md). |
| CH19/A08 | Phase C complete; 62 theorem contracts promoted | Fresh build, strict locks, standard-axiom audits, and independent migration and pedagogy reviews are recorded in [the validation report](note/ch19_phase_c_validation_2026-10-16.md). General-orientation Wick contractions, analytic vertex evaluation, finite interacting-state equivalence, and continuum power laws remain outside its scope. |
| CH20 finite order parameters and duality | Phase C complete; 64 theorem contracts promoted and frozen | Local Phase C evidence and independent review are in [the validation report](note/ch20_phase_c_validation_2026-10-16.md). That is Lean acceptance evidence; the LaTeX book has a separate GitHub Actions build and release workflow. |
| CH21 and dependent CH20b work | Pending | See the [roadmap](adaptative_roadmap.md) for current dependencies and acceptance gates. |

Lean completion and book completion are tracked separately. The LaTeX master currently includes Chapters 1–19 and Appendix A07. The full Chapter 19 replacement follows Chapter 18; its source compiles in the book, while independent editorial review of this replacement remains pending. Chapters 20–21 have staged LaTeX sections that are not yet included in the master. Therefore the released PDF is a working manuscript, not the complete 21-chapter monograph.

Download the [latest compiled monograph PDF](https://github.com/lufreitas0000/bosonize-lean/releases/download/latest/bosonize-monograph.pdf). Its [build receipt](https://github.com/lufreitas0000/bosonize-lean/releases/download/latest/book-build.json) records the source revision and PDF hash.

## Repository map

| Path | Contents |
| --- | --- |
| `Bosonize/Core/` | Promoted, frozen Lean modules. |
| `BosonizeStubs/` | Staging interfaces and approved proof work. |
| `docs/companion/` | Source-mirrored design, declaration mapping, and proof evidence. |
| `notes/md/` | Pedagogical chapter notes. |
| `notes/latex/` | Book master, chapter and appendix sources, bibliography, and build files. |
| `docs/webllm/chapters/` | Machine-readable phase and source-migration records. |
| `note/` | Dated validation records, audits, and scoped checkpoints. |
| `adaptative_roadmap.md` | Project roadmap, chapter dependencies, and release gates. |

## Build and validation

Build the LaTeX book locally:

```bash
make -C notes/latex
```

The GitHub Actions workflow **Build LaTeX Monograph** runs on relevant pushes and pull requests. It checks that manifest-listed chapter and section sources are included in the master, compiles the book, rejects unresolved references and duplicate labels, binds a source/PDF hash receipt, and uploads the PDF and logs. A successful push to `main` also updates the GitHub release named `latest`.

For the Lean repository checks:

```bash
make ci
```

The Lean build, freeze guards, warning and placeholder checks, and axiom audits provide separate evidence. A successful LaTeX build does not establish mathematical correctness, and a Lean promotion does not imply that the corresponding chapter is already integrated into the book.

## Chapter workflow

Lean chapters follow three reviewed phases:

1. **Phase A — Specify:** define the mathematical scope and carrier, prepare the interface and companion record, and independently review the exact declarations.
2. **Phase B — Prove:** preserve the approved interface while completing proofs; run the compiler, lock, placeholder, warning, and axiom checks.
3. **Phase C — Audit and promote:** independently review the proof and pedagogy, migrate accepted sources to frozen Core, and record fresh build and audit evidence.

The chapter phase record describes Lean status. The LaTeX catalog and import manifest separately describe book inclusion and editorial review. Neither status is inferred from the other.

See the [formalizer workflow](.agents/skills/formalizer/SKILL.md), [pedagogical synchronization guidance](.agents/skills/pedagogical-sync/SKILL.md), [LaTeX writing workflow](docs/webllm/LATEX_WORKFLOW.md), and [adaptive roadmap](adaptative_roadmap.md) for the detailed procedures.
