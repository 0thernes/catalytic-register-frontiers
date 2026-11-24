<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Changelog

All notable changes to `catalytic-register-frontiers` are documented here following Keep a Changelog.

## [Unreleased]

- Pending external publication milestones: GitHub push + live CI/SLSA run, Zenodo/OSF DOI minting, Software Heritage SWHID, Palomar Registry submission, and independent external second-person reproduction (`ROADMAP.md`).

## [1.0.0] - 2026-11-23

### Added
- **Zero-Mathlib Lean 4.35.0 formalization (`lean/`):** 11 `module` files (including concrete `0 ≠ 1` non-vacuity witnesses in `Catalytic/NonVacuity.lean`) with strict built-in core linters (`autoImplicit=false`, `linter.unusedVariables=true`, `linter.deprecated=true`), Palomar metadata (`lean/formalization.yaml`), and `lean/comparator.json`, proving 12 exported theorems (`T1`, `T1a`–`T1d`, `T2`, `T3a`–`T3e`, `T4`) + `prove_all_catalytic_theorems` + `nonvac_all_hypotheses`, verified across 6 independent kernel runs (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified` [3,004 decls], `con-ron --verified` [3,004 decls], `nanoda_bin 0.4.19`).
- **Exact-arithmetic, property, mutation, & SAT verification suite (`experiments/` & `tests/test_all.py`):** 4 reproducible verification scripts (`exp1`–`exp4`), 12/12 passing `pytest` tests including Hypothesis property-based & metamorphic shift-invariance tests, 5/5 certificate mutant-killing tests, exhaustive $n=2$ + canonical $n=3$ brute-force SAT encoder equivalence audit, automated citation verification (`scripts/check_citations.py`), and 0-error `ruff` + `mypy` static/type checks.
- **Deterministic vector figures (`scripts/make_figures.py`):** 3 publication-grade PDF figures (`fig1_digit_sum_phase.pdf`, `fig2_three_reg_exponent.pdf`, `fig3_bilinear_and_balanced.pdf`) with `CreationDate: None`.
- **AMS-LaTeX white paper & frozen artifacts (`paper/` & `dist/`):** Compiled via Tectonic with zero warnings (including Statement-Fidelity table, Threats to Validity, CRediT, COI, Export-Control Self-Screen, and Data/Code Availability), visually audited, plus clean-room verified `dist/arxiv_submission.tar.gz`, `paper/arxiv_metadata.txt`, `sbom.cdx.json`, and `MANIFEST.sha256`.
- **Full Build Standard v1.1.0 & Playbook v1.1 Governance:** Schema-validated `repo.yaml` (`repo-standard.schema.json`), `justfile`, `pyproject.toml`, `.env.example`, `.zenodo.json`, `CONTRIBUTING.md`, `CODE_OF_CONDUCT.md`, `SUPPORT.md`, `ROADMAP.md`, `THIRD_PARTY_NOTICES.md`, `ERRATA.md`, `DEVIATIONS.md`, `.github/labels.tsv`, `.github/ISSUE_TEMPLATE/`, `.github/workflows/{ci,release,pages}.yml`, `docs/{architecture,threat-model,configuration,operations,faq,glossary,verification,run-log,statement-fidelity,literature-search-log,legal-and-ethics}.md`, `docs/index.html`, `docs/media/social-preview.svg`, `docs/reviews/01-10-pass-review.md`, `docs/plan/{00-idea,00-redteam,kill-criteria,02-requirements,02-metrics,decision-log}.md`, and `scripts/Audit-Repo.ps1`.

### Fixed
- Pre-release Playbook Pass 5 & Pass 2 audit fixes (`ERRATA.md`): corrected `BoyarFind2018` DOI/title (`10.1016/j.tcs.2018.02.023`), corrected `AFM2025` authors/title/DOI (`10.4230/LIPIcs.MFCS.2025.6`, `arXiv:2504.17412`), refined Corollary `cor:streaming` regular workspace bound and Corollary `cor:matpow` non-commutative scalar register lift to match Vinciguerra (`arXiv:2609.18692`, Cor. 5.1.1 & Thm. 5.2) verbatim.
