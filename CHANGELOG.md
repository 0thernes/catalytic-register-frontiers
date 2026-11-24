<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Changelog

All notable changes to `catalytic-register-frontiers` are documented here.

## [1.0.0] - 2026-11-23

### Added
- **Zero-Mathlib Lean 4.35.0 formalization (`lean/`):** 10 `module` files proving 12 exported theorems (`T1`, `T1a`–`T1d`, `T2`, `T3a`–`T3e`, `T4`) plus master bundle `prove_all_catalytic_theorems`, verified across 6 independent kernel runs (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin`) with strict 3-axiom allowlist `[propext, Classical.choice, Quot.sound]` and zero forbidden tokens.
- **Exact-arithmetic verification suite (`experiments/` & `tests/test_all.py`):** 4 reproducible verification scripts (`exp1`–`exp4`, including CaDiCaL 2.1.2 SAT companion audit) and 8/8 passing `pytest` tests.
- **Deterministic vector figures (`scripts/make_figures.py`):** 3 publication-grade PDF figures (`fig1_digit_sum_phase.pdf`, `fig2_three_reg_exponent.pdf`, `fig3_bilinear_and_balanced.pdf`) with `CreationDate: None`.
- **AMS-LaTeX white paper & frozen artifacts (`paper/` & `dist/`):** Compiled via Tectonic with zero Overfull/Underfull hboxes, visually audited page-by-page, plus clean-room verified `dist/arxiv_submission.tar.gz` and `MANIFEST.sha256`.
- **Governance & Build Standard v1.1.0 package:** `README.md`, `CLAIMS.md`, `LIMITATIONS.md`, `REPLICATION.md`, `SECURITY.md`, `CITATION.cff`, `repo.yaml`, `llms.txt`, `llms-full.txt`, ADRs (`docs/adr/`), 10-pass review (`docs/10-pass-review.md`), `scripts/run_all.ps1`, and informational `.github/workflows/ci.yml`.
