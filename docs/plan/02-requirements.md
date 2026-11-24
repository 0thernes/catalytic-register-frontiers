<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Phase 2 — Requirements & Non-Goals (`docs/plan/02-requirements.md`)

## Problem & Users
- **Problem:** Independent algebraic-complexity results produced with AI proof tooling face justified skepticism unless definitions, proofs, computations, citations, and manuscripts are mechanically auditable from a clean clone.
- **Target users:** Theoretical computer scientists (catalytic computing, circuit complexity), Lean 4 / Palomar reviewers, and independent replicators.

## Scope (Must-Have)
1. Complete zero-Mathlib Lean 4.35.0 formalization of Theorems `T1` (`T1a`–`T1e`, `T1s`, `T1es`), `T2` (`T2b`), `T3` (`T3a`–`T3i`, including complete 4-register passive powering for all $N \ge 1$ and pointwise product-ring streaming frequency moments $F_D$), `T4`, and `NonVacuity` (14 modules, 8,069 lines, 22 audited declarations), passing 6 kernel runs.
2. Independent exact-arithmetic and CaDiCaL 2.1.2 verification scripts (`exp1`–`exp4`) + `pytest` / Hypothesis / mutant / brute-force SAT tests.
3. Deterministic vector PDF figures (`fig1`–`fig3`) and zero-warning AMS-LaTeX white paper + clean-room `dist/arxiv_submission.tar.gz`.
4. Full Build Standard v1.1.0 + Independent Research Playbook v1.1 governance, provenance (`MANIFEST.sha256`, `sbom.cdx.json`), and bibliographic audit.

## Explicit Non-Goals
1. **Not a P vs. NP proof** (and makes zero complexity-class separation claims beyond passive catalytic register programs).
2. **Not a Mathlib-dependent library** (keeping zero external Lake dependencies is an explicit trust-base invariant; see ADR 0001).
3. **Not a hosted web service or commercial product** (`service: false`, `deployed: false`, `personal_data: false`).
4. **Not redistributing third-party PDFs** (all prior literature is cited by arXiv ID / DOI only).

## User Journeys & Acceptance Criteria
1. **Clean-Room Lean Auditor:** Given a fresh clone with Lean 4.35.0 installed, when running `just build` (or `pwsh scripts/run_all.ps1 -Task lean`), then all 17 targets build with 0 warnings, `VerifyAxioms.lean` matches `results/lean_axioms.txt` verbatim (22/22 declarations), and `leanchecker` + `leanchecker-paranoid` + `con-leche` + `con-ron` exit 0.
2. **Computational & Adversarial Tester:** Given `.venv` installed from `requirements.lock.txt`, when running `pytest -v tests/test_all.py`, then all exact-arithmetic, Hypothesis property, mutant-killing, and brute-force SAT encoder equivalence tests pass.
3. **Manuscript & Provenance Referee:** Given Tectonic installed, when running `just reproduce`, then `paper/build/main.pdf` compiles with 0 warnings, `dist/arxiv_submission.tar.gz` compiles in a clean temp directory, and `MANIFEST.sha256` passes 100%.

## Non-Functional Requirements
| NFR | Measurable Target | Measured |
|---|---|---|
| Clean Lean build time | < 120 s offline, zero external deps | 56.6 s cold-start (< 60 s), 0 deps |
| Axiom trust base | $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$ | 22/22 decls pass |
| Forbidden tokens in `lean/` | 0 matches | 0 matches |
| LaTeX warnings (Overfull/Underfull/hyperref) | 0 warnings | 0 warnings |
| Build Standard v1.1.0 Core completion | 100% of applicable local Core items | Verified via `Audit-Repo.ps1` |
