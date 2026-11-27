<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Phase 2 — Success Metrics (`docs/plan/02-metrics.md`)

Review date: 2026-11-27 (Pass 23 — bivariate `FPS` non-vacuity witnesses `nonvac_T1sc_witness`/`nonvac_T1esc_witness`, hardened LRAT/citation/SW-cache & secondary-doc reconciliation).

| Metric Category | Metric | Target | Current Verified Value |
|---|---|---|---|
| **North Star** | Headline theorems formally verified across 5 distinct Lean 4.35 kernel implementations (6 runs) + non-vacuity witnesses | 22 theorems + NonVacuity (100%) | 22/22 + `prove_all` + `NonVacuity` (24 audited decls across 14 core modules, 8,930 lines; 5 distinct kernels / 6 runs) |
| **Input** | Exact-arithmetic + Hypothesis + mutant + brute-force SAT test pass rate | 100% passing | Verified via `pytest -v tests/test_all.py` |
| **Input** | BibTeX citations resolving via Crossref/DataCite/arXiv with 0 retractions | 10/10 (100%) | 10/10 verified (`docs/literature-search-log.md`) |
| **Guardrail** | Forbidden tokens (`sorry`, `admit`, `native_decide`, custom `axiom`, `@[extern]`) | 0 | 0 |
| **Guardrail** | LaTeX typography / hyperref warnings & figure overlaps | 0 | 0 (all pages & figures visually audited) |
| **Guardrail** | Build Standard v1.2.0 `Audit-Repo.ps1` Core completion | 100% locally actionable Core items | Audited via `scripts/Audit-Repo.ps1` (100.0%, 62/62) |
