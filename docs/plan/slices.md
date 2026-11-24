<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Vertical Slice Delivery Record (`docs/plan/slices.md`)

> Pipeline artifact `P6.F1`. Tracks the end-to-end vertical slices built and verified directly on `main`.

| Slice | Scope | Primary Artifacts | Verification Evidence | Status |
|---|---|---|---|---|
| **S1 — Algebraic Core** | Zero-Mathlib `CommRing`, `Field`, `CatProg`, `PrimeFieldTools` (Lucas binomials & digit sums) | `lean/Catalytic/CommRing.lean`, `PrimeFieldTools.lean` | `lake build` (0 warnings, `autoImplicit=false`) | `done` |
| **S2 — Theorems T1, T2, T4** | Prime-field dichotomy (`T1`), bilinear Frobenius collapse (`T2`), balanced multilinear product (`T4`) | `DigitSumDichotomy.lean`, `BilinearFrobenius.lean`, `BalancedProduct.lean` | `VerifyAxioms.lean` + `exp1` + `exp3` | `done` |
| **S3 — Theorem T3 Breakthrough** | Three-register $x^7, x^9, x^{11}, x^{13}$ (`t=5..8`) + exact exponent inequality chain | `ThreeRegisterBreakthrough.lean`, `experiments/exp2_three_register_breakthrough.py` | 6 Lean kernels + exact Python rational & $t=9$ check | `done` |
| **S4 — Palomar Contract & Non-Vacuity** | Public `Challenge.lean` / `Solution.lean` split + concrete `0 ≠ 1` witnesses (`NonVacuity.lean`) | `lean/Challenge.lean`, `Solution.lean`, `NonVacuity.lean`, `comparator.json`, `formalization.yaml` | 14/14 decls in `results/lean_axioms.txt` | `done` |
| **S5 — Empirical SAT Companion & LRAT Proofs** | CaDiCaL 2.1.2 `exp4` audit, brute-force encoder equivalence, archived `.cnf`+`.lrat` proofs, `scripts/verify_lrat.py` | `experiments/exp4_boolean_mc_companion.py`, `results/sat_certs/*`, `scripts/verify_lrat.py`, `tests/test_all.py` | 14/14 pytest pass + LRAT mutant rejection | `done` |
| **S6 — Manuscript & Figures** | 14-page AMS-LaTeX preprint (`paper/main.tex`), 3 deterministic vector PDFs, clean-room arXiv tarball | `paper/main.tex`, `scripts/make_figures.py`, `dist/Donahue_2026_catalytic_register_frontiers.pdf`, `dist/arxiv_submission.tar.gz` | Tectonic 0 warnings + live 10/10 citation check + visual page inspection | `done` |
| **S7 — Governance, REUSE, Provenance & Launch Prep** | Build Standard v1.1.0 + Pipeline v1.0.0 + Playbook v1.1 hardening, REUSE/SPDX, RFC 3161 timestamp, `MANIFEST.sha256` | `repo.yaml`, `project.yaml`, `REUSE.toml`, `provenance/*`, `docs/launch/*`, `MANIFEST.sha256` | `Audit-Repo.ps1` (98.4%), `pipeline-audit.py`, `run_all.ps1 -Task all` | `done` |
