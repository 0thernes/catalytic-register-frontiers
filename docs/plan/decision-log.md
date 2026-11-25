<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Decision Log (`docs/plan/decision-log.md`)

Dated go, pivot, and architectural decisions backed by evidence (Build Pipeline Models P1.F3 / P11.F2).

| Date | Decision | Evidence | Outcome |
|---|---|---|---|
| 2026-11-23 | **GO** on unified `T1`–`T4` catalytic register-program research repo | Exploratory exact-arithmetic probes (`open-math-discovery-lab` probes 1–12) discovered the exact $\mathbb{F}_p$ digit-sum dichotomy (`T1`), 2-access bilinear Frobenius collapse (`T2`), 3-register $x^{13}$ exponent $\log_{13} 8 \approx 0.81071$ (`T3`), and $(7d^2-4)/3$ balanced zero-workspace product (`T4`). | Created dedicated public repo `catalytic-register-frontiers`. |
| 2026-11-23 | **GO** on zero-Mathlib Lean 4.35.0 + multi-kernel verification | Avoids multi-GB Mathlib cache while enabling `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, and `nanoda_bin 0.4.19`. | Recorded in ADR 0001; all 5 distinct kernels (6 runs) PASS. |
| 2026-11-23 | **PIVOT (Hardening)** after `I:\All GH Repos` & `I:\White Papers` gap audit | `Audit-Repo.ps1` baseline scored 36.0% overall / 59.1% core; live Pass 5 citation audit caught `BoyarFind2018` DOI and `AFM2025` metadata errors plus Vinciguerra Cor. 5.1.1 / Thm. 5.2 wording gaps. | Added `NonVacuity.lean`, strict Lean core linters, `comparator.json`, Palomar `formalization.yaml`, full Build Standard v1.1.0 files, Hypothesis/mutant/SAT-equivalence tests, fixed BibTeX + paper corollaries, logged in `ERRATA.md`. |
