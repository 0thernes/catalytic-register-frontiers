<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Run Log (`docs/run-log.md`)

Append-only audit trail of formal builds, multi-kernel replays, exact computations, test runs, and release checks (Build Standard B40). Never overwrite past entries; append corrections as new rows.

| Date (UTC) | Commit | Command | Environment | Results Artifact | Run By |
|---|---|---|---|---|---|
| 2026-11-23 | `dc97c3b` | `lake build && lake env lean VerifyAxioms.lean && leanchecker && leanchecker-paranoid && con-leche --verified && con-ron --verified && nanoda_bin` | Windows 11, Lean 4.35.0 (zero Mathlib) | `results/lean_axioms.txt`, `results/six_kernel_audit.txt` | Alexander S. Donahue + Antigravity |
| 2026-11-23 | `dc97c3b` | `pwsh -NoProfile -File scripts/run_all.ps1 -Task all` | Windows 11, Python 3.13.12, CaDiCaL 2.1.2, Tectonic | `results/exp1..4.json`, `paper/figures/*.pdf`, `dist/*`, `MANIFEST.sha256` (54/54 PASS, 8/8 pytest) | Alexander S. Donahue + Antigravity |
| 2026-11-23 | pre-hardening | `pwsh -NoProfile -File I:\All GH Repos\Repo Checklist\repo-template\scripts\Audit-Repo.ps1 -Path .` | Windows 11, Build Standard v1.1.0 | Baseline audit: 36.0% overall (18/50), 59.1% core (13/22) — triggered full remediation | Alexander S. Donahue + Antigravity |
| 2026-11-23 | pre-hardening | `scripts/check_citations.py` + Crossref/DataCite/arXiv live check + primary PDF review | Python 3.13.12 | Caught & logged `BoyarFind2018` DOI error, `AFM2025` metadata error, and Cor. 5.1.1 / Thm. 5.2 precision fixes in `ERRATA.md` | Alexander S. Donahue + Antigravity |
| 2026-11-23 | post-hardening | Clean 6-kernel Lean rebuild (`NonVacuity.lean` + strict core linters) + 12/12 `pytest` (Hypothesis, mutant, brute-force SAT) + `ruff` (0) + `mypy` (0) + `check_citations.py --online` (10/10) + 0-warning Tectonic PDF + `Audit-Repo.ps1` | Windows 11, Lean 4.35.0, Python 3.13.12, CaDiCaL 2.1.2, Tectonic | `Audit-Repo.ps1`: 98.4% overall (61/62), 96.4% core (27/28, only `A19` remote About/Topics `todo`); 6/6 kernels PASS (3,004 decls); 12/12 pytest; 0 warnings | Alexander S. Donahue + Antigravity |
