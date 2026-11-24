<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Clean-Room Replication Guide (`REPLICATION.md`)

Every Lean 4.35 formal proof, exact-arithmetic experiment, `pytest` assertion, deterministic vector PDF figure, and frozen AMS-LaTeX manuscript in `catalytic-register-frontiers` reproduces end-to-end from scratch.

## Prerequisites

- **Lean 4.35.0** via `elan` (`leanprover/lean4:v4.35.0`, pinned in `lean/lean-toolchain`). Zero Mathlib dependency; builds fully offline once the toolchain is installed.
- **Python 3.13** with pinned packages in `requirements.lock.txt` (`matplotlib==3.11.2`, `numpy==2.5.5`, `pytest==9.2.0`, `scipy==1.18.1`).
- **CaDiCaL 2.1.2** (bundled with Lean 4.35.0 at `<toolchain>/bin/cadical[.exe]`, or set `CADICAL_BIN`).
- **Tectonic** (`tectonic -X compile`) for compiling `paper/main.tex`.

## 1. One-Command Verification (Windows PowerShell)

> **Bracket-Path Safety Note:** On Windows paths containing `[...]`, always pass `-LiteralPath` to PowerShell file cmdlets and run `pytest` repo-relative (`tests/test_all.py`).

```powershell
pwsh -File scripts/run_all.ps1 -Task all
```

Individual stages: `-Task lean`, `-Task experiments`, `-Task tests`, `-Task figures`, `-Task paper`, `-Task audit`.

## 2. Step-by-Step Verification (Linux / macOS / CI)

### A. Clean-from-Scratch Lean 4.35 Multi-Kernel Audit

```bash
cd lean
rm -rf .lake
lake build
lake env lean VerifyAxioms.lean
lake env leanchecker Solution
lake env leanchecker-paranoid Solution

# Export self-contained LF NDJSON stream for external verified kernels
lake env leanexport Solution -- Catalytic.Solution.prove_all_catalytic_theorems > /tmp/catalytic_solution.ndjson
con-leche --verified /tmp/catalytic_solution.ndjson
con-ron --verified /tmp/catalytic_solution.ndjson
```

### B. Exact-Arithmetic Experiments & Pytest Suite

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.lock.txt

python experiments/exp1_digit_sum_dichotomy.py
python experiments/exp2_three_register_breakthrough.py
python experiments/exp3_bilinear_and_balanced.py
python experiments/exp4_boolean_mc_companion.py

pytest -v tests/test_all.py
```

### C. Deterministic Vector Figures & AMS-LaTeX Manuscript

```bash
python scripts/make_figures.py
cd paper
mkdir -p build
tectonic -X compile main.tex --outdir build --keep-intermediates
```

### D. Standalone arXiv Tarball Clean-Room Compilation Test

```bash
mkdir -p /tmp/arxiv_check
tar -xzf dist/arxiv_submission.tar.gz -C /tmp/arxiv_check
cd /tmp/arxiv_check
tectonic -X compile main.tex --outdir out
```

### E. Cryptographic Provenance Check

```bash
sha256sum -c MANIFEST.sha256
```
