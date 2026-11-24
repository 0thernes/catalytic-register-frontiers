# SPDX-License-Identifier: Apache-2.0
# Task runner (https://just.systems). Run `just` to list recipes.
# Cross-platform: uses [unix] / [windows] recipes and Python one-liners so every
# recipe runs cleanly on Linux/macOS bash AND Windows PowerShell (even on bracketed paths).
# No recipe installs git hooks or gates a commit or push (Build Standard R1).

set shell := ["bash", "-euo", "pipefail", "-c"]
set windows-shell := ["pwsh", "-NoProfile", "-Command"]

py := if os_family() == "windows" { "python" } else { "python3" }

# List available recipes
default:
    @just --list

# Verify Lean 4.35.0 toolchain and install pinned Python dependencies
[unix]
setup:
    cd lean && lean --version
    {{py}} -m pip install -r requirements.lock.txt

[windows]
setup:
    Push-Location -LiteralPath lean; try { lean --version } finally { Pop-Location }
    {{py}} -m pip install -r requirements.lock.txt

# Build zero-Mathlib Lean 4.35 proofs, check axioms, and replay through external kernels
[unix]
build:
    bash scripts/run_all.sh lean

[windows]
build:
    pwsh -NoProfile -File scripts/run_all.ps1 -Task lean

# Run full pytest suite (exact arithmetic, Hypothesis property tests, mutant checks, SAT equivalence)
test:
    pytest -v tests/test_all.py

# Run static analysis, LRAT certificate check, REUSE/SPDX audit, and strict type checks (report-only)
[unix]
lint:
    ruff check experiments scripts tests || true
    mypy experiments scripts tests || true
    python3 scripts/verify_lrat.py
    python3 scripts/check_reuse.py

[windows]
lint:
    ruff check experiments scripts tests; if ($LASTEXITCODE -ne 0) { Write-Host "ruff exited $LASTEXITCODE (report-only)" }
    mypy experiments scripts tests; if ($LASTEXITCODE -ne 0) { Write-Host "mypy exited $LASTEXITCODE (report-only)" }
    python scripts/verify_lrat.py
    python scripts/check_reuse.py

# Score this repository against Build Standard v1.1.0 & Build Pipeline Models v1.0.0 (report-only)
[unix]
audit *ARGS:
    bash scripts/audit-repo.sh . {{ARGS}}
    python3 scripts/pipeline-audit.py

[windows]
audit *ARGS:
    pwsh -NoProfile -File scripts/Audit-Repo.ps1 -Path . {{ARGS}}
    python scripts/pipeline-audit.py

# Run all 4 exact-arithmetic and SAT companion experiments
experiments:
    {{py}} experiments/exp1_digit_sum_dichotomy.py
    {{py}} experiments/exp2_three_register_breakthrough.py
    {{py}} experiments/exp3_bilinear_and_balanced.py
    {{py}} experiments/exp4_boolean_mc_companion.py

# Generate deterministic vector PDF figures
figures:
    {{py}} scripts/make_figures.py

# Compile AMS-LaTeX white paper with Tectonic
[unix]
paper:
    bash scripts/run_all.sh paper

[windows]
paper:
    pwsh -NoProfile -File scripts/run_all.ps1 -Task paper

# Clean clone to headline results (Lean + experiments + tests + figures + paper + LRAT/REUSE/SHA-256/TSA)
[unix]
reproduce:
    bash scripts/run_all.sh all

[windows]
reproduce:
    pwsh -NoProfile -File scripts/run_all.ps1 -Task all

# Copy compiled PDF to dist/
dist: paper
    {{py}} -c "import shutil; shutil.copy2('paper/build/main.pdf', 'dist/Donahue_2026_catalytic_register_frontiers.pdf')"

# Push an offsite mirror (configure remote 'backup' first; see docs/operations.md)
mirror:
    git push backup --mirror

# Remove local build intermediates (cross-platform & bracket-path safe)
clean:
    {{py}} -c "import pathlib, shutil; [shutil.rmtree(p, ignore_errors=True) for p in ('lean/.lake', 'paper/build', '.pytest_cache', '.mypy_cache', '.ruff_cache', '.hypothesis') if pathlib.Path(p).exists()]"
