# SPDX-License-Identifier: Apache-2.0
# Task runner (https://just.systems). Run `just` to list recipes.
# No recipe installs git hooks or gates a commit or push (Build Standard R1).

set shell := ["bash", "-euo", "pipefail", "-c"]
set windows-shell := ["pwsh", "-NoProfile", "-Command"]

# List available recipes
default:
    @just --list

# Verify Lean 4.35.0 toolchain and install pinned Python dependencies
setup:
    cd lean && lean --version
    python -m pip install -r requirements.lock.txt

# Build zero-Mathlib Lean 4.35 proofs, check axioms, and replay through paranoid kernel
build:
    cd lean && lake build
    cd lean && lake env lean VerifyAxioms.lean
    cd lean && lake env leanchecker Solution
    cd lean && lake env leanchecker-paranoid Solution

# Run full pytest suite (exact arithmetic, Hypothesis property tests, mutant checks, SAT equivalence)
test:
    pytest -v tests/test_all.py

# Run static analysis, LRAT certificate check, and strict type checks (report-only)
lint:
    ruff check experiments scripts tests || true
    mypy experiments scripts tests || true
    python scripts/verify_lrat.py

# Score this repository against Build Standard v1.1.0 & Build Pipeline Models v1.0.0 (report-only)
audit *ARGS:
    pwsh -NoProfile -File scripts/Audit-Repo.ps1 -Path . {{ARGS}}
    python scripts/pipeline-audit.py

# Run all 4 exact-arithmetic and SAT companion experiments
experiments:
    python experiments/exp1_digit_sum_dichotomy.py
    python experiments/exp2_three_register_breakthrough.py
    python experiments/exp3_bilinear_and_balanced.py
    python experiments/exp4_boolean_mc_companion.py

# Generate deterministic vector PDF figures
figures:
    python scripts/make_figures.py

# Compile AMS-LaTeX white paper with Tectonic
paper:
    cd paper && tectonic -X compile main.tex --outdir build --keep-intermediates

# Clean clone to headline results (Lean + experiments + tests + figures + paper + SHA-256)
reproduce: build experiments test figures paper
    sha256sum -c MANIFEST.sha256

# Build release artifacts in dist/
dist: paper
    cp paper/build/main.pdf dist/Donahue_2026_catalytic_register_frontiers.pdf

# Push an offsite mirror (configure remote 'backup' first; see docs/operations.md)
mirror:
    git push backup --mirror

# Remove local build intermediates
clean:
    rm -rf lean/.lake paper/build .pytest_cache .mypy_cache .ruff_cache .hypothesis
