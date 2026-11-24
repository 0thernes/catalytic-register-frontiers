#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# End-to-end POSIX (Linux / macOS) reproducible verification orchestrator for
# catalytic-register-frontiers. Mirrors scripts/run_all.ps1.
# Usage: ./scripts/run_all.sh [all|lean|experiments|tests|figures|paper|audit]

set -euo pipefail

TASK="${1:-all}"
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON="${PYTHON:-python3}"

step() {
  printf '\n=== [%s] ===\n' "$1"
}

run_lean() {
  step "Lean 4.35 lake build + VerifyAxioms + leanchecker-paranoid"
  (
    cd "$REPO/lean"
    lake build
    lake env lean VerifyAxioms.lean
    lake env leanchecker Solution
    lake env leanchecker-paranoid Solution
    if command -v con-leche >/dev/null 2>&1 && command -v con-ron >/dev/null 2>&1; then
      TMP_EXP="$(mktemp)"
      trap 'rm -f "$TMP_EXP"' EXIT
      lake env leanexport Solution -- \
        Catalytic.Solution.prove_all_catalytic_theorems \
        Catalytic.NonVacuity.nonvac_all_hypotheses > "$TMP_EXP"
      con-leche --verified "$TMP_EXP"
      con-ron --verified "$TMP_EXP"
    fi
  )
}

run_experiments() {
  step "Run all 4 exact-arithmetic and SAT companion experiments"
  (
    cd "$REPO"
    "$PYTHON" experiments/exp1_digit_sum_dichotomy.py
    "$PYTHON" experiments/exp2_three_register_breakthrough.py
    "$PYTHON" experiments/exp3_bilinear_and_balanced.py
    "$PYTHON" experiments/exp4_boolean_mc_companion.py
  )
}

run_tests() {
  step "Pytest verification suite (exact, Hypothesis, mutant, brute-force SAT, LRAT, REUSE)"
  (
    cd "$REPO"
    "$PYTHON" -m pytest -v tests/test_all.py
  )
}

run_figures() {
  step "Generate 3 deterministic vector PDF figures"
  (
    cd "$REPO"
    "$PYTHON" scripts/make_figures.py
  )
}

run_paper() {
  step "Compile AMS-LaTeX white paper with Tectonic"
  (
    cd "$REPO/paper"
    mkdir -p build
    tectonic -X compile main.tex --outdir build --keep-intermediates
  )
}

run_audit() {
  step "Verify LRAT UNSAT proofs, REUSE/SPDX, citations, and MANIFEST.sha256"
  (
    cd "$REPO"
    "$PYTHON" scripts/verify_lrat.py
    "$PYTHON" scripts/check_reuse.py
    "$PYTHON" scripts/check_citations.py --offline
    sha256sum -c MANIFEST.sha256 --quiet && echo "MANIFEST_SHA256_VERIFIED: all checksums match."
  )
}

case "$TASK" in
  lean)        run_lean ;;
  experiments) run_experiments ;;
  tests)       run_tests ;;
  figures)     run_figures ;;
  paper)       run_paper ;;
  audit)       run_audit ;;
  all)
    run_lean
    run_tests
    run_figures
    run_paper
    run_audit
    ;;
  *)
    echo "Usage: $0 [all|lean|experiments|tests|figures|paper|audit]" >&2
    exit 2
    ;;
esac

printf '\nALL REQUESTED TASKS COMPLETED SUCCESSFULLY (%s).\n' "$TASK"
