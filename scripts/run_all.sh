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
    if grep -rnE --exclude-dir=.lake --exclude=PalomarChallenge.lean '\b(sorry|admit|native_decide|implemented_by|unsafe)\b|^\s*(private\s+|protected\s+|local\s+|scoped\s+|noncomputable\s+)*axiom\b|@\[extern' .; then
      echo "FORBIDDEN TOKEN FOUND IN PROOF MODULES!" >&2
      exit 1
    fi
    lake build
    TMP_AX="$(mktemp)"
    trap 'rm -f "$TMP_AX"' EXIT
    lake env lean VerifyAxioms.lean | tr -d '\r' > "$TMP_AX"
    cat "$TMP_AX"
    test -s "$TMP_AX"
    diff -u ../results/lean_axioms.txt "$TMP_AX"
    if grep -qE 'sorryAx|_native|Lean\.ofReduceBool|Lean\.trustCompiler' "$TMP_AX"; then
      echo "UNPERMITTED AXIOM DETECTED!" >&2
      exit 1
    fi
    "$PYTHON" - "$TMP_AX" <<'PYEOF'
import pathlib, re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
lines = [ln.strip() for ln in pathlib.Path(sys.argv[1]).read_text(encoding="utf-8").splitlines() if ln.strip()]
assert len(lines) == 22, f"Expected 22 audited axiom lines, got {len(lines)}"
for ln in lines:
    if ln.endswith("does not depend on any axioms"):
        continue
    m = re.match(r"^'[^']+' depends on axioms: \[([^\]]+)\]$", ln)
    assert m, f"Unrecognized axiom line: {ln}"
    extra = {tok.strip() for tok in m.group(1).split(",") if tok.strip()} - allowed
    assert not extra, f"Disallowed axioms {extra} in: {ln}"
print(f"Strict 3-axiom allowlist verified on {len(lines)}/22 declarations.")
PYEOF
    lake env leanchecker --fresh Solution
    lake env leanchecker-paranoid Solution
    if lake env sh -c 'command -v con-leche >/dev/null 2>&1 && command -v con-ron >/dev/null 2>&1'; then
      TMP_EXP="$(mktemp)"
      trap 'rm -f "$TMP_AX" "$TMP_EXP"' EXIT
      lake env leanexport Solution -- \
        Catalytic.Solution.prove_all_catalytic_theorems \
        Catalytic.NonVacuity.nonvac_all_hypotheses > "$TMP_EXP"
      lake env con-leche --verified "$TMP_EXP"
      lake env con-ron --verified "$TMP_EXP"
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
  step "Verify LRAT UNSAT proofs, REUSE/SPDX, citations, MANIFEST.sha256, and RFC 3161 TSA"
  (
    cd "$REPO"
    "$PYTHON" scripts/verify_lrat.py
    "$PYTHON" scripts/check_reuse.py
    "$PYTHON" scripts/check_citations.py --offline
    sha256sum -c MANIFEST.sha256 --quiet && echo "MANIFEST_SHA256_VERIFIED: all checksums match."
    if command -v openssl >/dev/null 2>&1 && [ -f provenance/MANIFEST.sha256.tsr ]; then
      if [ -f /etc/ssl/certs/ca-certificates.crt ]; then
        openssl ts -verify -data MANIFEST.sha256 -in provenance/MANIFEST.sha256.tsr -CAfile /etc/ssl/certs/ca-certificates.crt
      elif [ -d /etc/ssl/certs ]; then
        openssl ts -verify -data MANIFEST.sha256 -in provenance/MANIFEST.sha256.tsr -CApath /etc/ssl/certs
      elif [ -f /usr/ssl/certs/ca-bundle.crt ]; then
        openssl ts -verify -data MANIFEST.sha256 -in provenance/MANIFEST.sha256.tsr -CAfile /usr/ssl/certs/ca-bundle.crt
      else
        openssl ts -verify -data MANIFEST.sha256 -in provenance/MANIFEST.sha256.tsr
      fi
    fi
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
    run_audit
    run_figures
    run_paper
    ;;
  *)
    echo "Usage: $0 [all|lean|experiments|tests|figures|paper|audit]" >&2
    exit 2
    ;;
esac

printf '\nALL REQUESTED TASKS COMPLETED SUCCESSFULLY (%s).\n' "$TASK"
