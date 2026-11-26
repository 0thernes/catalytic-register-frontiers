<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Clean-Room Replication Guide (`REPLICATION.md`)

Every Lean 4.35 formal proof, non-vacuity witness, exact-arithmetic experiment, `pytest` / Hypothesis / mutant / SAT-equivalence test, deterministic vector PDF figure, and frozen AMS-LaTeX manuscript in `catalytic-register-frontiers` reproduces end-to-end from scratch.

## Prerequisites

- **Lean 4.35.0** via `elan` (`leanprover/lean4:v4.35.0`, pinned in `lean/lean-toolchain`). Zero Mathlib dependency; builds fully offline once the toolchain is installed.
- **Python 3.13** with pinned packages in `requirements.lock.txt` (`pytest==9.2.0`, `hypothesis==6.170.17`, `matplotlib==3.11.2`, `numpy==2.5.5`, `scipy==1.18.1`, `ruff==0.17.6`, `mypy==2.4.1`).
- **CaDiCaL 2.1.2** (bundled with Lean 4.35.0 at `<toolchain>/bin/cadical[.exe]`, or set `CADICAL_BIN`).
- **Tectonic** (`tectonic -X compile`) for compiling `paper/main.tex`.

## 1. One-Command Verification (Windows PowerShell, Linux/macOS Bash, or `just`)

> **Bracket-Path Safety Note:** On Windows paths containing `[...]`, always pass `-LiteralPath` to PowerShell file cmdlets and run `pytest` repo-relative (`tests/test_all.py`).

```bash
# Windows PowerShell
pwsh -NoProfile -File scripts/run_all.ps1 -Task all

# Linux / macOS POSIX shell
bash scripts/run_all.sh all

# Cross-platform via justfile
just reproduce
```

Individual stages: `lean`, `experiments`, `tests`, `figures`, `paper`, `audit` (verifies 8/8 LRAT proofs, 100% REUSE/SPDX, offline citations, and `MANIFEST.sha256`).

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
lake env leanexport Solution -- \
  Catalytic.Solution.prove_all_catalytic_theorems \
  Catalytic.NonVacuity.nonvac_all_hypotheses > /tmp/catalytic_solution.ndjson
lake env con-leche --verified /tmp/catalytic_solution.ndjson
lake env con-ron --verified /tmp/catalytic_solution.ndjson

# On Linux (with bwrap installed), run Lean 4.35's bundled sandboxed multi-kernel checker:
lake check --paranoid
```

### B. Exact-Arithmetic Experiments, Pytest, Hypothesis, & Linters

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.lock.txt

python experiments/exp1_digit_sum_dichotomy.py
python experiments/exp2_three_register_breakthrough.py
python experiments/exp3_bilinear_and_balanced.py
python experiments/exp4_boolean_mc_companion.py

pytest -v tests/test_all.py
ruff check experiments scripts tests
mypy experiments scripts tests
python scripts/check_citations.py --offline
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

### E. Cryptographic Provenance & Build Standard Audit

```bash
sha256sum -c MANIFEST.sha256
pwsh -NoProfile -File scripts/Audit-Repo.ps1 -Path .
```

## 3. Replication Log (Build Standard B44)

Independent external human replications (pass or fail) are welcome via `.github/ISSUE_TEMPLATE/question.yml` (label: `replication`). Self-replications are explicitly marked as such and do not substitute for external replication.

| Date | Replicator | Scope | Environment | Outcome | Notes |
|---|---|---|---|---|---|
| 2026-11-23 | Alexander S. Donahue (author — clean-room self-replication) | Clean `.lake` + 6 kernels + `exp1`–`exp4` + `pytest`/Hypothesis/mutant/SAT + Tectonic + standalone `arxiv_submission.tar.gz` + `MANIFEST.sha256` | Windows 11 x64, Lean 4.35.0, Python 3.13.12, CaDiCaL 2.1.2, Tectonic | **PASS (self)** | Zero warnings, 6/6 kernels PASS, 100% SHA-256 match. External second-person replication still open. |
| 2026-11-24 | Alexander S. Donahue (author — Pass 6 full self-replication) | 14 Lean modules (19 theorems + NonVacuity = 21 decls, incl. `T3h` 4-register powering) across 6 kernels (`con-*` 3,506 decls, `nanoda_bin` 3,819 decls) + 8/8 LRAT + `pytest` + `ruff`/`mypy` + 0-warning PDF & clean-room arXiv tarball + `MANIFEST.sha256` + DigiCert RFC 3161 TSA | Windows 11 x64 + Git Bash POSIX audit, Lean 4.35.0, Python 3.13.12, CaDiCaL 2.1.2, Tectonic, OpenSSL | **PASS (self)** | All 6/6 kernels PASS, 0 warnings, 100% REUSE & SHA-256, DigiCert `Verification: OK`, `Audit-Repo.ps1` & `audit-repo.sh` parity 98.4%. External second-person replication still open. |
| 2026-11-24 | Alexander S. Donahue (author — Pass 7 full self-replication) | 14 Lean modules (8,036 lines; 20 theorems + `prove_all` + `NonVacuity` = 22 decls, incl. `T3i` pointwise product-ring streaming frequency moments $F_D$) across 6 kernels (`con-*` 3,523 decls, `nanoda_bin` 3,836 decls) + 8/8 LRAT + 20/20 `pytest` (incl. SVG XML/overflow, $D_4..D_9$ prime-factorization, and Table 3/4 coefficient guards) + `ruff`/`mypy` + 0-warning PDF & clean-room arXiv tarball + `MANIFEST.sha256` + DigiCert RFC 3161 TSA | Windows 11 x64 + Git Bash POSIX audit, Lean 4.35.0, Python 3.13.12, CaDiCaL 2.1.2, Tectonic, OpenSSL | **PASS (self)** | All 6/6 kernels PASS, 0 warnings, 20/20 pytest PASS, 100% REUSE & SHA-256, DigiCert `Verification: OK`, `Audit-Repo.ps1` & `audit-repo.sh` parity 98.4%. External second-person replication still open. |
| 2026-11-24 | Alexander S. Donahue (author — Pass 8 full self-replication) | 14 Lean modules (8,069 lines; 20 theorems + `prove_all` + `NonVacuity` incl. `Fin 3 → ModP 13` `nonvac_T3i_witness` = 22 decls) across 6 kernels (`con-*` 3,525 decls, `nanoda_bin` 3,838 decls) + strict monotonic-ID 8/8 LRAT + conflict-strict 148/148 REUSE + 29-component SBOM + bit-for-bit LF-deterministic `exp1`–`exp4` + 21/21 `pytest` + `ruff`/`mypy` + 0-warning PDF & clean-room arXiv tarball + `MANIFEST.sha256` + DigiCert RFC 3161 TSA | Windows 11 x64 + Git Bash POSIX audit, Lean 4.35.0, Python 3.13.12, CaDiCaL 2.1.2, Tectonic, OpenSSL | **PASS (self)** | All 6/6 kernels PASS, 0 warnings, 21/21 pytest PASS, 0-diff bit-for-bit `exp1`–`exp4` replay, 100% conflict-free REUSE & SHA-256, DigiCert `Verification: OK`, `Audit-Repo.ps1` & `audit-repo.sh` parity 98.4%. External second-person replication still open. |
| 2026-11-24 | Alexander S. Donahue (author — Pass 9 cold-start clean self-replication) | Wiped `lean/.lake` true cold-start clean build (**56.6 s**, 17/17 jobs, 0 warnings) + 6/6 kernels (`con-*` 3,525 decls, `nanoda_bin` 3,838 decls) + exact non-commutative Cor. 5.4 matrix-lift test + strict HTML5/WCAG & schema audit + 22/22 `pytest` + `ruff`/`mypy` + 8/8 strict LRAT + 148/148 conflict-free REUSE + 0-warning 15p PDF & clean-room arXiv tarball + `MANIFEST.sha256` + DigiCert RFC 3161 TSA | Windows 11 x64 + Git Bash POSIX audit, Lean 4.35.0, Python 3.13.12, CaDiCaL 2.1.2, Tectonic, OpenSSL | **PASS (self)** | Cold-start clean `.lake` build 56.6 s (< 60 s), 6/6 kernels PASS, 22/22 pytest PASS, 0 warnings, 100% REUSE & SHA-256, DigiCert `Verification: OK`, `Audit-Repo.ps1` & `audit-repo.sh` parity 98.4%. External second-person replication still open. |
| 2026-11-25 | Alexander S. Donahue (author — Pass 11 3-cycle audit & Adaptive Forking PWA self-replication) | 14 core Lean modules (8,151 lines, max 1,364) + `PalomarChallenge`/`PalomarSolution` across 5 distinct kernel implementations in 6 runs (`Solution` 3,544 decls, `PalomarSolution` 3,502 decls) + 22/22 axioms + 8/8 strict LRAT + 155/155 conflict-free REUSE + 24/24 `pytest` (incl. live Node.js verbatim Lean→JS Adaptive Forking differential & 200-trial fuzzer checks) + `ruff`/`mypy` + 0-warning 15p PDF & clean-room arXiv tarball + `MANIFEST.sha256` + DigiCert RFC 3161 TSA | Windows 11 x64, Lean 4.35.0, Python 3.13.12, Node.js, CaDiCaL 2.1.2, Tectonic, OpenSSL | **PASS (self)** | 19/19 Lean default jobs (0 warnings), 5 distinct kernels / 6 runs PASS on both `Solution` & `PalomarSolution`, 24/24 pytest PASS, 0 warnings, 100% REUSE & SHA-256, DigiCert `Verification: OK`, Build Standard 100.0% (62/62). External second-person replication still open. |
| 2026-11-25 | Alexander S. Donahue (author — Pass 12 adversarial hardening & PWA v1.2 self-replication) | Reproducible `r=4` triangular frontier in `exp2` + strict RAT LRAT + Node-24 CI + `catalytic-engine.js` v1.2.0 (exact ring invertibility, composite rings $\mathbb{Z}/m\mathbb{Z}$, `p=137` dodge, SHA-256 Byte-Vault, live SVG Fork-DAG, 6-mode fuzzer) + 25/25 `pytest` + 156/156 conflict-free REUSE + 0-warning 15p PDF & clean-room arXiv tarball + `MANIFEST.sha256` + DigiCert RFC 3161 TSA | Windows 11 x64 + GitHub Actions Linux & Windows, Lean 4.35.0, Python 3.13.12, Node.js, CaDiCaL 2.1.2, Tectonic, OpenSSL | **PASS (self)** | 25/25 pytest PASS, 0 TeX warnings (15p), 156/156 REUSE, DigiCert `Verification: OK`, Build Standard 100.0% (62/62). External second-person replication still open. |
| 2026-11-25 | Alexander S. Donahue (author — Pass 13 minimal TeX preamble & Adaptive Forking v1.3 self-replication) | Minimal arXiv TeX preamble (`-mathtools/-multirow/-cleveref`) + `catalytic-engine.js` v1.3.0 universal Node.js CLI (`plan`/`run`/`vault`/`bench`/`fuzz`) & `runDeviceBenchmark()` + PWA v1.3 (auto-run 64 KiB SHA-256 Byte-Vault, Play/Pause/Scrub Register Animator, non-trivial `T2` `k=5`, `p=0` dispatch) + 26/26 `pytest` + 8/8 strict LRAT + 156/156 conflict-free REUSE + 0-warning 15p PDF & clean-room arXiv tarball + `MANIFEST.sha256` + DigiCert RFC 3161 TSA | Windows 11 x64 + POSIX `audit-repo.sh` + GitHub Actions Linux & Windows, Lean 4.35.0, Python 3.13.12, Node.js, CaDiCaL 2.1.2, Tectonic, OpenSSL | **PASS (self)** | 26/26 pytest PASS (incl. live CLI subcommands), 0 TeX warnings (15p), 156/156 REUSE, DigiCert `Verification: OK`, `Audit-Repo.ps1` & `audit-repo.sh` parity 100.0% (62/62). External second-person replication still open. |
| 2026-11-25 | Alexander S. Donahue (author — Pass 14 full-TOC forensic hardening & Adaptive Forking v1.4 self-replication) | Large-$N$ `T1` & all-base optimality + arbitrary-`BigInt` Frobenius/`T1` execution + winner-first DAG + `computeAdaptiveHorizon()` + `verifyCertificate()` + dual positional/flag CLI (`horizon`/`verify`) + local-safe `sw.js` + non-clobbering PWA v1.4 + Tab 2 live telemetry sparkline + bracket-safe `verify_lrat.py` + 27/27 `pytest` + 8/8 strict LRAT + 156/156 conflict-free REUSE + 0-warning 15p PDF & clean-room arXiv tarball + `MANIFEST.sha256` + DigiCert RFC 3161 TSA | Windows 11 x64 + POSIX `audit-repo.sh` + GitHub Actions Linux & Windows, Lean 4.35.0, Python 3.13.12, Node.js, CaDiCaL 2.1.2, Tectonic, OpenSSL | **PASS (self)** | 27/27 pytest PASS (0 torture-test bugs), 0 TeX warnings (15p), 156/156 REUSE, DigiCert `Verification: OK`, `Audit-Repo.ps1` & `audit-repo.sh` parity 100.0% (62/62). External second-person replication still open. |
| 2026-11-25 | Alexander S. Donahue (author — Pass 15 hostile planner-executor, CSP & Auto-Pilot v1.5 self-replication) | `prog9_x15` dispatch + 100% JSON-safe `planAdaptiveFork` + large-$N$ hybrid planner-executor alignment + strict hex-digest tamper rejection + non-blocking `execCatalyticByteVaultAsync` + zero-exfiltration CSP + Live Closed-Loop Adaptive Auto-Pilot PWA v1.5 + live `10/10` online citations + 28/28 `pytest` + 8/8 strict LRAT + 156/156 REUSE + 0-warning 15p PDF & clean-room arXiv tarball + `MANIFEST.sha256` + DigiCert RFC 3161 TSA | Windows 11 x64 + POSIX `audit-repo.sh` + GitHub Actions Linux & Windows, Lean 4.35.0, Python 3.13.12, Node.js, CaDiCaL 2.1.2, Tectonic, OpenSSL | **PASS (self)** | 28/28 pytest PASS (0 JS planner-executor/tamper bugs), live 10/10 online citations PASS, 0 TeX warnings (15p), 156/156 REUSE, DigiCert `Verification: OK`, `Audit-Repo.ps1` & `audit-repo.sh` parity 100.0% (62/62). External second-person replication still open. |
| 2026-11-25 | Alexander S. Donahue (author — Pass 16 `cor:matpow` parity, bit-determinism & portable proof exchange v1.6 self-replication) | Exact $\mu_\delta$ matrix invertibility ($p > 7$ for `prog5_x7`, $p > 5$ for `prog4_x5`) + bit-identical SHA-256 replay of `exp1`–`exp3`, `fig1`–`fig3` & live `VerifyAxioms.lean` + CLI `stream` & `vault --stdin` + portable external cert file verifier & battery-safe `visibilitychange` pause in PWA v1.6 + 29/29 `pytest` + 8/8 strict LRAT + 156/156 REUSE + 0-warning 15p PDF & clean-room arXiv tarball + `MANIFEST.sha256` + DigiCert RFC 3161 TSA | Windows 11 x64 + POSIX `audit-repo.sh` + GitHub Actions Linux & Windows, Lean 4.35.0, Python 3.13.12, Node.js, CaDiCaL 2.1.2, Tectonic, OpenSSL | **PASS (self)** | 29/29 pytest PASS (0 JS/matrix bugs), bit-identical replay of all JSONs/PDF figures/axioms, 0 TeX warnings (15p), 156/156 REUSE, DigiCert `Verification: OK`, `Audit-Repo.ps1` & `audit-repo.sh` parity 100.0% (62/62). External second-person replication still open. |
| 2026-11-25 | Alexander S. Donahue (author — Pass 17 hostile `NaN`/bounds sanitization, Watch/Phone preview & printable HTML audit report v1.7 self-replication) | `safeInt` sanitization & structured `verifyCertificate` error handling in `catalytic-engine.js` v1.7.0 + Watch 320px/Phone 390px preview switcher, `CSP: Zero-Exfiltration` badge, printable HTML report export & `D <= 500` streaming bound in PWA v1.7 + 30/30 `pytest` + 8/8 strict LRAT + 156/156 REUSE + 0-warning 15p PDF & clean-room arXiv tarball + `MANIFEST.sha256` + DigiCert RFC 3161 TSA | Windows 11 x64 + POSIX `audit-repo.sh` + GitHub Actions Linux & Windows, Lean 4.35.0, Python 3.13.12, Node.js, CaDiCaL 2.1.2, Tectonic, OpenSSL | **PASS (self)** | 30/30 pytest PASS (0 hostile `NaN`/integer/uncaught-exception bugs), 0 TeX warnings (15p), 156/156 REUSE, DigiCert `Verification: OK`, `Audit-Repo.ps1` & `audit-repo.sh` parity 100.0% (62/62). External second-person replication still open. |
| 2026-11-25 | Alexander S. Donahue (author — Pass 18 648-pair differential parity, null-safety, CLI `--flag=val`/`selfcheck` & Visual Byte-Diff Matrix v1.8 self-replication) | 648-case `(N, p)` planner-vs-executor differential audit + 0 final-pass TeX `Overfull \hbox` + null-safe `opts` & strict $2\times 2$ matrix / $d \le 64$ guards + CLI `--flag=val` & `selfcheck` + Visual Catalytic Byte-Diff Matrix & 1-tap Tamper Simulation in PWA v1.8 + 31/31 `pytest` + 8/8 strict LRAT + 156/156 REUSE + 0-warning 15p PDF & clean-room arXiv tarball + `MANIFEST.sha256` + DigiCert RFC 3161 TSA | Windows 11 x64 + POSIX `audit-repo.sh` + GitHub Actions Linux & Windows, Lean 4.35.0, Python 3.13.12, Node.js, CaDiCaL 2.1.2, Tectonic, OpenSSL | **PASS (self)** | 31/31 pytest PASS (0 differential/null/CLI bugs), 0 TeX warnings/overfulls (15p), 156/156 REUSE, DigiCert `Verification: OK`, `Audit-Repo.ps1` & `audit-repo.sh` parity 100.0% (62/62). External second-person replication still open. |
