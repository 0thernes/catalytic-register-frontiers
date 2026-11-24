<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Environment & Configuration (`docs/configuration.md`)

This repository requires **zero API keys, zero network credentials, and zero external databases** for local builds, Lean verification, Python exact arithmetic, figure generation, or PDF compilation.

## Environment Variables (`.env.example`)

| Variable | Default | Purpose |
|---|---|---|
| `CADICAL_BIN` | Auto-detected from Lean 4.35.0 toolchain (`~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/cadical[.exe]`) | Explicit path to the CaDiCaL 2.1.2 binary used by `experiments/exp4_boolean_mc_companion.py` |
| `PYTHONUTF8` | `1` | Ensures UTF-8 I/O on Windows consoles |
| `SOURCE_DATE_EPOCH` | `1795420800` (optional) | Deterministic timestamp metadata for reproducible archival packaging |

## Pinned Toolchains & Lockfiles

| Component | Pin File | Pinned Version |
|---|---|---|
| Lean 4 toolchain & external kernels | `lean/lean-toolchain`, `lean/lake-manifest.json` | `leanprover/lean4:v4.35.0` (zero external Lake dependencies) |
| Python environment | `pyproject.toml`, `requirements.lock.txt` | Python 3.13.12 (`pytest==9.2.0`, `hypothesis==6.170.17`, `matplotlib==3.11.2`, `numpy==2.5.5`, `scipy==1.18.1`, `ruff==0.17.6`, `mypy==2.4.1`) |
| LaTeX engine | `paper/main.tex` | Tectonic (`tectonic -X compile main.tex --outdir build --keep-intermediates`) |

## Windows PowerShell Bracket-Path Safety

If the repository is cloned into a directory path containing literal square brackets (e.g., `Z:\[Vibe Coded (AI)]\ANTIGRAVITY\catalytic-register-frontiers`), PowerShell treats `[...]` as wildcard syntax unless `-LiteralPath` is passed to file cmdlets. All scripts in `scripts/` use `-LiteralPath` and invoke `pytest` with repo-relative paths (`tests/test_all.py`).
