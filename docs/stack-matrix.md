<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Stack Selection & Weighted Decision Matrix (`docs/stack-matrix.md`)

> Pipeline artifact `P4.F1`. Applies the Build Pipeline Models boring-technology bias (`P4.03`) and build-vs-buy rationale (`P4.04`) to every tool layer.

## 1. Formal Verification Proof Assistant (Weights: Kernel Trust 35%, Build Speed 25%, Dependency Stability 25%, External Checkers 15%)

| Candidate | Kernel Trust (35%) | Build Speed (25%) | Stability (25%) | External Checkers (15%) | Weighted Score | Decision |
|---|---|---|---|---|---|---|
| **Lean 4.35.0 (Zero-Mathlib)** | 5 | 5 (< 60 s clean, 56.6 s measured) | 5 (0 external pkgs) | 5 (5 kernels / 6 runs incl. `nanoda`, `con-leche`, `con-ron`) | **5.00** | **Selected (ADR 0001)** |
| Lean 4 + Mathlib4 | 5 | 2 (multi-GB cache) | 3 (frequent API churn) | 4 (huge export graph) | 3.60 | Rejected for core artifact |
| Coq / Rocq | 5 | 4 | 4 | 3 | 4.20 | Secondary alternative |

## 2. Companion SAT Solver & Proof Format (Weights: Proof Certification 40%, Determinism 30%, Zero Extra Install 30%)

| Candidate | Proof Certification (40%) | Determinism (30%) | Zero Extra Install (30%) | Weighted Score | Decision |
|---|---|---|---|---|---|
| **CaDiCaL 2.1.2 (Bundled with Lean 4.35) + ASCII LRAT** | 5 (native `--lrat=true`) | 5 | 5 (already in toolchain) | **5.00** | **Selected** |
| Z3 / PySAT | 3 (no native LRAT) | 4 | 2 (extra wheel dep) | 3.00 | Rejected |

## 3. Manuscript Typesetting & Dependency Blueprint

| Layer | Selected Tool | Rejected Alternative | Rationale |
|---|---|---|---|
| **LaTeX Compiler** | **Tectonic** (single binary, deterministic bundle) | Full 4 GB TeX Live install | Self-contained, fast, 0-warning compilation; clean-room arXiv tarball verified separately. |
| **Theorem Blueprint** | **Static zero-dependency HTML (`docs/index.html`)** | `leanblueprint` (plasTeX + Graphviz + Mathlib hooks) | For 14 zero-Mathlib `.lean` modules, a static HTML/SVG dependency graph and declaration map has zero build fragility and deploys cleanly on GitHub Pages (recorded per Playbook #11). |
| **Python Computational Suite** | **Exact stdlib (`int`, `fractions.Fraction`) + `pytest`/`hypothesis`/`ruff`/`mypy`** | NumPy/SciPy floating-point solvers for proofs | Zero rounding error in mathematical verification; floats confined strictly to matplotlib visualization (`scripts/make_figures.py`). |
