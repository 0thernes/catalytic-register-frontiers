<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Positive-Characteristic Dichotomy and Optimal Three-Register Exponents in Passive Catalytic Register Programs

**Author:** Alexander S. Donahue (Independent Researcher, Spokane, WA, USA · ORCID [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648) · `0_0@0thernes.art`)
**Version:** `1.0.0` (2026-11-23) · **Licenses:** Apache-2.0 (code & Lean) · CC-BY-4.0 (paper, docs, figures)
**Frozen White Paper:** [`dist/Donahue_2026_catalytic_register_frontiers.pdf`](dist/Donahue_2026_catalytic_register_frontiers.pdf) (13 pages, AMS-LaTeX, zero warnings)

> **Verification & Epistemic Status:** All 12 formal theorem and corollary statements (`T1`, `T1a`–`T1d`, `T2`, `T3a`–`T3e`, `T4`) are machine-checked from first principles in **zero-Mathlib Lean 4.35.0** and pass **six independent kernel runs across five implementations** (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin`) with strict 3-axiom allowlist `[propext, Classical.choice, Quot.sound]` and zero forbidden tokens. This preprint has **not** undergone external peer review; see [`CLAIMS.md`](CLAIMS.md) and [`LIMITATIONS.md`](LIMITATIONS.md) for explicit verification tiers and open questions.

---

## Core Mathematical Discoveries

This repository answers two structural open questions left by Antoine Vinciguerra's operator analysis of passive-output catalytic register programs ([`arXiv:2609.18692`](https://arxiv.org/abs/2609.18692), September 2026), unifies them with an optimal zero-workspace bilinear multilinear product, and contrasts catalytic nonlinear cancellation against Boolean multiplicative complexity ([`arXiv:2608.30238`](https://arxiv.org/abs/2608.30238), Morse 2026; Boyar–Find, TCS 2018):

1. **Theorem T1 — Complete Base-$p$ Digit-Sum Dichotomy for $\mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t)$** ([`DigitSumDichotomy.lean`](lean/Catalytic/DigitSumDichotomy.lean)):
   For every prime $p$, every budget $t \ge 1$, and every univariate polynomial $f(x) = \sum_{d \ge 0} \alpha_d x^d \in \mathbb{F}_p[x]$:
   $$f \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t) \quad \Longleftrightarrow \quad \forall\, d \ge 2 \text{ with } \alpha_d \neq 0,\;\; s_p(d) \le \min(p - 1,\; t - 1).$$
   - **T1a:** Total collapse of Vinciguerra's characteristic-0 lower bounds (Theorems 3.2, 3.3, 3.5) in every prime characteristic: $x^{p^m} \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, 2)$ for all $m \ge 0$ ($D_{2,\mathbb{F}_p}^{\mathrm{pass}}(2) = +\infty$).
   - **T1b:** Exact $\mathbb{F}_2$ saturation: $x^3 \notin \mathrm{RP}_{\mathbb{F}_2}^{\mathrm{pass}}(2, t)$ for **all** $t \ge 0$.
   - **T1c:** Universal impossibility threshold: whenever $s_p(d) \ge p$, $x^d \notin \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t)$ for all $t \ge 1$.
   - **T1d:** Characteristic-0 recovery: whenever $2 \le d < p$, $x^d \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t) \iff t \ge d + 1$.

2. **Theorem T2 — Strictly Bilinear 2-Access Frobenius Collapse over Characteristic 2** ([`BilinearFrobenius.lean`](lean/Catalytic/BilinearFrobenius.lean)):
   Even restricting basic instructions strictly to bilinear updates $R_i \leftarrow R_i + R_j R_\ell$ ($j, \ell \neq i$, passive output $R_0$), for every $k \ge 1$ and every commutative characteristic-2 ring $R$, $x^{2^k}$ is cleanly computed in $k + 1$ registers, $4k - 2$ bilinear ops, and **exactly 2 input accesses**.

3. **Theorem T3 — Strict Improvement Over Vinciguerra's 3-Register Powering, Streaming, and Matrix-Powering Exponent** ([`ThreeRegisterBreakthrough.lean`](lean/Catalytic/ThreeRegisterBreakthrough.lean)):
   Using literal Definition 2.2 Pascal-row shear loops with exact integer coefficients:
   - $x^7 \in \mathrm{RP}_K^{\mathrm{pass}}(3, 5)$ ($\mathrm{char}(K) \neq 2, 3$, $D_5 = 576$, $\log_7 5 \approx 0.827087$);
   - $x^9 \in \mathrm{RP}_K^{\mathrm{pass}}(3, 6)$ ($\mathrm{char}(K) \notin \{2, 3, 5, 17\}$, $D_6 = 382{,}500{,}000$, $\log_9 6 \approx 0.815465$);
   - $x^{11} \in \mathrm{RP}_K^{\mathrm{pass}}(3, 7)$ ($\log_{11} 7 \approx 0.811508$);
   - $x^{13} \in \mathrm{RP}_K^{\mathrm{pass}}(3, 8)$ ($\mathbf{\log_{13} 8 \approx 0.810714}$ — unique integer global minimizer of $\log_{2t-3} t$!).
   - **Downstream Corollaries:** Reduces the $r=3$ base exponent from Vinciguerra's $\log_5 4 \approx 0.86135$ to $0.81071$ across 4-register powering (Corollary 4.3.1), catalytic streaming frequency moments $F_D(\sigma)$ (Corollary 5.1.1), and matrix powering $A^N$ (Theorem 5.2).

4. **Theorem T4 — Balanced Zero-Workspace Bilinear Multilinear Product** ([`BalancedProduct.lean`](lean/Catalytic/BalancedProduct.lean)):
   Over any commutative ring $R$, for $d = 2^k$, cleanly computes $x_0 \cdots x_{d-1}$ with zero clean workspace, $\log_2 d + 2$ registers, strictly pairwise-distinct indices, and exact primitive op count $(7d^2 - 4)/3$ (improving linear-chain $3 \cdot 4^{d-1} - 2$).

---

## Quick Verification

```powershell
# Full end-to-end verification (Lean 4.35 + VerifyAxioms + leanchecker-paranoid + pytest + figures + PDF + SHA-256)
pwsh -File scripts/run_all.ps1 -Task all
```

See [`REPLICATION.md`](REPLICATION.md) for step-by-step Linux/macOS/Windows instructions, including exporting NDJSON to `con-leche`, `con-ron`, and `nanoda_bin`, and clean-room verification of `dist/arxiv_submission.tar.gz`.

## Repository Layout

| Path | Description |
|---|---|
| `lean/` | Zero-Mathlib Lean 4.35.0 formalization (`Catalytic/*`, `Challenge.lean`, `Solution.lean`, `VerifyAxioms.lean`, `formalization.yaml`) |
| `experiments/` | 4 exact-arithmetic & CaDiCaL 2.1.2 verification scripts (`exp1`–`exp4`) |
| `tests/test_all.py` | 8/8 passing `pytest` verification tests |
| `scripts/` | Deterministic vector figure generator (`make_figures.py`) & orchestrator (`run_all.ps1`) |
| `paper/` | AMS-LaTeX manuscript (`main.tex`, `references.bib`, 3 deterministic vector PDFs) |
| `dist/` | Frozen release PDF (`Donahue_2026_catalytic_register_frontiers.pdf`) & clean-room verified `arxiv_submission.tar.gz` |
| `results/` | Machine-generated JSON outputs, `lean_axioms.txt`, and `six_kernel_audit.txt` |
| `docs/` | Architecture Decision Records (`docs/adr/`), plan (`docs/plan/`), and 10-pass review (`docs/10-pass-review.md`) |

## Attribution & Primary Literature

This work builds directly on and cites:
- A. Vinciguerra, *An Operator Approach to Register Programs for Catalytic Computing*, [`https://arxiv.org/abs/2609.18692`](https://arxiv.org/abs/2609.18692) (Sep 2026).
- G. Morse, *Unrestricted Boolean Multiplicative Complexity of Four-Term Binary Polynomial Multiplication*, [`https://arxiv.org/abs/2608.30238`](https://arxiv.org/abs/2608.30238) (Aug 2026).

No third-party copyrighted PDFs are redistributed in this repository.
