# Implementation Plan — `catalytic-register-frontiers`

<!-- SPDX-License-Identifier: CC-BY-4.0 -->

## Objective

Prove, formally verify in zero-Mathlib Lean 4.35.0 (6 kernel runs), independently verify in exact Python arithmetic, visualize in deterministic vector PDFs, and publish an AMS-LaTeX white paper covering our four convergent theorems on catalytic register programs and nonlinear cancellation:

1. **Theorem T1 (Base-$p$ Digit-Sum Dichotomy for $\mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t)$):**
   Unconditional IFF characterization for every prime $p$, $t \ge 1$, and $f \in \mathbb{F}_p[x]$:
   $f \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t) \iff \forall d \ge 2$ with $[x^d]f \neq 0$, $s_p(d) \le \min(p-1, t-1)$.
2. **Theorem T2 (Strictly Bilinear 2-Access Frobenius Collapse over $\mathbb{F}_2$):**
   For every $k \ge 1$, $x^{2^k}$ is cleanly computed by a passive-output bilinear catalytic program over $\mathbb{F}_2$ in $k+1$ registers, $4k$ bilinear operations, and exactly **2** input accesses.
3. **Theorem T3 (3-Register Powering, Streaming, and Matrix-Powering Exponent Breakthrough):**
   Explicit passive-output 3-register catalytic programs over $\mathbb{Q}$ (and $\mathbb{F}_p$ avoiding explicit bad primes) establishing $x^9 \in \mathrm{RP}_K^{\mathrm{pass}}(3, 6)$, $x^{11} \in \mathrm{RP}_K^{\mathrm{pass}}(3, 7)$, and $x^{13} \in \mathrm{RP}_K^{\mathrm{pass}}(3, 8)$, strictly improving Vinciguerra's (`arXiv:2609.18692`) exponent $\log_5 4 \approx 0.86135$ down to $\log_{13} 8 \approx 0.81071$ (with machine-checked rational separator $\log_{13} 8 < \log_9 6 < 9/11 < \log_5 4$).
4. **Theorem T4 (Balanced Zero-Workspace Multilinear Catalytic Product):**
   For every $k \ge 1$ and $d = 2^k$, exact zero-workspace computation of $x_0 \cdots x_{d-1}$ over any commutative ring using $k+2$ catalysts and $(7d^2 - 4)/3$ primitive operations.
5. **Empirical Companion (Boolean Multiplicative Complexity & Boyar–Find):**
   Exact CaDiCaL 2.1.2 SAT sweep confirming zero counterexamples across 382 genuine degree-$\ge 3$ cancellation circuits and 14 hard quadratic maps, contrasting Boolean XAG rigidity (`arXiv:2608.30238`) with catalytic cancellation.
