# Implementation Plan — `catalytic-register-frontiers`

<!-- SPDX-License-Identifier: CC-BY-4.0 -->

## Objective

Prove, formally verify in zero-Mathlib Lean 4.35.0 (6 kernel runs), independently verify in exact Python arithmetic, visualize in deterministic vector PDFs, and publish an AMS-LaTeX white paper covering our four convergent theorems on catalytic register programs and nonlinear cancellation:

1. **Theorem T1 (Base-$p$ Digit-Sum Dichotomy for $\mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t)$ & Soundness/Extension Bridges `T1a`–`T1e`, `T1s`, `T1es`):**
   Unconditional IFF characterization for every prime $p$, $t \ge 1$, and $f \in \mathbb{F}_p[x]$:
   $f \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t) \iff \forall d \ge 2$ with $[x^d]f \neq 0$, $s_p(d) \le \min(p-1, t-1)$, together with sharp $\mathbb{F}_4$ separation (`T1e`) and literal `CRing` / `GF4`-algebra soundness bridges (`T1s`, `T1es`).
2. **Theorem T2 (Strictly Bilinear & Distinct-Operand 2-Access Frobenius Collapse over Char 2; `T2`, `T2b`):**
   For every $k \ge 1$, $x^{2^k}$ is cleanly computed by a passive-output bilinear catalytic program over every characteristic-2 commutative ring in $k+1$ registers, $4k - 2$ bilinear operations, and exactly **2** input accesses (or $k+2$ registers with strictly pairwise-distinct bilinear operands, `T2b`).
3. **Theorem T3 (3-Register Powering Improvement, 4-Register Powering, & Streaming Moments `T3a`–`T3i`):**
   Explicit passive-output 3-register catalytic programs over $\mathbb{Q}$ (and $\mathbb{F}_p$ avoiding explicit bad primes) establishing $x^7, x^9, x^{11}, x^{13}, x^{15}$ in $5..9$ accesses, strictly improving Vinciguerra's (`arXiv:2609.18692`) exponent $\log_5 4 \approx 0.86135$ down to the unique global integer minimizer $\log_{13} 8 \approx 0.81071$ (`T3f`, separator $30/37$), plus complete machine-checked 4-register passive powering for every $N \ge 1$ (`T3h`, `< (104/3) * N^{log_13 8}` and `< (70/3) * N^{log_7 5}`) and pointwise product-ring streaming frequency moments $F_D(\mathbf{f}) = \sum_{i<n} f_i^D$ (`T3i`).
4. **Theorem T4 (Balanced Zero-Workspace Multilinear Catalytic Product):**
   For every $k \ge 0$ and $d = 2^k$, exact zero-workspace computation of $x_0 \cdots x_{d-1}$ over any commutative ring using $k+2$ registers ($k \ge 1$) and $(7d^2 - 4)/3$ strictly distinct primitive operations.
5. **Empirical Companion (Boolean Multiplicative Complexity & Boyar–Find):**
   Exact CaDiCaL 2.1.2 SAT sweep confirming zero counterexamples across 182 sampled degree-3 cancellation circuits and 6 hard $(n=4, m=3)$ quadratic maps plus $\mathbb{F}_4$ multiplication and an orthogonal bent pair (8/8 archived & verified LRAT UNSAT proofs, 18,932 steps), contrasting Boolean XAG rigidity (`arXiv:2608.30238`) with catalytic cancellation.
