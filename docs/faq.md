<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Frequently Asked Questions (`docs/faq.md`)

### 1. Does this repository claim to solve P vs. NP?
**No.** This repository proves four self-contained theorems (`T1`–`T4`) on algebraic catalytic register programs over prime fields and commutative rings, answering open questions raised by Vinciguerra (`arXiv:2609.18692`, Sep 2026) and providing an empirical SAT companion contrasting Boolean multiplicative complexity (`arXiv:2608.30238`, Morse 2026). See [`LIMITATIONS.md`](../LIMITATIONS.md).

### 2. Why does the Lean 4.35 formalization avoid Mathlib and Batteries?
Zero external dependencies keep the formal trust base minimal (8,151 lines across 14 self-contained core Lean 4.35 modules, longest 1,364 lines; plus a 283-line standalone zero-import Palomar Challenge contract), eliminate multi-gigabyte cache requirements, allow a full clean-from-scratch rebuild in under one minute on any machine, and permit clean export to all five locally reproducible kernel implementations (`lean`, `leanchecker`/`leanchecker-paranoid`, `con-leche`, `con-ron`, `nanoda_bin`). See [`docs/adr/0001-zero-mathlib-six-kernel-lean.md`](adr/0001-zero-mathlib-six-kernel-lean.md).

### 3. Does Theorem T1 contradict Vinciguerra's Theorem 3.5?
**No — it refines and extends it to every prime characteristic.** Vinciguerra (`arXiv:2609.18692`, Theorem 3.5) proved $D_{2,K}^{\mathrm{pass}}(t) = t - 1$ over fields of characteristic $0$. Theorem `T1d` recovers that exact bound whenever $2 \le d < p$, while `T1` proves the complete base-$p$ digit-sum IFF criterion for all degrees $d \ge 2$ over $\mathbb{F}_p$ (showing both unbounded-degree Frobenius collapse at $t = 2$ via `T1a` and absolute impossibility whenever $s_p(d) \ge p$ via `T1c`).

### 4. Why do Theorems T3a–T3d exclude specific prime characteristics?
The explicit Pascal-row shear programs `prog5_x7`, `prog6_x9`, `prog7_x11`, and `prog8_x13` have integer coefficients and compute $D_t \cdot x^{2t-3}$ cleanly over **every** commutative ring $R$; dividing the output register by $D_t$ yields $x^{2t-3}$ whenever $D_t$ is invertible in $R$. For `prog5_x7`, $D_5 = 576 = 2^6 \cdot 3^2$, so it holds over $\mathbb{Q}$ and every prime field $\mathbb{F}_p$ with $p \ge 5$. Exact prime factorizations of all $D_t$ ($t = 4, \dots, 9$) are recorded in `results/exp2_three_register.json`.

### 5. Has this paper been externally peer-reviewed?
**Not yet.** Every Tier-1 theorem is machine-checked across 5 distinct Lean 4.35 kernel implementations (6 runs), and every Tier-2 computation is exact and reproducible, but external human peer review has not yet occurred.
