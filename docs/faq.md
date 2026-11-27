<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Frequently Asked Questions (`docs/faq.md`)

### 1. Does this repository claim to solve P vs. NP?
**No.** This repository proves four self-contained theorems (`T1`–`T4`) on algebraic catalytic register programs over prime fields and commutative rings. They extend Vinciguerra (`arXiv:2609.18692`, Sep 2026, an arXiv preprint); no question posed in that paper is resolved. The repository also provides an empirical SAT companion contrasting Boolean multiplicative complexity (`arXiv:2608.30238`, Morse 2026). See [`LIMITATIONS.md`](../LIMITATIONS.md).

### 2. Why does the Lean 4.35 formalization avoid Mathlib and Batteries?
Zero external dependencies keep the formal trust base minimal (8,881 lines across 14 self-contained core Lean 4.35 modules, longest 1,511 lines; plus a 283-line standalone zero-import Palomar Challenge contract), eliminate multi-gigabyte cache requirements, allow a full clean-from-scratch rebuild in under one minute on any machine, and permit clean export to all five locally reproducible kernel implementations (`lean`, `leanchecker`/`leanchecker-paranoid`, `con-leche`, `con-ron`, `nanoda_bin`). See [`docs/adr/0001-zero-mathlib-six-kernel-lean.md`](adr/0001-zero-mathlib-six-kernel-lean.md).

### 3. Does Theorem T1 contradict Vinciguerra's Theorem 3.5?
**No.** Vinciguerra (`arXiv:2609.18692`, Theorem 3.5) proved $D_{2,K}^{\mathrm{pass}}(t) = t - 1$ for every $t \ge 2$ over fields of characteristic $0$; Section 3 of that paper is stated for characteristic 0 only, and it poses no positive-characteristic question. `T1` is this repository's own extension to prime fields, in a stated model: "cleanly computes" means equality of formal polynomials in $\mathbb{F}_p[R, x]$, with program constants in $\mathbb{F}_p$. In that model `T1` gives the base-$p$ digit-sum criterion for all degrees $d \ge 2$; `T1a` ($x^{p^m}$ with 2 accesses) shows that the characteristic-0 lower bounds do not extend to characteristic $p$, and `T1c` shows that no program yields the formal polynomial $x^d$ when $s_p(d) \ge p$. `T1d` is the analogue of Theorem 3.5 over $\mathbb{F}_p$ for $2 \le d < p$; nothing is proved over a field of characteristic 0. As functions on $\mathbb{F}_p$ the statements do not apply, since $x^p = x$.

### 4. Why do Theorems T3a–T3d exclude specific prime characteristics?
The explicit Pascal-row shear programs `prog5_x7`, `prog6_x9`, `prog7_x11`, and `prog8_x13` have integer coefficients and compute $D_t \cdot x^{2t-3}$ cleanly over **every** commutative ring $R$; dividing the output register by $D_t$ yields $x^{2t-3}$ whenever $D_t$ is invertible in $R$. For `prog5_x7`, $D_5 = 576 = 2^6 \cdot 3^2$, so it holds over $\mathbb{Q}$ and every prime field $\mathbb{F}_p$ with $p \ge 5$. Exact prime factorizations of all $D_t$ ($t = 4, \dots, 9$) are recorded in `results/exp2_three_register.json`.

### 5. Has this paper been externally peer-reviewed?
**Not yet.** Every Tier-1 theorem is machine-checked across 5 distinct Lean 4.35 kernel implementations (6 runs), and every Tier-2 computation is exact and reproducible, but external human peer review has not yet occurred.
