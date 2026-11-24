<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Machine-Auditable Claims Ledger (`CLAIMS.md`)

Every scientific claim in `catalytic-register-frontiers` is assigned an explicit epistemic tier:

- **`TIER-1 (Lean 4.35 Multi-Kernel)`**: Formally verified from first principles in `lean/Solution.lean` (zero Mathlib, zero forbidden tokens, axioms $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$, 6 passing kernel runs across 5 implementations).
- **`TIER-2 (Exact-Arithmetic / SAT-Certified)`**: 100% exact integer, rational (`fractions.Fraction`), finite-field ($\mathbb{F}_p$, $\mathbb{F}_4$), or CaDiCaL 2.1.2 SAT/UNSAT computation verified by `pytest`.
- **`TIER-3 (Paper-Level Reduction)`**: Standard mathematical deduction combining our Tier-1 theorems with published composition theorems in Vinciguerra (`arXiv:2609.18692`, Lemma 2.2, Corollaries 4.3.1, 5.1.1, Theorem 5.2).
- **`TIER-4 (Open Frontier)`**: Explicitly unresolved conjecture or research question.

## Tier-1 Machine-Checked Lean 4.35 Theorems

| ID | Statement (`lean/Challenge.lean`) | Proof (`lean/Solution.lean`) | Exact `#print axioms` | Verification |
|---|---|---|---|---|
| `T1` | `T1_DigitSumDichotomy` ($f \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t) \iff \forall d \ge 2,\, \alpha_d \neq 0 \to s_p(d) \le \min(p-1, t-1)$) | `t1_digit_sum_dichotomy` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels (`results/six_kernel_audit.txt`) |
| `T1a` | `T1a_TwoAccessFrobeniusCollapse` ($\forall p\text{ prime},\, m,\, x^{p^m} \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, 2)$) | `t1a_two_access_frobenius_collapse` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T1b` | `T1b_F2Saturation` ($\forall t,\, x^3 \notin \mathrm{RP}_{\mathbb{F}_2}^{\mathrm{pass}}(2, t)$) | `t1b_f2_saturation` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T1c` | `T1c_ImpossibilityThreshold` ($s_p(d) \ge p \implies \forall t,\, x^d \notin \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t)$) | `t1c_impossibility_threshold` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T1d` | `T1d_VinciguerraRecovery` ($2 \le d < p \implies (x^d \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t) \iff d + 1 \le t)$) | `t1d_vinciguerra_recovery` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T2` | `T2_BilinearFrobeniusCollapse` ($\forall k \ge 1$, $x^{2^k}$ cleanly in $k+1$ regs, $4k-2$ bilinear ops, **2** input accesses over any `Char2CRing`) | `t2_bilinear_frobenius_collapse` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T3a` | `T3a_ThreeReg5CallX7` ($x^7 \in \mathrm{RP}_R^{\mathrm{pass}}(3, 5)$ whenever $576$ invertible, i.e., $\mathrm{char} \neq 2, 3$) | `t3a_three_reg_5call_x7` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T3b` | `T3b_ThreeReg6CallX9` ($x^9 \in \mathrm{RP}_R^{\mathrm{pass}}(3, 6)$ whenever $382{,}500{,}000$ invertible, i.e., $\mathrm{char} \notin \{2,3,5,17\}$) | `t3b_three_reg_6call_x9` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T3c` | `T3c_ThreeReg7CallX11` ($x^{11} \in \mathrm{RP}_R^{\mathrm{pass}}(3, 7)$ over $\mathbb{Q}$ and good prime fields) | `t3c_three_reg_7call_x11` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T3d` | `T3d_ThreeReg8CallX13` ($x^{13} \in \mathrm{RP}_R^{\mathrm{pass}}(3, 8)$, optimal exponent $\log_{13} 8 \approx 0.810714$) | `t3d_three_reg_8call_x13` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T3e` | `T3e_ExponentChain` (exact `Nat` proof of $\log_{13} 8 < \frac{30}{37} < \log_{11} 7 < \frac{13}{16} < \log_9 6 < \frac{9}{11} < \log_7 5 < \frac{5}{6} < \log_5 4$ and $< \log_{15} 9$) | `t3e_exponent_chain` | *(none — zero axioms)* | 6 kernels |
| `T4` | `T4_BalancedMultilinearProduct` ($\forall k$, $d=2^k$, clean $x_0\cdots x_{d-1}$ with $0$ workspace, $k+2$ regs, $(7d^2-4)/3$ ops) | `t4_balanced_multilinear_product` | `propext`, `Quot.sound` | 6 kernels |
| `ALL` | Conjunction of all 12 theorems above | `prove_all_catalytic_theorems` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels (`con-leche`, `con-ron`, `nanoda_bin`) |

## Tier-2 Exact-Arithmetic & SAT-Certified Claims

| ID | Summary | Artifact | Pytest Guard |
|---|---|---|---|
| `E1` | Exhaustive $\mathbb{F}_2, \mathbb{F}_3, \mathbb{F}_5, \mathbb{F}_7$ verification ($d=2..120$/$100$): 107 feasible degrees ($s_p+1$), 82 exhaustive subset lower-bound audits, 349 impossible degrees ($s_p \ge p$). | `results/exp1_digit_sum.json` | `test_t1_prime_field_dichotomy_exact` |
| `E2` | Exact $\mathbb{F}_4$ extension-field spectrum ($d=1..16$): $x^5, x^{10} \to 3$ calls; $x^3, x^6, x^9, x^{12} \to 4$ calls; $x^7, x^{11}, x^{13}, x^{14}, x^{15}$ impossible $\forall t$. | `results/exp1_digit_sum.json` | `test_t1_extension_field_f4_spectrum` |
| `E3` | Exact $\mathbb{Z}[x, u, v]$ and $\mathbb{F}_p$ replay of $r=3$, $t=4..9$ ($x^5, x^7, x^9, x^{11}, x^{13}, x^{15}$), full prime factorizations of $D_t$, and all 9 integer exponent-chain inequalities. | `results/exp2_three_register.json` | `test_t3_three_register_breakthrough_exact` |
| `E4` | Exact $\mathbb{F}_2[x, c_0..c_k]$ symbolic verification of `T2` ($k=1..6$, $x^2..x^{64}$) and exact integer verification of `T4` ($d=2..32$, up to 2,388 ops). | `results/exp3_bilinear_balanced.json` | `test_t2_bilinear_frobenius_exact`, `test_t4_balanced_multilinear_product_exact` |
| `E5` | Exact CaDiCaL 2.1.2 SAT companion audit: $\mathbb{F}_4$ mul $\mathrm{MC}_\wedge = 3$, orthogonal bent pair $\mathrm{MC}_\wedge = 3$, 182 degree-3 cancellations, 6/6 hard $(n=4, m=3)$ quadratic maps certified $k=2$ UNSAT, 0 Boyar–Find counterexamples. | `results/exp4_boolean_mc.json` | `test_exp4_boolean_mc_companion_sat` |

## Tier-3 Paper-Level Reductions

- **`R1` (Powering with 4 registers):** Composing `T3d` with Vinciguerra (`arXiv:2609.18692`, Lemma 2.2) gives $x^N \in \mathrm{RP}_K^{\mathrm{pass}}(4, O(N^{\log_{13} 8}))$ ($\approx O(N^{0.81072})$ vs. $O(N^{0.86136})$).
- **`R2` (Catalytic streaming frequency moments $F_D(\sigma)$):** Reduces pass complexity at the $r=3$ base space tier from $O(D^{0.86136})$ to $O(D^{0.81072})$ (Corollary 5.1.1 of `arXiv:2609.18692`).
- **`R3` (Matrix powering $A^N$):** Reduces recursive matrix-input calls at $r=3$ base from $O(N^{0.86136})$ to $O(N^{0.81072})$ (Theorem 5.2 of `arXiv:2609.18692`).

## Tier-4 Open Frontiers (Explicitly Unresolved)

- **`O1`**: Uniform proof of $D_{3,\mathbb{Q}}^{\mathrm{pass}}(t) = 2t - 3$ for all $t \ge 4$ (and matching upper bounds for $r \ge 3$).
- **`O2`**: Whether non-triangular or multi-stage $r = 4$ loops can reach $N \ge 10$ at $t=5$ or $N \ge 13$ at $t=6$ to beat Vinciguerra's $r=4$ exponent $\log_7 4 \approx 0.71241$.
- **`O3`**: General closed-form combinatorial characterization of $\mathrm{RP}_{\mathbb{F}_{p^e}}^{\mathrm{pass}}(2, t)$ over non-prime extension fields ($e \ge 2$).
- **`O4`**: Boyar–Find conjecture (TCS 2018) and Morse's $n = 5$ binary polynomial multiplication program (`arXiv:2608.30238`).
