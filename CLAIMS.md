<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Machine-Auditable Claims Ledger (`CLAIMS.md`)

Every scientific claim in `catalytic-register-frontiers` is assigned an explicit epistemic tier and an explicit refutation condition (Build Standard B04, B42):

- **`TIER-1 (Lean 4.35 Multi-Kernel)`**: Formally verified from first principles in `lean/Solution.lean` + `lean/Catalytic/NonVacuity.lean` (zero Mathlib, zero forbidden tokens, strict core linters clean, axioms $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$, 6 passing kernel runs across 5 implementations).
- **`TIER-2 (Exact-Arithmetic / SAT-Certified)`**: 100% exact integer, rational (`fractions.Fraction`), finite-field ($\mathbb{F}_p$, $\mathbb{F}_4$), or CaDiCaL 2.1.2 SAT/UNSAT computation verified by `pytest`, Hypothesis property tests, mutant checks, and brute-force SAT encoder equivalence tests.
- **`TIER-3 (Paper-Level Reduction)`**: Standard mathematical deduction combining our Tier-1 theorems (`T3a`, `T3d`, `T3h`) with published reductions in Vinciguerra (`arXiv:2609.18692`, Corollary 5.1.1, §4.4, and Theorem 5.2).
- **`TIER-4 (Open Frontier)`**: Explicitly unresolved conjecture or research question.

## Tier-1 Machine-Checked Lean 4.35 Theorems

| ID | Statement (`lean/Challenge.lean`) | Proof (`lean/Solution.lean`) | Exact `#print axioms` | Verification |
|---|---|---|---|---|
| `T1` | `T1_DigitSumDichotomy` ($f \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t) \iff \forall d \ge 2,\, \alpha_d \neq 0 \to s_p(d) \le \min(p-1, t-1)$) | `t1_digit_sum_dichotomy` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels (`results/six_kernel_audit.txt`) |
| `T1a` | `T1a_TwoAccessFrobeniusCollapse` ($\forall p\text{ prime},\, m,\, x^{p^m} \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, 2)$) | `t1a_two_access_frobenius_collapse` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T1b` | `T1b_F2Saturation` ($\forall t,\, x^3 \notin \mathrm{RP}_{\mathbb{F}_2}^{\mathrm{pass}}(2, t)$) | `t1b_f2_saturation` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T1c` | `T1c_ImpossibilityThreshold` ($s_p(d) \ge p \implies \forall t,\, x^d \notin \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t)$) | `t1c_impossibility_threshold` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T1d` | `T1d_VinciguerraRecovery` ($2 \le d < p \implies (x^d \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t) \iff d + 1 \le t)$) | `t1d_vinciguerra_recovery` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T1e` | `T1e_ExtensionFieldSeparation` (exact sharp $\mathbb{F}_4$ separation: $x^5 \in \mathrm{RP}(2, 3) \setminus \mathrm{RP}(2, 2)$, $x^3 \in \mathrm{RP}(2, 4) \setminus \mathrm{RP}(2, 3)$, and $\forall t,\, x^7 \notin \mathrm{RP}(2, t)$) | `t1e_extension_field_separation` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T1s` | `T1s_Pass2RingSoundness` (literal `CRing` execution `Pass2Prog.execRing` agrees identically with symbolic `Pass2Prog.exec` over every char-$p$ commutative ring $R$) | `t1s_pass2_ring_soundness` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T1es` | `T1es_Pass2GF4Soundness` (literal `GF4`-algebra execution `Pass2GF4Prog.execAlg` agrees identically with symbolic `Pass2GF4Prog.exec` over every commutative $\mathbb{F}_4$-algebra $(R, \varphi)$) | `t1es_pass2_gf4_soundness` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T2` | `T2_BilinearFrobeniusCollapse` ($\forall k \ge 1$, $x^{2^k}$ cleanly in $k+1$ regs, $4k-2$ bilinear ops, **2** input accesses over any `Char2CRing`) | `t2_bilinear_frobenius_collapse` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T2b` | `T2b_DistinctOperandFrobenius` ($\forall k \ge 1$, $x^{2^k}$ cleanly in $k+2$ regs using strictly pairwise-distinct bilinear operands + passive linear copies, **2** input accesses over any `Char2CRing`) | `t2b_distinct_operand_frobenius` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T3a` | `T3a_ThreeReg5CallX7` ($x^7 \in \mathrm{RP}_R^{\mathrm{pass}}(3, 5)$ whenever $576$ invertible, i.e., $\mathrm{char} \neq 2, 3$) | `t3a_three_reg_5call_x7` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T3b` | `T3b_ThreeReg6CallX9` ($x^9 \in \mathrm{RP}_R^{\mathrm{pass}}(3, 6)$ whenever $382{,}500{,}000$ invertible, i.e., $\mathrm{char} \notin \{2,3,5,17\}$) | `t3b_three_reg_6call_x9` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T3c` | `T3c_ThreeReg7CallX11` ($x^{11} \in \mathrm{RP}_R^{\mathrm{pass}}(3, 7)$ over $\mathbb{Q}$ and good prime fields) | `t3c_three_reg_7call_x11` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T3d` | `T3d_ThreeReg8CallX13` ($x^{13} \in \mathrm{RP}_R^{\mathrm{pass}}(3, 8)$, optimal exponent $\log_{13} 8 \approx 0.810714$) | `t3d_three_reg_8call_x13` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T3e` | `T3e_ExponentChain` (exact `Nat` proof of $\log_{13} 8 < \frac{30}{37} < \log_{11} 7 < \frac{13}{16} < \log_9 6 < \frac{9}{11} < \log_7 5 < \frac{5}{6} < \log_5 4$ and $< \log_{15} 9$) | `t3e_exponent_chain` | *(none — zero axioms)* | 6 kernels |
| `T3f` | `T3f_GlobalIntegerOptimality` ($8^{37} < 13^{30}$ and $\forall t \ge 4,\, t \ne 8 \implies (2t-3)^{30} < t^{37}$, proving $\log_{13} 8 < \frac{30}{37} < \log_{2t-3} t$ for ALL $t \ge 4$) | `t3f_global_integer_optimality` | `propext`, `Quot.sound` | 6 kernels |
| `T3g` | `T3g_ThreeReg9CallX15` ($x^{15} \in \mathrm{RP}_R^{\mathrm{pass}}(3, 9)$ whenever $D_9$ invertible, post-minimum ascent point $\log_{15} 9 \approx 0.811368$) | `t3g_three_reg_9call_x15` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T3h` | `T3h_FourRegPowering` (complete 4-register passive powering for EVERY $N \ge 1$ over any `CRing`: $< \frac{104}{3} \cdot 8^\ell \le \frac{8}{3}\cdot 13 N^{\log_{13} 8}$ when $D_8, 12!, (\ell+1)!$ invertible; $< \frac{70}{3} \cdot 5^{\ell'} \le \frac{10}{3}\cdot 7 N^{\log_7 5}$ when $6!, (\ell'+1)!$ invertible; promotes Corollary 5.2 from Tier-3 to Tier-1!) | `t3h_four_reg_powering` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `T4` | `T4_BalancedMultilinearProduct` ($\forall k$, $d=2^k$, clean $x_0\cdots x_{d-1}$ with $0$ workspace, $k+2$ regs, $(7d^2-4)/3$ ops) | `t4_balanced_multilinear_product` | `propext`, `Quot.sound` | 6 kernels |
| `ALL` | Conjunction of all 19 theorems above | `prove_all_catalytic_theorems` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels |
| `NONVAC` | Concrete $0 \neq 1$ ring/prime/evaluation witnesses for `T1`–`T4` (incl. `ModP 5` $\mathrm{char}=5$, `ModP 7`/`ModP 13` for `T3h`, `GF4Hom.id`, and all five $D_5 \dots D_9$) | `Catalytic.NonVacuity.nonvac_all_hypotheses` | `propext`, `Classical.choice`, `Quot.sound` | 6 kernels (`con-leche`, `con-ron`, `nanoda_bin`) |

## Tier-2 Exact-Arithmetic & SAT-Certified Claims

| ID | Summary | Artifact | Pytest Guard |
|---|---|---|---|
| `E1` | Exhaustive $\mathbb{F}_2, \mathbb{F}_3, \mathbb{F}_5, \mathbb{F}_7$ verification ($d=2..120$/$100$): 107 feasible degrees ($s_p+1$), 82 exhaustive subset lower-bound audits, 349 impossible degrees ($s_p \ge p$). | `results/exp1_digit_sum.json` | `test_t1_prime_field_dichotomy_exact` |
| `E2` | Exact $\mathbb{F}_4$ extension-field spectrum ($d=1..16$): $x^5, x^{10} \to 3$ calls; $x^3, x^6, x^9, x^{12} \to 4$ calls; $x^7, x^{11}, x^{13}, x^{14}, x^{15}$ impossible $\forall t$. | `results/exp1_digit_sum.json` | `test_t1_extension_field_f4_spectrum` |
| `E3` | Exact $\mathbb{Z}[x, u, v]$ and $\mathbb{F}_p$ replay of $r=3$, $t=4..9$ ($x^5, x^7, x^9, x^{11}, x^{13}, x^{15}$), full prime factorizations of $D_t$, and all 9 integer exponent-chain inequalities. | `results/exp2_three_register.json` | `test_t3_three_register_breakthrough_exact` |
| `E4` | Exact $\mathbb{F}_2[x, c_0..c_k]$ symbolic verification of `T2` ($k=1..6$, $x^2..x^{64}$) and exact integer verification of `T4` ($d=2..32$, up to 2,388 ops). | `results/exp3_bilinear_balanced.json` | `test_t2_bilinear_frobenius_exact`, `test_t4_balanced_multilinear_product_exact` |
| `E5` | Exact CaDiCaL 2.1.2 SAT companion audit + brute-force $n=2, 3$ encoder equivalence audit + **8/8** archived & verified LRAT UNSAT proofs (`18,932` derived steps via `scripts/verify_lrat.py`): $\mathbb{F}_4$ mul $\mathrm{MC}_\wedge = 3$, orthogonal bent pair $\mathrm{MC}_\wedge = 3$, 182 degree-3 cancellations, 6/6 hard $(n=4, m=3)$ quadratic maps certified $k=2$ UNSAT, 0 Boyar–Find counterexamples. | `results/exp4_boolean_mc.json`, `results/sat_certs/*` | `test_exp4_boolean_mc_companion_sat`, `test_sat_encoder_bruteforce_equivalence`, `test_lrat_certificates_and_mutant_rejection` |

## Tier-3 Paper-Level Reductions

- **`R1` (Promoted to Tier-1 `T3h`):** Four-register passive powering for all $N \ge 1$ (`Cor. 5.2`) is now **fully machine-checked in Lean 4.35** (`lean/Catalytic/FourRegisterPowering.lean`, `T3h_FourRegPowering`) across all 6 kernels!
- **`R2` (Catalytic streaming frequency moments $F_D(\sigma)$):** Instantiating Tier-1 `T3h` over $\mathbb{F}_p^n$ with $p > \max(12, m^D, \lfloor\log_{13} D\rfloor + 1)$ and $p \nmid D_8$ reduces pass complexity at the $r=3$ base space tier from $O(D^{0.86136})$ to $O(D^{0.81072})$ using $O(n D \log(m+1))$ catalytic bits and $O(D \log(m+1) + \log n + \log D)$ regular workspace bits (matching Corollary 5.1.1 of `arXiv:2609.18692`).
- **`R3` (Non-commutative matrix powering $A^N$):** Lifting `T3a` (`prog5_x7`, shear degree $d = 2$) via Vinciguerra §4.4's $\ell_A(z)$ homogeneous lift cleanly computes $A^N$ for $A \in M_m(\mathbb{F}_p)$ ($p > \max(7, \lfloor \log_7 N \rfloor + 1)$) using at most $\frac{10}{3} \cdot 7 \cdot N^{\log_7 5} = O(N^{0.82709})$ recursive matrix calls and the **exact** $r=3$ scalar register count $2m^2 + \binom{m^2+2}{2} - 1$ (zero extra scalar registers vs. Theorem 5.2 of `arXiv:2609.18692`). Lifting `T3d` (`prog8_x13`, shear degree $d = 6$, $p > \max(13, \lfloor \log_{13} N \rfloor + 1)$, $p \nmid D_8$) achieves $O(N^{0.81072})$ calls using $3m^2 + \binom{m^2+5}{6} = \Theta(m^{12})$ scalar registers.

## What Would Prove Us Wrong (Refutation & Falsification Criteria — Build Standard B42)

Every claim in this repository is explicitly falsifiable:

1. **Refuting Formal Correctness (`T1`–`T4`, `NONVAC`):** Any of: (a) a clean rebuild of `lean/` failing or emitting any axiom outside `{propext, Classical.choice, Quot.sound}`; (b) any of the 6 kernels (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche`, `con-ron`, `nanoda_bin`) rejecting the exported proof stream; or (c) any mismatch between `lean/Challenge.lean` definitions and Vinciguerra (`arXiv:2609.18692`, Def. 2.2) documented in `docs/statement-fidelity.md`.
2. **Refuting `T1` (Digit-Sum Dichotomy):** Exhibiting a single prime $p$, budget $t \ge 1$, and passive 2-register program over $\mathbb{F}_p[x]$ cleanly computing a monomial $x^d$ ($d \ge 2$) with $s_p(d) > \min(p-1, t-1)$ — e.g., any clean 2-register program computing $x^3$ over $\mathbb{F}_2[x]$ in any number of calls $t$.
3. **Refuting `T2` or `T4`:** Exhibiting an input/catalytic state where `frobBilinProg` (over a `Char2CRing`) or `balancedProdProg` (over a `CRing`) fails to restore a single catalytic register or violates passive/strictly-distinct operand rules, or fails Hypothesis randomized testing in `tests/test_all.py`.
4. **Refuting `T3` (3-Register Exponent Improvement):** Finding a single input/catalyst triple $(x, u, v)$ where `prog5_x7`..`prog8_x13` fails to compute $O + D_t x^{2t-3}$ cleanly, or finding a good prime $p \nmid D_t$ where reduction modulo $p$ fails.
5. **Refuting `E5` (SAT Companion Audit):** Exhibiting a valid 2-AND unrestricted XAG circuit over $\mathbb{F}_2$ computing $\mathbb{F}_4$ multiplication, the orthogonal bent pair, or any of the 6 UNSAT $(n=4, m=3)$ maps — or finding a single input where our CNF encoder disagrees with brute-force ground truth.
6. **Refuting Novelty:** Citing any peer-reviewed paper or preprint predating 2026-11-23 that already proved Theorem `T1` (exact base-$p$ digit-sum IFF for $\mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t)$) or `T3d` ($x^{13} \in \mathrm{RP}_K^{\mathrm{pass}}(3, 8)$ achieving $\log_{13} 8$). If found, we will immediately log it in `ERRATA.md` and reframe to formalization/rediscovery.

## Tier-4 Open Frontiers (Explicitly Unresolved)

- **`O1`**: Uniform proof of $D_{3,\mathbb{Q}}^{\mathrm{pass}}(t) = 2t - 3$ for all $t \ge 4$ (and matching upper bounds for $r \ge 3$).
- **`O2`**: Whether non-triangular or multi-stage $r = 4$ loops can reach $N \ge 10$ at $t=5$ or $N \ge 13$ at $t=6$ to beat Vinciguerra's $r=4$ exponent $\log_7 4 \approx 0.71241$.
- **`O3`**: General closed-form combinatorial characterization of $\mathrm{RP}_{\mathbb{F}_{p^e}}^{\mathrm{pass}}(2, t)$ over non-prime extension fields ($e \ge 2$).
- **`O4`**: Boyar–Find conjecture (TCS 720, 2018) and Morse's $n = 5$ binary polynomial multiplication program (`arXiv:2608.30238`).
