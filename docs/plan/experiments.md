<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Experiment Log (`docs/plan/experiments.md`)

> Pipeline artifact `P11.F3`. Exact commands, deterministic seeds, verification scope, and output artifacts for all four computational experiments.

| ID | Script | Purpose & Scope | Determinism / Seed | Output Artifact | Status |
|---|---|---|---|---|---|
| **E1** | `experiments/exp1_digit_sum_dichotomy.py` | Exhaustive exact RREF check of Theorem T1 across 10,800 $(p, N, t)$ cases ($p \in \{2,3,5,7,11\}$) + extension-field $\mathbb{F}_4$ counterexample verification | Deterministic (exact exhaustive finite-field algebra) | `results/exp1_digit_sum.json` | Verified (`PASS`) |
| **E2** | `experiments/exp2_three_register_breakthrough.py` | Exact rational/integer synthesis, cleanliness check, and Pollard-Rho bad-prime factorization for $r = 3$, $t \in \{4, 5, 6, 7, 8, 9\}$ ($x^5 \dots x^{15}$) | Deterministic (exact `Fraction` + deterministic Miller–Rabin/Pollard-Rho) | `results/exp2_three_register.json` | Verified (`PASS`) |
| **E3** | `experiments/exp3_bilinear_and_balanced.py` | Independent exact verification of Theorem T2 (bilinear Frobenius collapse) and Theorem T4 ($2n$-call balanced multilinear product + $n$-register scaling) | Deterministic (exact multivariate polynomial arithmetic) | `results/exp3_bilinear_balanced.json` | Verified (`PASS`) |
| **E4** | `experiments/exp4_boolean_mc_companion.py` | Exact CaDiCaL 2.1.2 SAT/UNSAT audit of $\mathbb{F}_4$ mul ($k=2$ UNSAT, $k=3$ SAT), orthogonal bent pair ($k=2$ UNSAT, $k=3$ SAT), 182 sampled degree-3 cancellations, and 6 hard $(n=4, m=3)$ quadratic maps (`0` counterexamples); archives `.cnf` + ASCII `.lrat` certificates verified by `scripts/verify_lrat.py` | Fixed PRNG seed `20261123` + exact deterministic SAT encoding | `results/exp4_boolean_mc.json`, `results/sat_certs/f4_mul_k2.{cnf,lrat}`, `results/sat_certs/orthogonal_bent_pair_k2.{cnf,lrat}` | Verified (`PASS`, 2,338 & 3,264 LRAT steps) |

## Re-Run Command

```powershell
pwsh -NoProfile -File scripts/run_all.ps1 -Task experiments
.\.venv\Scripts\python.exe scripts/verify_lrat.py
```
