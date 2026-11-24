<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Future Ideas & Research Parking Lot (`docs/plan/ideas.md`)

> Pipeline artifact `P0.F4` (Scope-lock guardrail `AI02`: ideas discovered outside the frozen v1.0.0 scope are parked here instead of creeping into the release).

1. **All-$t$ Theorem for $r = 3$ Passive Catalytic Powering:** Prove (or refute) $D_{3,\mathbb{Q}}^{\mathrm{pass}}(t) = 2t - 3$ for all $t \ge 4$, including matching degree upper bounds and minimal bad-prime elimination sets across non-uniform shift tuples.
2. **Breaking $r = 4$ Beyond Vinciguerra's $\log_7 4 \approx 0.71241$:** Our triangular closed-loop $r = 4$ search reached $N = 2t - 1$ ($\epsilon_{\min} = 0.73249$ at $t=5$); investigate non-triangular feedback topologies or mixed-degree schedules to test whether $D_{4,\mathbb{Q}}^{\mathrm{pass}}(t)$ can exceed $2t - 1$.
3. **Prime-Power Extension Fields $\mathbb{F}_{p^e}$ ($e \ge 2$):** Classify $\mathrm{RP}_{\mathbb{F}_{p^e}}^{\mathrm{pass}}(2, t)$ completely (our Tier-1 Lean theorem `T1e` already proves the sharp $\mathbb{F}_4$ separation $t_{\min}(5)=3$, $t_{\min}(3)=4$, and $x^7$ impossible for all $t$, while `exp1` audits $d \le 16$).
4. **Morse's $n = 5$ Binary Polynomial Multiplication Conjecture (`arXiv:2608.30238`) & Boyar–Find (2018):** Scale exact symmetry-broken SAT + `cake_lpr` LRAT replay to test nonlinear-cancellation candidates at $n = 5, 6$.
5. **Independent CakeML `cake_lpr` CI Step:** Add an optional Linux CI job downloading a SHA-256-pinned `cake_lpr` release binary to replay `results/sat_certs/*.{cnf,lrat}` inside a formally verified theorem-prover-backed checker.
6. **Mathlib Upstream Contribution Path (Post-v1.0.0):** Extract clean standalone Lucas-theorem / digit-sum lemmas into a separate Mathlib-compatible PR once human Mathlib style review is complete (keeping `catalytic-register-frontiers` itself zero-Mathlib per ADR 0001).
