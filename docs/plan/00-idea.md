<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Phase 0 — Idea & One-Page Bet (`docs/plan/00-idea.md`)

**One-liner:** Give complexity theorists and formal-verification researchers machine-checked, zero-Mathlib Lean 4.35 results extending the study of passive catalytic register programs (`arXiv:2609.18692`; no question posed there is resolved) that improve the four-register powering exponent bound from $\log_5 4 \approx 0.86135$ to $\log_{13} 8 \approx 0.81071$ (not proved optimal; the streaming and non-commutative matrix-powering consequences, $\log_7 5 \approx 0.82709$ for matrices, are paper-level arguments). Correction note (2026-11-26 statement audit): the original wording of this plan said "resolution of two concrete open frontiers", "settle" and "optimal"; those words are withdrawn.

## Remarkable Angles Evaluated (Chosen: #1 + #3 Unified)

1. **(Chosen)** **Exact Positive-Characteristic Dichotomy + 3-Register Exponent Breakthrough:** Unconditionally settle $\mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t)$ via base-$p$ digit sums (`T1`), prove 2-access strictly bilinear Frobenius collapse (`T2`), strictly beat Vinciguerra's 3-register exponent (`T3`), and pair with an optimal zero-workspace balanced product (`T4`).
2. Generalize Vinciguerra's $r$-register 4-call operator identity to $r \ge 4$ at $t \ge 5$ (probed; triangular ansatz stays at $2t-1$, leaving non-triangular $r=4$ as Tier-4 Open Problem O2).
3. Formalize a zero-Mathlib, 6-kernel verified Lean 4.35 artifact with concrete non-vacuity witnesses (`NonVacuity.lean`) so independent skeptical verification takes under 60 seconds.
4. Contrast catalytic nonlinear cancellation against Boolean XAG multiplicative complexity (`arXiv:2608.30238`) via exact SAT audits.
5. Attempt a full separation of $P$ vs. $NP$ directly (rejected as infeasible inside finite appetite; barrier anatomy isolated separately in `p-vs-np-frontier-lab`).

## Reframes Considered

- **Pure paper proof only:** Rejected — independent AI-assisted math requires mechanical multi-kernel certification.
- **Mathlib-heavy formalization:** Rejected — multi-GB dependency cache bloats the trust base and slows independent clean-room verification.
- **Self-contained zero-Mathlib Lean 4.35 + exact Python + AMS-LaTeX release (Chosen):** Maximizes verification speed, minimality of trust base, and Palomar readiness.

## Upside, Estimates & Appetite

- **Appetite:** 2-day sprint (completed 2026-11-23).
- **Best case:** Publishable, Palomar-registered, peer-reviewed algebraic complexity result strictly improving the 3-register catalytic powering exponent and settling the prime-field 2-register frontier.
- **Likely case:** Permanent, zero-doubt, multi-kernel verified preprint and Lean artifact advancing the open problems of Vinciguerra (`arXiv:2609.18692`).
- **Cost of failure:** < 48 hours compute + author review time; \$0 direct cash outlay. Survives pessimistic 3x effort estimate comfortably.
