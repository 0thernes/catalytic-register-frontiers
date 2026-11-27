<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Phase 0 — Idea & One-Page Bet (`docs/plan/00-idea.md`)

**One-liner:** Give complexity theorists and formal-verification researchers machine-checked, zero-Mathlib Lean 4.35 results extending the study of passive catalytic register programs (`arXiv:2609.18692`; no question posed there is resolved) that improve the four-register powering exponent bound from $\log_5 4 \approx 0.86135$ to $\log_{13} 8 \approx 0.81071$ (not proved optimal; the streaming and non-commutative matrix-powering consequences, $\log_7 5 \approx 0.82709$ for matrices, are paper-level arguments). Correction note (2026-11-26 statement audit): the original wording of this plan said "resolution of two concrete open frontiers", "settle" and "optimal"; those words are withdrawn.

## Remarkable Angles Evaluated (Chosen: #1 + #3 Unified)

1. **(Chosen)** **Prime-Field Digit-Sum Characterisation + Improved Powering Exponent:** characterise $\mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t)$ under formal-polynomial cleanliness with $\mathbb{F}_p$ constants (`T1`), give 2-access product-only programs for $x^{2^k}$ in characteristic 2 (`T2`), improve the four-register powering exponent of Vinciguerra's Cor. 4.3.1 (`T3`, not proved optimal), and formalise the classical balanced clean-product recursion (`T4`, no lower bound).
2. Generalize Vinciguerra's $r$-register 4-call operator identity to $r \ge 4$ at $t \ge 5$ (probed; triangular ansatz stays at $2t-1$, leaving non-triangular $r=4$ as Tier-4 Open Problem O2).
3. Formalize a zero-Mathlib, 5-kernel (6-run) verified Lean 4.35 artifact with concrete non-vacuity witnesses (`NonVacuity.lean`) so independent skeptical verification takes under 60 seconds.
4. Contrast catalytic nonlinear cancellation against Boolean XAG multiplicative complexity (`arXiv:2608.30238`) via exact SAT audits.
5. Attempt a full separation of $P$ vs. $NP$ directly (rejected as infeasible inside finite appetite; barrier anatomy isolated separately in `p-vs-np-frontier-lab`).

## Reframes Considered

- **Pure paper proof only:** Rejected — independent AI-assisted math requires mechanical multi-kernel certification.
- **Mathlib-heavy formalization:** Rejected — multi-GB dependency cache bloats the trust base and slows independent clean-room verification.
- **Self-contained zero-Mathlib Lean 4.35 + exact Python + AMS-LaTeX release (Chosen):** Maximizes verification speed, minimality of trust base, and Palomar readiness.

## Upside, Estimates & Appetite

- **Appetite:** 2-day sprint (completed 2026-11-23).
- **Best case:** Publishable, Palomar-registered, peer-reviewed algebraic complexity result improving the four-register powering exponent bound and characterising two-register programs over $\mathbb{F}_p$ in the formal-polynomial model.
- **Likely case:** Permanent, zero-doubt, multi-kernel verified preprint and Lean artifact extending the study of passive catalytic register programs (`arXiv:2609.18692`; no question posed there is resolved).
- **Cost of failure:** < 48 hours compute + author review time; \$0 direct cash outlay. Survives pessimistic 3x effort estimate comfortably.
