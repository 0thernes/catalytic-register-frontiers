<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Phase 0 — Kill & Pivot Criteria (`docs/plan/kill-criteria.md`)

Measurable stop/pivot conditions evaluated before release (2026-11-23):

1. **Formal Soundness Gate (Kill):** If any headline theorem (`T1`–`T4`) fails to compile in zero-Mathlib Lean 4.35.0, requires any axiom outside `[propext, Classical.choice, Quot.sound]`, or fails any of the 5 distinct verification kernels (6 runs), **drop** that theorem from the paper rather than shipping an unverified claim. -> *Status: PASSED (22/22 theorems + `prove_all` + `NonVacuity` = 24 audited declarations across 14 core modules verified across 5 distinct kernel implementations / 6 runs).*
2. **Counterexample / Statement-Fidelity Gate (Kill/Pivot):** If any Hypothesis property test, exact-arithmetic replay, or primary-PDF fidelity check finds a discrepancy between Lean definitions and Vinciguerra Def. 2.2 or a counterexample to `T1`–`T4`, **halt publication immediately** and fix or retract. -> *Status: PASSED (pre-release BibTeX and corollary phrasing errors caught and fixed in `ERRATA.md`).*
3. **Novelty / Scope Gate (Pivot):** If prior literature is found containing exact Theorem `T1` or `T3d` ($\log_{13} 8$), **pivot** framing cleanly to "first multi-kernel Lean 4 formalization" without claiming priority. -> *Status: No prior source found as of 2026-11-23 (`docs/literature-search-log.md`); conservative framing retained.*
