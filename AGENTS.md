# Agent & Contributor Instructions — `catalytic-register-frontiers`

<!-- SPDX-License-Identifier: CC-BY-4.0 -->

Follow these repository invariants on every edit:

1. **Workspace & Shell Safety:** This repository lives on a bracketed Windows path (`Z:\[Vibe Coded (AI)]\ANTIGRAVITY\catalytic-register-frontiers`). Always use `-LiteralPath` in PowerShell file cmdlets and run `pytest` repo-relative (`tests/test_all.py`).
2. **Zero-Mathlib Lean 4.35 Bar:** Every `.lean` file begins with `module` (Lean 4.35 module system). Zero `sorry`, zero `admit`, zero `native_decide`, zero custom `axiom`, zero `@[extern]`. Every exported theorem in `Challenge.lean` / `Solution.lean` must pass `VerifyAxioms.lean` strictly within `[propext, Classical.choice, Quot.sound]` and replay cleanly across `lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, and `nanoda_bin`.
3. **Exact Arithmetic & Reproducibility:** All computational checks in `experiments/` and `tests/` use exact integer/rational/finite-field arithmetic (`int`, `fractions.Fraction`) with no floating-point proof steps. Vector PDF figures must set `metadata={"CreationDate": None}` for determinism.
4. **Epistemic Integrity & Attribution:** Clearly separate machine-checked theorems (`T1`–`T4`), paper-level asymptotic corollaries, empirical companion data (Boyar–Find SAT sweep), and open questions. Cite `arXiv:2609.18692` (Vinciguerra, 2026) and `arXiv:2608.30238` (Morse, 2026) accurately without redistributing third-party PDFs. Author metadata uses `Alexander S. Donahue` (independent researcher, ORCID `0009-0006-8168-9648`, no unformed LLC claim); dual license is Apache-2.0 (code) + CC-BY-4.0 (prose/docs/figures).
5. **Git & CI Hygiene:** Commit directly to `main`; keep CI informational-only (`continue-on-error` absent, no PR gates, no Dependabot/Copilot config files). Regenerate `MANIFEST.sha256` after any change to tracked artifacts.
