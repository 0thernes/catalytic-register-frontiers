<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# ADR 0001: Zero-Mathlib Lean 4.35 Formalization, Core Linters, and Multi-Kernel Replay

- **Date:** 2026-11-23
- **Status:** Accepted (amended 2026-11-23 with core linters, `NonVacuity.lean`, and Batteries dilemma; expanded 2026-11-24 across Passes 3–8 to 14 modules and 20 theorems + `NonVacuity` = 22 audited declarations)
- **Context:** External proof-assistant dependencies (Mathlib, Batteries) introduce multi-GB transitive trusted codebases, slower clean-room builds, and version drift across independent type-checking kernels. Our theorems (`T1`–`T4`, including sharp $\mathbb{F}_4$ separation `T1e`, literal `CRing`/`GF4` soundness bridges `T1s`/`T1es`, distinct-operand `T2b`, global $t=8$ optimality `T3f`, $x^{15}$ `T3g`, 4-register powering `T3h`, and pointwise product-ring streaming frequency moments `T3i`) are self-contained algebraic and number-theoretic results over finite fields $\mathbb{F}_p$, $\mathbb{F}_4$, and commutative rings.
- **Decision:**
  1. Pin `leanprover/lean4:v4.35.0` with **zero Mathlib and zero third-party Lake dependencies** (`dependencies = []`).
  2. Prefix every `.lean` source file (all 14 files, 8,069 lines total, max 1,361 lines — well under Palomar's 10,000-line cap) with the Lean 4.35 `module` header.
  3. Enable strict zero-dependency core linters in `lean/lakefile.toml` (`autoImplicit = false`, `relaxedAutoImplicit = false`, `linter.unusedVariables = true`, `linter.deprecated = true`).
  4. **Recorded Dilemma (Playbook Finding #12 — Batteries `#lint` vs. zero dependencies):** Running Mathlib's `Batteries` `#lint` / `lake exe runLinter` requires adding `Batteries` as an external Lake dependency. We explicitly retain `dependencies = []` to keep the 6-kernel trust base minimal and enforce core Lean 4.35 linters cleanly instead.
  5. Isolate all 20 theorem statements as zero-`sorry` `Prop` definitions in `lean/Challenge.lean`, provide matching `lean/comparator.json` and `lean/formalization.yaml`, prove all 20 theorems in `lean/Solution.lean`, and prove concrete `0 ≠ 1` non-vacuity witnesses for every hypothesis bundle in `lean/Catalytic/NonVacuity.lean`.
  6. Prohibit `sorry`, `admit`, `native_decide`, custom `axiom`, `unsafe`, and `@[extern]` across `lean/`; audit every exported theorem via `VerifyAxioms.lean` strictly within `[propext, Classical.choice, Quot.sound]`; verify across 6 kernel runs spanning 5 implementations (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin 0.4.19`).
- **Consequences:** Full clean-from-scratch rebuild and 6-kernel certification complete in under one minute on standard hardware with zero warnings and a minimal trusted computing base.
