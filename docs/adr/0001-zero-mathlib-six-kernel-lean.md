# ADR 0001: Zero-Mathlib Lean 4.35 Formalization and Multi-Kernel Replay

<!-- SPDX-License-Identifier: CC-BY-4.0 -->

- **Date:** 2026-11-23
- **Status:** Accepted
- **Context:** External proof-assistant dependencies (such as Mathlib) introduce large transitive trusted codebases, slower clean-room builds, and brittle version drift across independent type-checking kernels. Our theorems (`T1`–`T4`) are self-contained algebraic and number-theoretic results over finite prime fields $\mathbb{F}_p$, $\mathbb{F}_2$, $\mathbb{Q}$, and $\mathbb{Z}$.
- **Decision:**
  1. Pin `leanprover/lean4:v4.35.0` with **zero Mathlib and zero third-party Lake dependencies**.
  2. Prefix every `.lean` source file with the Lean 4.35 `module` header.
  3. Prohibit `sorry`, `admit`, `native_decide`, custom `axiom`, and `@[extern]` across the entire repository; audit every exported theorem via `VerifyAxioms.lean` strictly within `[propext, Classical.choice, Quot.sound]`.
  4. Verify compiled `.olean` artifacts across all six independent local kernel runs: `lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, and `nanoda_bin`.
- **Consequences:** Full clean-from-scratch rebuild and multi-kernel certification run in seconds on standard hardware with minimal trusted computing base.
