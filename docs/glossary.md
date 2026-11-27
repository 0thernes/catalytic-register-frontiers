<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Glossary (`docs/glossary.md`)

## Mathematical & Verification Terms

- **Catalytic register program ($\mathrm{RP}_R(r, t)$):** A sequence of reversible register updates $R_i \leftarrow R_i + p(R_{\neq i})$ (basic instruction) and $R_i \leftarrow R_i + \lambda x_j$ (input access) on $r$ registers using at most $t$ input accesses that leaves all non-output registers restored to their arbitrary initial catalytic values (`arXiv:2609.18692`, Def. 2.2).
- **Passive-output program ($\mathrm{RP}_R^{\mathrm{pass}}(r, t)$):** A register program whose output register $O$ never appears on the right-hand side of any instruction.
- **Base-$p$ digit sum ($s_p(d)$):** Sum of the base-$p$ digits of $d \in \mathbb{N}$ (e.g., $s_2(7) = 3$, $s_p(p^m) = 1$). Governs `T1` via Lucas's Theorem.
- **Non-vacuity witness:** A concrete, non-trivial mathematical object ($0 \neq 1$) proved inside Lean (`lean/Catalytic/NonVacuity.lean`) to satisfy every hypothesis of a theorem so the theorem cannot hold vacuously.
- **Statement fidelity:** Line-by-line correspondence between a formal Lean declaration and the informal mathematical theorem stated in the paper and primary literature (`docs/statement-fidelity.md`).
- **Epistemic Tiers (`TIER-1`–`TIER-4`):**
  - `TIER-1`: Kernel-checked Lean 4.35 theorem verified across 5 distinct kernel implementations (6 runs).
  - `TIER-2`: Exact-arithmetic (`int`, `Fraction`, $\mathbb{F}_p$) or SAT-certified computation verified by `pytest`.
  - `TIER-3`: Standard paper-level reduction composing Tier-1 results with published composition lemmas.
  - `TIER-4`: Explicitly unresolved open mathematical problem.

## Build Standard Ten Finding Classes (v1.2.0)

| Class | Definition |
|---|---|
| `bug` | Defect in program logic: code runs but does something different from its specification or intent. |
| `error` | Wrong artifact or failed execution outside program logic: wrong number, claim, doc, config, version, build, or command. |
| `issue` | Weakness in something that exists: it works and is not wrong, but is unclear, inconsistent, fragile, or hard to maintain. |
| `problem` | External obstacle that blocks progress and is not caused by the project's own code or artifacts (e.g., missing external tool, network block, pending human reviewer). |
| `concern` | Risk that has not caused harm yet: something that could fail, mislead, cost money, or create security or legal exposure later. |
| `dilemma` | Trade-off between two or more valid options where the right choice depends on owner priorities. |
| `conflict` | Two requirements, sources, or rules contradict each other so satisfying one violates the other. |
| `gap` | Something required or expected is missing: a file, feature, doc, or item this standard or the task calls for does not exist yet, though nothing present is wrong. |
| `hole` | Missing check or safeguard: a path that nothing verifies or protects, so a defect could pass unnoticed. |
| `blindspot` | Something outside current attention: a user, platform, failure mode, or assumption nobody has examined yet, so what is wrong there is unknown. |
