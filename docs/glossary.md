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

## Build Standard Six Finding Classes

| Class | Definition |
|---|---|
| `bug` | Defect in program logic: code runs but does something different from its specification or intent. |
| `error` | Wrong artifact or failed execution outside program logic: wrong number, claim, citation, doc, config, version, or build. |
| `issue` | Gap: something required by the standard or task is missing or incomplete, though nothing present is wrong. |
| `problem` | External obstacle not caused by project artifacts (e.g., missing external tool, network block, pending human reviewer). |
| `dilemma` | Trade-off between two or more valid options where the right choice depends on owner priorities. |
| `conflict` | Two requirements, sources, or rules contradict each other so satisfying one violates the other. |
