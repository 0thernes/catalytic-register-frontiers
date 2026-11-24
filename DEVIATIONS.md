<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Deviations Log (`DEVIATIONS.md`)

Append-only log of any deviations from the initial research plan (`docs/plan/implementation-plan.md`).

| Date | Scope | Change | Reason | Impact on Claims |
|---|---|---|---|---|
| 2026-11-23 | Lean formalization (`lean/Catalytic/NonVacuity.lean`) | Added explicit concrete `ModP` and `Int` non-vacuity witnesses plus strict core linters (`autoImplicit = false`, `linter.unusedVariables = true`). | Defensible Independent AI Research Playbook v1.1 Checklist #5, #8, #12. | Strengthens formal verification; zero changes to theorem statements `T1`–`T4`. |
| 2026-11-23 | Test suite (`tests/test_all.py`) | Added Hypothesis property-based tests (B10), certificate mutant-killing tests (B13), and brute-force SAT encoder equivalence tests on $n = 2, 3$ (Playbook #14). | Build Standard v1.1.0 & Playbook compliance audit. | Increases adversarial test coverage; all prior assertions unchanged and passing. |
| 2026-11-23 | Governance & provenance | Aligned `repo.yaml` to `repo-standard.schema.json`, added `justfile`, `.zenodo.json`, `sbom.cdx.json`, `lean/comparator.json`, release/Pages workflows, and full `docs/` set. | Gap audit against `I:\All GH Repos` and `I:\White Papers`. | Raises Build Standard v1.1.0 compliance and closes release-readiness gaps. |
| 2026-11-24 | Tier-1 promotion (`T1e`, `T1s`, `T1es`, `T2b`, `T3f`, `T3g`, `T3h`) | Formalized sharp $\mathbb{F}_4$ separation, literal `CRing`/`GF4` soundness bridges, distinct-operand char-2 collapse, global $t=8$ optimality, $x^{15}$, and complete 4-register passive powering for all $N \ge 1$ (`FourRegisterPowering.lean`, promoting Corollary 5.2 from Tier-3 to Tier-1). | Hostile-referee hardening Passes 3–6 eliminating paper-only and symbolic-to-literal trust gaps. | Expands Tier-1 from 12 to 19 machine-checked theorems (21 decls across 14 modules, 6/6 kernels) and tightens Corollary 5.2 & 5.3 finite-characteristic bounds (`ERRATA.md`). |
