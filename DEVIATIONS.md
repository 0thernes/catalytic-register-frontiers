<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Deviations Log (`DEVIATIONS.md`)

Append-only log of any deviations from the initial research plan (`docs/plan/implementation-plan.md`).

| Date | Scope | Change | Reason | Impact on Claims |
|---|---|---|---|---|
| 2026-11-23 | Lean formalization (`lean/Catalytic/NonVacuity.lean`) | Added explicit concrete `ModP` and `Int` non-vacuity witnesses plus strict core linters (`autoImplicit = false`, `linter.unusedVariables = true`). | Defensible Independent AI Research Playbook v1.1 Checklist #5, #8, #12. | Strengthens formal verification; zero changes to theorem statements `T1`–`T4`. |
| 2026-11-23 | Test suite (`tests/test_all.py`) | Added Hypothesis property-based tests (B10), certificate mutant-killing tests (B13), and brute-force SAT encoder equivalence tests on $n = 2, 3$ (Playbook #14). | Build Standard v1.1.0 & Playbook compliance audit. | Increases adversarial test coverage; all prior assertions unchanged and passing. |
| 2026-11-23 | Governance & provenance | Aligned `repo.yaml` to `repo-standard.schema.json`, added `justfile`, `.zenodo.json`, `sbom.cdx.json`, `lean/comparator.json`, release/Pages workflows, and full `docs/` set. | Gap audit against `I:\All GH Repos` and `I:\White Papers`. | Raises Build Standard v1.1.0 compliance and closes release-readiness gaps. |
