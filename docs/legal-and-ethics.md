<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Legal, Ethics, AI Disclosure & Export-Control Self-Screen (`docs/legal-and-ethics.md`)

Records compliance with Sections 4, 5, 8 (#31–#37), and 10 of the *Defensible Independent AI Research Playbook* (v1.1).

## 1. Author Identity & Conflict of Interest (COI)

- **Author:** Alexander S. Donahue (`ORCID 0009-0006-8168-9648`)
- **Affiliation:** Independent Researcher, Spokane, WA, USA (`0_0@0thernes.art`)
- **Entity / Commercial Disclosure:** No LLC or corporate entity is claimed as author, affiliation, or copyright holder (see [`docs/adr/0002-epistemic-scope-and-identity.md`](adr/0002-epistemic-scope-and-identity.md)).
- **Funding & COI:** Self-funded independent research. No external grants, no institutional employer, no commercial conflicts of interest.

## 2. AI-Contribution & CRediT Statement

- **Human contributions (CRediT):** Conceptualization; Methodology; Formal analysis (definition design, statement-fidelity audit, primary-literature cross-check); Validation; Writing – review & editing; Supervision.
- **AI tools used:** Antigravity / Gemini (2026-11-23) assisted in exploratory exact-arithmetic probing, Lean 4.35 proof engineering, Python verification/figure scripting, and AMS-LaTeX manuscript drafting.
- **Not delegated to AI:** Choice of research questions, acceptance of theorem statements, statement-fidelity sign-off (`docs/statement-fidelity.md`), and epistemic scope boundaries (`CLAIMS.md`, `LIMITATIONS.md`).
- **Authorship & Accountability:** No AI system is listed as an author. Alexander S. Donahue takes full responsibility for all claims, proofs, code, and references. Mathematical soundness of all Tier-1 theorems is certified mechanically across 5 distinct locally reproducible Lean 4.35 kernel implementations in 6 runs (`results/six_kernel_audit.txt`).
- **Zenodo Generative-AI Policy Compliance (April 27, 2026):** Depositor eligibility under Zenodo's generative-AI policy (human-conducted research with AI used as a tool, no AI listed in creators/contributors) was verified prior to minting confirmed Zenodo Concept DOI `10.5281/zenodo.24517198` (`v1.0.1` Version DOI `10.5281/zenodo.24517199`). Palomar Registry explicitly accepts AI-assisted Lean formalizations when disclosed in `lean/formalization.yaml`.

## 3. Licensing & SPDX Attribution

- **Code, Lean 4.35 formalization, scripts, workflows:** `Apache-2.0` (compatible with Mathlib upstreaming and OSI/JOSS requirements).
- **White paper (`paper/`), documentation (`docs/`, `*.md`), figures (`paper/figures/*.pdf`):** `CC-BY-4.0`.
- **SPDX Headers:** Declared across source, script, workflow, and documentation files (`LICENSE`, `THIRD_PARTY_NOTICES.md`).
- **Copyright note on AI-assisted output:** Legal copyrightability of AI-generated portions varies by jurisdiction (see US Copyright Office AI reports); open permissive licensing (`Apache-2.0` / `CC-BY-4.0`) avoids restrictive "All rights reserved" claims.

## 4. Export-Control Self-Screen (Playbook Checklist #37)

- **Subject matter:** Pure algebraic complexity theory and finite-field combinatorics (polynomial degree bounds for passive catalytic register programs, Lucas's theorem, bilinear circuits, and small-instance Boolean multiplicative complexity).
- **Screening outcome:** Publicly available fundamental mathematical research (cf. 15 CFR 734.8). Contains zero cryptographic primitives, zero offensive-cyber code, zero dual-use biological/chemical/nuclear/defense material, and zero ITAR-controlled technical data (22 CFR 120). No export-control restriction identified. (Not formal legal advice; consult counsel if future extensions enter dual-use domains.)

## 5. Recorded Standard Conflict & Precedence Resolution (Build Standard R8)

- **Conflict (`I:\All GH Repos` R1 vs. `I:\White Papers` Checklist #27):** Build Standard Rule R1 prohibits mandatory commit/tag signing gates or local git hooks; White Paper Playbook Checklist #27 recommends SSH/GPG-signed commits and release tags.
- **Resolution under R8:** Local commits on `main` have zero hooks or forced signing gates (satisfying R1). When cutting a public archival tag for Zenodo/Palomar (`v1.0.0`), the author may optionally sign the release tag manually (`git tag -s v1.0.0`) to satisfy Playbook #27 without gating development.
