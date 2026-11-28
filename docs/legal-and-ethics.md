<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Legal, Ethics, AI Disclosure & Export-Control Self-Screen (`docs/legal-and-ethics.md`)

Records compliance with Sections 4, 5, 8 (#27–#40), and 10 of the *Defensible Independent AI Research Playbook* (v1.3, merged edition) and Build Standard for LLMs (v1.2.0).

## 1. Author Identity & Conflict of Interest (COI)

- **Author:** Alexander S. Donahue (`ORCID 0009-0006-8168-9648`)
- **Affiliation:** Independent Researcher, Spokane, WA, USA (`0_0@0thernes.art`)
- **Entity / Commercial Disclosure:** No LLC or corporate entity is claimed as author, affiliation, or copyright holder (see [`docs/adr/0002-epistemic-scope-and-identity.md`](adr/0002-epistemic-scope-and-identity.md)).
- **Funding & COI:** Self-funded independent research. No external grants, no institutional employer, no commercial conflicts of interest.

## 2. AI-Contribution, CRediT & Venue-Matched Policy Compliance (Playbook v1.3 #32, #40)

- **Human contributions (CRediT):** Conceptualization; Methodology; Formal analysis (definition design, statement-fidelity audit, primary-literature cross-check); Validation; Writing – review & editing; Supervision.
- **AI tools used:** Antigravity / Gemini (2026-11-23 through 2026-11-27) assisted in exploratory exact-arithmetic probing, Lean 4.35 proof engineering, Python/JS verification and figure scripting, and AMS-LaTeX manuscript drafting.
- **Not done by AI:** Choice of research questions, acceptance of theorem statements, statement-fidelity sign-off (`docs/statement-fidelity.md`), and epistemic scope boundaries (`CLAIMS.md`, `LIMITATIONS.md`).
- **Authorship & Accountability:** No AI system is listed as an author. Alexander S. Donahue takes full responsibility for all claims, proofs, code, and references. Mathematical soundness of all Tier-1 theorems is certified mechanically across 5 distinct locally reproducible Lean 4.35 kernel implementations in 6 runs (`results/six_kernel_audit.txt`, zero `sorryAx`/`_native` axioms).
- **Venue-Matched AI Disclosures:**
  - **Zenodo Generative-AI Policy (April 27, 2026):** Depositor eligibility (human-conducted research with AI used as a tool, no AI listed in creators/contributors) was verified prior to minting Zenodo Concept DOI `10.5281/zenodo.24517198` (`v1.0.1` Version DOI `10.5281/zenodo.24517199`).
  - **Palomar Registry:** Explicitly accepts AI-assisted Lean formalizations when declared honestly in `lean/formalization.yaml` (live verified entry **`PALOMAR-2026-11-26-000004` v1**, `https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000004&version=1`, commit `1a92f47`, `✓ ORCID record checked`).
  - **Nature Portfolio Risk-Disclosure Framework (Nov 2026) & JOSS AI Policy:** Tool names, task boundaries ("Not done by AI"), and independent mechanical verification boundaries (5 Lean kernels, 8/8 LRAT UNSAT proofs, exact BigInt/Python differential checks) are disclosed transparently in `paper/main.tex` Section 8 and `README.md`.
  - **arXiv CS Practice (Oct 2025 onward):** Original formal/mathematical contribution (not a survey/position paper); clean-room LaTeX source bundle archived in `dist/arxiv_submission.tar.gz`.
  - **ORCID / DataCite Note:** Because DataCite Auto-Update requires the depositor's ORCID to appear verbatim in creator metadata, ORCID `0009-0006-8168-9648` is included in `.zenodo.json`, `CITATION.cff`, and manually verified visible (`Everyone`) on ORCID.
  - **Transcript Privacy & Redaction (Playbook v1.3 #33):** Raw agent transcripts are held locally by the author outside the public repository; any excerpt or transcript shared externally is scrubbed beforehand to remove secrets, API tokens, private emails, and personal data.

## 3. Licensing, Third-Party Rights & SPDX Attribution (Playbook v1.3 #24, #35)

- **Code, Lean 4.35 formalization, scripts, workflows:** `Apache-2.0` (compatible with Mathlib upstreaming and OSI/JOSS requirements).
- **White paper (`paper/`), documentation (`docs/`, `*.md`), figures (`paper/figures/*.pdf`):** `CC-BY-4.0`.
- **Third-Party Material & SPDX:** Zero third-party copyrighted papers, PDFs, or restricted figures are bundled; external toolchains are attributed in `THIRD_PARTY_NOTICES.md` and `sbom.cdx.json`, with 100% conflict-free REUSE 3.3 coverage verified by `scripts/check_reuse.py`.
- **Copyright note on AI-assisted output:** Legal copyrightability of AI-generated portions varies by jurisdiction (see US Copyright Office AI reports); open permissive licensing (`Apache-2.0` / `CC-BY-4.0`) avoids restrictive "All rights reserved" claims.

## 4. Versioning, Corrections & Withdrawal Policy (Playbook v1.3 #39)

- Every archival release carries a semantic tag (`v1.0.0`, `v1.0.1`, `v1.1.0`), a stable Zenodo Concept DOI (`10.5281/zenodo.24517198`), per-release Version DOIs (prior `v1.0.1`: `10.5281/zenodo.24517199`), live Palomar Registry entry `PALOMAR-2026-11-26-000004` v1, and a permanent Software Heritage SWHID (`swh:1:snp:f960eeda6f145e54c0ac52538ace866a16e24085`).
- All post-freeze corrections are logged append-only in [`ERRATA.md`](../ERRATA.md) and [`CHANGELOG.md`](../CHANGELOG.md).
- If any headline claim were ever falsified, the author will publish a dated withdrawal or correction notice on Zenodo and GitHub (plus any downstream preprint server) and never silently delete the archived record.

## 5. Export-Control Self-Screen (Playbook v1.3 #37)

- **Subject matter:** Pure algebraic complexity theory and finite-field combinatorics (polynomial degree bounds for passive catalytic register programs, Lucas's theorem, bilinear circuits, and small-instance Boolean multiplicative complexity).
- **Screening outcome:** Publicly available fundamental mathematical research (cf. 15 CFR 734.8). Contains zero cryptographic primitives (note: browser SHA-256 calls use standard platform Web Crypto API purely for memory-restoration integrity checking), zero offensive-cyber code, zero dual-use biological/chemical/nuclear/defense material, and zero ITAR-controlled technical data (22 CFR 120). No export-control restriction identified. (Not formal legal advice; consult counsel if future extensions enter dual-use domains.)

## 6. Tagging & Standard Precedence Alignment (Build Standard v1.2.0 R1/R8 & Playbook v1.3 #27)

- Under Playbook v1.1, Checklist #27 conflicted with Build Standard R1 by recommending signed commits/tags. **Playbook v1.3 resolved this conflict:** Checklist #27 explicitly specifies plain release tags without mandatory signing or local git hooks, aligning 100% with Build Standard v1.2.0 R1 (`v1.0.0` and `v1.0.1` plain tags published on GitHub).
