<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Gold Standard 41-Item Release Checklist (`docs/launch/release-checklist.md`)

> Pipeline artifact `P9.F1` mapped 1-to-1 to Section 8 of `DEFENSIBLE_INDEPENDENT_AI_RESEARCH_PLAYBOOK.md` (v1.1).  
> **Honesty rule (`R6`):** Items requiring external services, remote GitHub push, third-party DOI minting, or human external reproduction are explicitly marked `[ ] PENDING (external)` and NEVER fabricated.

## Local Pre-Push Verification (Completed)

1. [x] **Claims ledger tagged:** `CLAIMS.md` classifies every claim (Tier-1 kernel-checked, Tier-2 certificate/exact-verified, Tier-3 paper proof, Tier-4 conjecture/open).
2. [x] **Zero forbidden Lean tokens:** 0 matches for `sorry`, `admit`, `native_decide`, `implemented_by`, `unsafe`, custom `axiom`, `@[extern]` across all 11 `.lean` files (`tests/test_all.py` + `.github/workflows/ci.yml`).
3. [x] **Strict `#print axioms`:** All 14 exported declarations strictly within `[propext, Classical.choice, Quot.sound]` (`lean/VerifyAxioms.lean`, `results/lean_axioms.txt`).
4. [x] **Exact `#print axioms` in README & CI:** Pasted verbatim in `README.md` ("5-Second Trust Check") and regenerated in `.github/workflows/ci.yml`.
5. [x] **Linters clean:** Zero-Mathlib Lean 4.35 core linters (`autoImplicit=false`, `relaxedAutoImplicit=false`, `linter.unusedVariables=true`, `linter.deprecated=true`) pass with 0 warnings across 14/14 jobs (no Mathlib dependency; `ruff` and `mypy` also pass with 0 errors).
6. [x] **Clean build from empty `.lake`:** Verified with pinned `lean/lean-toolchain` (`v4.35.0`) and `lean/lake-manifest.json` (zero external dependencies).
7. [x] **Multi-kernel verification:** 6 runs across 5 implementations (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin 0.4.19`) PASS natively on Windows (`results/six_kernel_audit.txt`). Upstream Windows `lean4lean.exe` `.olean` header mismatch (`problem`) is honestly documented; Linux CI runs `lake check --paranoid`.
8. [x] **Non-vacuity witnesses:** `lean/Catalytic/NonVacuity.lean` (`nonvac_all_hypotheses`) instantiates every hypothesis bundle of T1–T4 on concrete `0 ≠ 1` rings/fields (`ModP 2`, `ModP 5`, `ModP 7`, `ModP 11`, `Int`).
9. [x] **Palomar contract & comparator config:** `lean/Challenge.lean`, `lean/Solution.lean`, `lean/comparator.json`, `lean/formalization.yaml` present; every `.lean` file begins with `module` and is < 1,000 lines (Palomar limit: 10,000). Live `lake comparator --paranoid` runs on Linux CI (`bwrap`).
10. [x] **Statement-fidelity table:** Complete in `docs/statement-fidelity.md` and Table 6 of `paper/main.tex` (requires owner final visual sign-off before tag push).
11. [x] **Blueprint published / reason recorded:** Zero-dependency interactive HTML dependency graph and declaration map at `docs/index.html` (`.github/workflows/pages.yml`); reason for choosing static HTML over plasTeX `leanblueprint` recorded in `AGENTS.md` and `docs/stack-matrix.md`.
12. [x] **Adversarial definition tests:** Non-vacuity witnesses + exact brute-force/known-case checks + 5/5 certificate mutant-killing tests in `tests/test_all.py`.
13. [x] **SAT certificates verified:** CaDiCaL 2.1.2 DIMACS `.cnf` + ASCII `.lrat` proofs archived in `results/sat_certs/` (`f4_mul_k2`, 2,338 steps; `orthogonal_bent_pair_k2`, 3,264 steps) and verified by standalone exact checker `scripts/verify_lrat.py` (with mutant-rejection tests). *Honest note:* CakeML `cake_lpr` is not installed locally (`LIMITATIONS.md`; no Tier-1 Lean theorem depends on SAT).
14. [x] **CNF encoder brute-force equivalence & float boundary:** Exhaustive brute-force equivalence over all 16 $n=2$ functions ($k=0,1$) and canonical $n=3$ benchmarks passes in `tests/test_all.py`. Zero floating-point code exists in any proof or exact verification script (floats appear solely in matplotlib plotting `scripts/make_figures.py`).
15. [x] **Literature search logged:** Dated arXiv, zbMATH/MathSciNet, Google Scholar, OEIS search log in `docs/literature-search-log.md`.
16. [x] **Citation & retraction verification:** `scripts/check_citations.py` passed 10/10 live via Crossref/DataCite/arXiv with 0 retractions (catching and fixing `BoyarFind2018` DOI and `AFM2025` metadata, logged in `ERRATA.md`).
17. [x] **Pre-registration / exploratory status:** N/A for pure deductive proof discovery; clearly disclosed as exploratory formalization + deterministic companion audit (`DEVIATIONS.md`, `docs/plan/01-spikes.md`).
18. [x] **Deviations log:** Included in `DEVIATIONS.md`.
19. [x] **Negative results reported:** $r = 4$ triangular closed-loop non-improvement, $\mathbb{F}_4$ extension-field divergence, and 0 Boyar–Find counterexamples disclosed in `LIMITATIONS.md` and `paper/main.tex` Section 7.
20. [x] **Statistical protocol:** N/A — all results are exact algebraic/formal proofs or deterministic SAT certifications (no stochastic hypothesis testing).
21. [x] **Blinded scoring:** N/A — exact formal verification has binary machine-checked truth values.
22. [x] **Seeds, hardware, run counts reported:** Fixed seed (`20261123`), exact toolchain/hardware, and timings logged in `docs/run-log.md` and `docs/plan/experiments.md`.
23. [x] **Pinned toolchain & lockfiles:** `lean/lean-toolchain` (`v4.35.0`), `lean/lake-manifest.json`, `requirements.lock.txt`, `pyproject.toml`; container N/A reason recorded in `AGENTS.md` (`P5.07`).
24. [x] **SBOM generated:** CycloneDX 1.5 SBOM committed at `sbom.cdx.json`.
25. [x] **`MANIFEST.sha256` complete & cache-free:** Covers 100% of tracked repository artifacts (strictly excluding `.hypothesis/` and build caches; verified by `run_all.ps1 -Task audit` and `tests/test_all.py`).
26. [x] **RFC 3161 trusted timestamp & OpenTimestamps:** RFC 3161 query/response (`provenance/MANIFEST.sha256.{tsq,tsr}`) generated and verified via OpenSSL against a public TSA; OpenTimestamps calendar submission (`provenance/MANIFEST.sha256.ots` or documented status in `provenance/TIMESTAMP_AUDIT.txt`).
27. [ ] **PENDING (external / owner key):** Signed Git commits and signed `v1.0.0` release tag (owner signs locally with SSH/GPG/gitsign before `git push --tags`; Build Standard R1 forbids automated git hooks).
28. [ ] **PENDING (external / GitHub push):** GitHub artifact attestations (`actions/attest-build-provenance`) configured in `.github/workflows/release.yml`; will run automatically when tag `v1.0.0` is pushed.
29. [ ] **PENDING (external):** Zenodo DOI (verify Zenodo generative-AI depositor eligibility per `docs/legal-and-ethics.md`, or use OSF/HAL DOI) and Software Heritage SWHID snapshot.
30. [ ] **PENDING (external DOI/SWHID):** `CITATION.cff` validates locally against CFF 1.2.0; DOI and SWHID fields will be populated immediately after Step 29.
31. [ ] **PENDING (external):** Update ORCID `0009-0006-8168-9648` with minted DOI; already verified zero unformed-LLC affiliation across the entire repository (ADR 0002).
32. [x] **AI-contribution disclosure & CRediT roles:** Explicit in `paper/main.tex` (Section 8), `docs/legal-and-ethics.md`, and `README.md`; zero AI co-authors.
33. [x] **Prompt & transcript provenance:** Development & verification audit trail recorded in `docs/run-log.md`, `docs/reviews/01-10-pass-review.md`, and `MANIFEST.sha256` (conversation transcript SHA-256 archived locally by owner outside public repo privacy boundary).
34. [x] **Conflict of Interest (COI) statement:** Explicit in `paper/main.tex` Section 8 and `docs/legal-and-ethics.md`.
35. [x] **Open dual licenses & 100% SPDX/REUSE:** `Apache-2.0` (code/Lean) + `CC-BY-4.0` (text/figures), inline `SPDX-License-Identifier` headers across source/doc files, plus `REUSE.toml` covering 100% of tracked files.
36. [x] **Limitations & threats to validity:** Explicit in `LIMITATIONS.md` and `paper/main.tex` Section 8.
37. [x] **Export-control self-screen:** Completed (`15 CFR 734.8` fundamental research) in `docs/legal-and-ethics.md` and `paper/main.tex` Section 8.
38. [x] **Title & abstract match claims ledger:** Verified in Pass 1 (`docs/reviews/01-10-pass-review.md`); zero overclaiming beyond Tier-1/Tier-2 ledger.
39. [ ] **PENDING (external human):** Independent clean-machine reproduction by a second human following `REPLICATION.md`.
40. [x] **All 10 review passes logged:** Dated findings with six-class taxonomy recorded in `docs/reviews/01-10-pass-review.md` and `ERRATA.md`.
41. [ ] **PENDING (external):** Execute the 6-step release sequence in `docs/launch/channels.md` (`ai.viXra.org` strictly last).
