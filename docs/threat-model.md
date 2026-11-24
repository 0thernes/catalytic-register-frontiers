<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Threat Model (`docs/threat-model.md`)

Adversarial threat model for an independent AI-assisted formal mathematics repository, mapped directly to the six skeptical failure modes in the *Defensible Independent AI Research Playbook*.

## Assets & Trust Boundaries

- **Assets:** Mathematical truth of Theorems `T1`–`T4`, statement fidelity between `paper/main.tex` and `lean/Challenge.lean`, exactness of `results/exp*.json`, bibliographic integrity of `paper/references.bib`, and cryptographic integrity of `dist/*`.
- **Trust boundaries:** (1) Untrusted AI-drafted Lean tactics vs. independent type-checking kernels; (2) Formal definitions in `lean/` vs. primary literature definitions (`arXiv:2609.18692`); (3) Python SAT/algebra scripts vs. exact mathematical truth; (4) Local build artifacts vs. attested GitHub CI & immutable archive releases.

## Threats and Mitigations

| # | Threat | Attack Vector | Mitigation in `catalytic-register-frontiers` | Verification Evidence |
|---|---|---|---|---|
| 1 | **Axiom smuggling / compiler trust** | Hidden `sorry`, `admit`, `native_decide`, custom `axiom`, `@[extern]`, or `unsafe` code | Repository-wide forbidden-token grep in CI & `run_all.ps1` (0 hits) + `VerifyAxioms.lean` strict 3-axiom allowlist `[propext, Classical.choice, Quot.sound]` | `results/lean_axioms.txt`, `.github/workflows/ci.yml` |
| 2 | **Single-kernel soundness bug** | Kernel bug (cf. Lean #14576, July 2026) accepting an invalid proof term | Replay exported proof stream across 6 kernel runs / 5 implementations (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin`) | `results/six_kernel_audit.txt` |
| 3 | **Vacuous or weakened definitions** | Empty ring hypothesis, zero ring `0 = 1`, or subtly weakened model definition | Explicit `lean/Catalytic/NonVacuity.lean` exhibiting concrete `0 ≠ 1` witnesses (`ModP 2`, `ModP 5`, `ModP 7`, `ModP 11`, `Int`) + 1-to-1 Statement-Fidelity Audit Table | `lean/Catalytic/NonVacuity.lean`, `docs/statement-fidelity.md` |
| 4 | **SAT encoder bug / solver trust** | Buggy CNF encoding in `exp4_boolean_mc_companion.py` yielding false UNSAT | Independent brute-force ground-truth equivalence test on all small $n=2, 3$ Boolean functions ($k=0, 1, 2$ AND gates) + CaDiCaL internal proof checking; `cake_lpr` absence explicitly disclosed in `LIMITATIONS.md` | `tests/test_all.py`, `LIMITATIONS.md` |
| 5 | **Bibliographic / citation hallucination** | Wrong DOI, misattributed authors, or misstated baseline theorem | Automated `scripts/check_citations.py` checking every DOI/arXiv ID against Crossref / DataCite / arXiv APIs + direct primary-PDF audit logged in `ERRATA.md` | `scripts/check_citations.py`, `docs/literature-search-log.md`, `ERRATA.md` |
| 6 | **Mutable repo / forged logs / secret leakage** | Editing files post-release or accidentally committing credentials | `MANIFEST.sha256` covering all artifacts, CI secret regex scan, tag-triggered `release.yml` with `SHA256SUMS` + Sigstore `actions/attest-build-provenance@v2`, and no `.env` secrets | `MANIFEST.sha256`, `.github/workflows/release.yml` |
