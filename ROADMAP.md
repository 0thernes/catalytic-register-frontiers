<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Roadmap (`ROADMAP.md`)

## Shipped (`v1.0.0` / `v1.0.1`)

- Zero-Mathlib Lean 4.35.0 formalization of all 20 theorems & soundness bridges (`T1`, `T1a`–`T1e`, `T1s`, `T1es`, `T2`, `T2b`, `T3a`–`T3i`, `T4` with machine-checked `CatOp.usesOnly` containment within $\le k + 2$ designated registers) plus concrete `0 ≠ 1` `NonVacuity` witnesses (14 core modules, 8,145 lines, max 1,361 lines; plus standalone zero-import `PalomarChallenge.lean` [283 lines] and `PalomarSolution.lean` [842 lines]; 22 audited declarations), passing 5 distinct locally reproducible kernel implementations across 6 runs (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin 0.4.19`).
- Exact-arithmetic computational suite (`exp1`–`exp4`), `pytest` + Hypothesis property/metamorphic tests + mutant-killing tests + brute-force & second-encoder differential SAT audits + 8/8 archived & verified CaDiCaL 2.1.2 LRAT UNSAT proofs (`18,932` steps).
- Deterministic vector PDF figures, frozen AMS-LaTeX white paper + clean-room `dist/arxiv_submission.tar.gz`, 100% REUSE 3.3 SPDX coverage, and cryptographically verified DigiCert RFC 3161 + OpenTimestamps provenance (`provenance/`).
- **Confirmed Live Public Releases & Archival Mirrors:** Published `https://github.com/0thernes/catalytic-register-frontiers` with 100.0% Build Standard v1.1.0 score (`62/62`), green Linux & Windows CI + Sigstore SLSA attestations, live GitHub Pages Blueprint (`https://0thernes.github.io/catalytic-register-frontiers/`), Zenodo Concept DOI `10.5281/zenodo.24517198` (`v1.0.1` Version DOI `10.5281/zenodo.24517199`), Software Heritage snapshot `swh:1:snp:f960eeda6f145e54c0ac52538ace866a16e24085`, ORCID `0009-0006-8168-9648` work link, and `0thernes-research-archive` record `0TH-2026-010`.

## Planned & In-Progress External Credibility Steps

1. **Palomar Registry Final Registration:** Complete Palomar Registry editorial review and registration of the hardened commit (`lean/PalomarChallenge.lean`, `lean/PalomarSolution.lean`, `lean/palomar_comparator.json`, `lean/formalization.yaml`) at `submit.palomar-registry.org` (Palomar ID not yet assigned).
2. **Community & Peer Scrutiny:** Request independent reproduction on a second clean machine (updating [`REPLICATION.md`](REPLICATION.md)), post hand-written 5-sentence outreach on Lean Zulip (`#new members` → `#maths`), complete arXiv (`cs.CC`, `math.CO`, `cs.LO`) and HAL preprint deposits (IDs not yet assigned), and consider formal peer-reviewed journal submission.

## Open Mathematical Frontiers (Tier-4)

- **O1:** Uniform proof of $D_{3,\mathbb{Q}}^{\mathrm{pass}}(t) = 2t - 3$ for all $t \ge 4$ and matching upper bounds for $r \ge 3$.
- **O2:** Non-triangular or multi-stage $r = 4$ loops reaching $N \ge 10$ at $t = 5$ or $N \ge 13$ at $t = 6$ to improve $\log_7 4 \approx 0.71241$.
- **O3:** Closed-form combinatorial characterization of $\mathrm{RP}_{\mathbb{F}_{p^e}}^{\mathrm{pass}}(2, t)$ over non-prime extension fields ($e \ge 2$).
- **O4:** Boyar–Find conjecture (TCS 2018) and Morse's $n = 5$ binary polynomial multiplication program (`arXiv:2608.30238`).
