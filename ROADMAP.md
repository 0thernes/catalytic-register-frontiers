<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Roadmap (`ROADMAP.md`)

## Shipped (`v1.0.0`)

- Zero-Mathlib Lean 4.35.0 formalization of Theorems `T1` (`T1a`–`T1d`), `T2`, `T3` (`T3a`–`T3e`), `T4`, and `NonVacuity` witnesses, passing 6 kernel runs across 5 implementations (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin`).
- Exact-arithmetic computational suite (`exp1`–`exp4`), `pytest` + Hypothesis property tests + mutant-killing tests + brute-force SAT encoder equivalence audit.
- Deterministic vector PDF figures and frozen AMS-LaTeX white paper + clean-room `dist/arxiv_submission.tar.gz`.

## Next Release & External Credibility Steps (Ordered per Independent Research Playbook)

1. **Public GitHub Push & CI Verification:** Push `main` to `https://github.com/0thernes/catalytic-register-frontiers` and verify green Linux (`lake check --paranoid` + `pytest` + Tectonic) and Windows CI runs.
2. **Cryptographic Release & Archival:** Cut a release tag `v1.0.0` triggering `.github/workflows/release.yml` (`SHA256SUMS` + Sigstore SLSA attestations), evaluate Zenodo April 2026 AI eligibility honestly (or deposit via OSF/HAL), request a Software Heritage SWHID (`archive.softwareheritage.org/save`), and generate OpenTimestamps / RFC 3161 proof for `MANIFEST.sha256`.
3. **Palomar Registry Submission:** Submit the pinned 40-character commit SHA with `lean/Challenge.lean`, `lean/Solution.lean`, `lean/comparator.json`, and `lean/formalization.yaml` at `submit.palomar-registry.org`.
4. **Community & Peer Scrutiny:** Request independent reproduction on a second clean machine (updating [`REPLICATION.md`](REPLICATION.md)), post hand-written outreach on Lean Zulip (`#new members` → `#maths`), seek domain arXiv (`cs.CC`) endorsement from an active complexity author, and consider formal journal submission.

## Open Mathematical Frontiers (Tier-4)

- **O1:** Uniform proof of $D_{3,\mathbb{Q}}^{\mathrm{pass}}(t) = 2t - 3$ for all $t \ge 4$ and matching upper bounds for $r \ge 3$.
- **O2:** Non-triangular or multi-stage $r = 4$ loops reaching $N \ge 10$ at $t = 5$ or $N \ge 13$ at $t = 6$ to improve $\log_7 4 \approx 0.71241$.
- **O3:** Closed-form combinatorial characterization of $\mathrm{RP}_{\mathbb{F}_{p^e}}^{\mathrm{pass}}(2, t)$ over non-prime extension fields ($e \ge 2$).
- **O4:** Boyar–Find conjecture (TCS 2018) and Morse's $n = 5$ binary polynomial multiplication program (`arXiv:2608.30238`).
