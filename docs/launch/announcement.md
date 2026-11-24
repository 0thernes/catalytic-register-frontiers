<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Release Announcement & 5-Sentence Outreach Copy (`docs/launch/announcement.md`)

> Pipeline artifact `P9.F2`. Follows the Defensible Independent AI Research Playbook v1.1 5-sentence outreach protocol for Lean Zulip (`#new members` → `#maths`), Zenodo, and peer review.  
> **Published Coordinates:** Release `v1.0.1` (`8e4d53e`), Zenodo Concept DOI `10.5281/zenodo.24517198` (`v1.0.1`: `10.5281/zenodo.24517199`), SWHID `swh:1:snp:f960eeda6f145e54c0ac52538ace866a16e24085`.

## 1. Lean Zulip 5-Sentence Outreach (`#maths`)

1. **Result:** I formalized four results on passive catalytic register programs in zero-Mathlib Lean 4.35.0, including an exact base-$p$ digit-sum dichotomy for two-register powering over every prime field $\mathbb{F}_p$ and an explicit 3-register, 8-access construction for $x^{13}$ lowering the powering exponent from $\log_5 4 \approx 0.8614$ (Vinciguerra 2026) to $\log_{13} 8 \approx 0.8107$.
2. **Trust base:** All 14 Lean files (20 theorems/soundness bridges + non-vacuity = 22 audited declarations, including complete 4-register passive powering for all $N \ge 1$ and pointwise product-ring streaming frequency moments $F_D$) use `module`, zero external dependencies, zero `sorry`/`admit`/`native_decide`/custom axioms, strict built-in linters (`autoImplicit=false`), concrete non-vacuity witnesses (`NonVacuity.lean`), and replay cleanly across `lean`, `leanchecker`, `leanchecker-paranoid`, `lean4lean` (Ubuntu CI `lake check --paranoid`, 59,800 decls), `con-leche --verified`, `con-ron --verified`, and `nanoda_bin` with axioms strictly inside `[propext, Classical.choice, Quot.sound]`.
3. **Artifacts:** Repository: `https://github.com/0thernes/catalytic-register-frontiers` (release `v1.0.1`, commit `8e4d53e`, Zenodo DOI `https://doi.org/10.5281/zenodo.24517198`, SWHID `swh:1:snp:f960eeda6f145e54c0ac52538ace866a16e24085`), interactive Blueprint at `https://0thernes.github.io/catalytic-register-frontiers/`, and short public statement contract in `lean/Challenge.lean`.
4. **AI disclosure:** Exploratory algebra synthesis, proof drafting, and verification scripts were assisted by AI tools under my direction, with all formal truth established solely by the Lean 4.35 kernels and independent exact Python/LRAT checks.
5. **Specific question:** I would greatly appreciate critical feedback on the statement fidelity of `lean/Challenge.lean` (including our literal commutative-ring soundness bridges `Pass2Soundness.lean` and `CatProg` cleanliness) and whether any reader knows prior appearances of the $s_p(d) \le \min(p-1, t-1)$ prime-field criterion or $r=3$ powering exponent $\log_{13} 8$ in the catalytic-computing literature.

## 2. Short Repository & Archive Abstract

This repository contains the zero-Mathlib Lean 4.35.0 formalization, exact computational verification suite, archived CaDiCaL 2.1.2 LRAT UNSAT companion certificates, and 15-page AMS-LaTeX preprint for *Positive-Characteristic Dichotomy and Optimal Three-Register Exponents in Passive Catalytic Register Programs* by Alexander S. Donahue (`ORCID: 0009-0006-8168-9648`).
