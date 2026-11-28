<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Prime-Field Digit-Sum Dichotomy and Improved Three-Register Powering Exponents in Passive Catalytic Register Programs

[![Version 1.1.0](https://img.shields.io/badge/version-1.1.0-blue.svg)](VERSION)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24517198.svg)](https://doi.org/10.5281/zenodo.24517198)
[![Palomar PALOMAR-2026-11-26-000004](https://img.shields.io/badge/Palomar-PALOMAR--2026--11--26--000004-009E73.svg)](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000004&version=1)
[![Lean 4.35.0 Zero-Mathlib](https://img.shields.io/badge/Lean-4.35.0%20(zero--Mathlib)-brightgreen.svg)](lean/lean-toolchain)
[![5 Kernels / 6 Runs PASS](https://img.shields.io/badge/kernels-5%20impls%20%2F%206%20runs%20PASS-brightgreen.svg)](results/six_kernel_audit.txt)
[![Code License: Apache-2.0](https://img.shields.io/badge/code%20license-Apache--2.0-blue.svg)](LICENSE)
[![Docs License: CC-BY-4.0](https://img.shields.io/badge/docs%20license-CC--BY--4.0-lightgrey.svg)](LICENSE)
[![Status: Preprint — Not Peer Reviewed](https://img.shields.io/badge/status-preprint%20(not%20peer%20reviewed)-yellow.svg)](LIMITATIONS.md)

A zero-Mathlib Lean 4.35.0 formalization, an exact-arithmetic verification suite and an AMS-LaTeX preprint with new results that extend Vinciguerra's register-program paper (`arXiv:2609.18692`, an arXiv preprint). No question posed in that paper is resolved. The two-register result characterises, under formal-polynomial cleanliness, which polynomials two-register passive programs with $\mathbb{F}_p$ constants compute. The explicit three-register programs improve the four-register powering exponent bound from $\log_5 4 \approx 0.8614$ to $\log_{13} 8 \approx 0.8107$; this exponent is not proved optimal.

The archived Zenodo `v1.0.1` record ([`10.5281/zenodo.24517199`](https://doi.org/10.5281/zenodo.24517199)) and Palomar Registry `v1` entry ([`PALOMAR-2026-11-26-000004`](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000004&version=1), pinned to verified commit `1a92f47`, deposited prior to the 2026-11-26 audit) carry the earlier title "Optimal Three-Register Exponents"; that word is withdrawn, and release **`v1.1.0`** ([`paper/main.tex`](paper/main.tex) and [`dist/Donahue_2026_catalytic_register_frontiers.pdf`](dist/Donahue_2026_catalytic_register_frontiers.pdf)) carries the corrected title above (see [`ERRATA.md`](ERRATA.md)).

**Author:** Alexander S. Donahue (Independent Researcher, Spokane, WA, USA · ORCID [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648) · `0_0@0thernes.art`)  
**Maintenance status:** active independent research artifact (`v1.1.0`, 2026-11-27) · **Zenodo Concept DOI:** [`10.5281/zenodo.24517198`](https://doi.org/10.5281/zenodo.24517198) (prior `v1.0.1`: [`10.5281/zenodo.24517199`](https://doi.org/10.5281/zenodo.24517199)) · **Palomar Registry:** [`PALOMAR-2026-11-26-000004`](https://palomar-registry.org/entry?id=PALOMAR-2026-11-26-000004&version=1) (`v1`) · **Frozen White Paper:** [`dist/Donahue_2026_catalytic_register_frontiers.pdf`](dist/Donahue_2026_catalytic_register_frontiers.pdf) · **Live Adaptive Forking PWA & Blueprint:** [`0thernes.github.io/catalytic-register-frontiers`](https://0thernes.github.io/catalytic-register-frontiers/) · **SWHID:** [`swh:1:snp:f960eeda6f145e54c0ac52538ace866a16e24085`](https://archive.softwareheritage.org/api/1/snapshot/f960eeda6f145e54c0ac52538ace866a16e24085/)

> **Epistemic Status:** All 22 headline theorems, corollaries, and bi-directional commutative-ring soundness/completeness bridges (`T1`, `T1a`–`T1e`, `T1s`, `T1es`, `T1sc`, `T1esc`, `T2`, `T2b`, `T3a`–`T3i` — including 4-register passive powering for all $N \ge 1$ over rings where $D_8$, $12!$ and $(\lfloor\log_{13} N\rfloor+1)!$ are invertible, and its coordinatewise form over $R^n$ (`T3i`), `T4` — including machine-checked `CatOp.usesOnly` containment within $\le k + 2$ designated registers, a conjunct added in commit `1a92f47`, after the `v1.0.1` tag) plus concrete `0 ≠ 1` non-vacuity witnesses (`NonVacuity`, including bivariate `FPS (FPS (ModP 5))` / `FPS (FPS GF4)` for `T1sc`/`T1esc` and product ring `Fin 3 → ModP 13` for `T3i`) are machine-checked from first principles in **zero-Mathlib Lean 4.35.0** across **14 core module files** (8,930 lines, max 1,511 lines; plus standalone Palomar contract files `PalomarChallenge.lean` [283 lines] and `PalomarSolution.lean`) and **5 distinct kernel implementations across 6 locally reproducible runs** (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin 0.4.19`) with 0 forbidden tokens and 0 linter warnings. (On Windows, the bundled `lean4lean.exe` fails locally with an upstream `.olean` header mismatch and is excluded from the completed local kernel count; see [`results/six_kernel_audit.txt`](results/six_kernel_audit.txt).) All 8/8 companion SAT UNSAT proofs are archived as ASCII LRAT certificates (`results/sat_certs/`), independently verified (`scripts/verify_lrat.py`), and cross-checked against both brute-force enumeration and a second independent CNF encoder (`tests/test_all.py`). This preprint has **not** undergone external peer review; confirmed archival identifiers are Zenodo Concept DOI `10.5281/zenodo.24517198` (prior `v1.0.1`: `10.5281/zenodo.24517199`), Palomar Registry `PALOMAR-2026-11-26-000004` (`v1`, commit `1a92f47`), Software Heritage SWHID `swh:1:snp:f960eeda6f145e54c0ac52538ace866a16e24085`, and ORCID `0009-0006-8168-9648` (arXiv and HAL IDs are not yet assigned). See [`CLAIMS.md`](CLAIMS.md) and [`LIMITATIONS.md`](LIMITATIONS.md).

### Scope of the claims (2026-11-26 statement audit)

An independent statement audit ([log](https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md)) found the following, and this README follows it:

- **What Lean proves.** `T1` is an exact iff in a stated model: "cleanly computes" means equality of formal polynomials in $\mathbb{F}_p[R, x]$, with program constants in $\mathbb{F}_p$. `T1s` and `T1sc` (`T1es`, `T1esc`, formalized in Pass 22 via zero-Mathlib formal power series $\mathbb{F}_p[[U]][[X]]$) prove the exact equivalence ($\Leftrightarrow$) between formal cleanliness and clean execution over every commutative ring of characteristic $p$ (every commutative $\mathbb{F}_4$-algebra), yielding a direct literal-ring Theorem `T1` (`rp_pass_two_literal_ring_iff`). It is still not a statement about pointwise functions on $\mathbb{F}_p$ alone, where $x^p = x$; for example $x^3$ over $\mathbb{F}_2$ is computed as a function with one input access, although `T1b` excludes the formal polynomial $x^3$. `T3a`–`T3d`, `T3g` are five explicit programs; `T3f` is an inequality between integers about the formula $\log_{2t-3} t$ and contains no register program.
- **What is not proved.** No upper bound on what three-register programs can achieve, so neither $\log_{13} 8$ nor any other three-register exponent is proved optimal. If $D^{\mathrm{pass}}_3(4) \ge 7$, the exponent $\log_7 4 \approx 0.7124$ would be smaller. No lower bound for `T4`.
- **Relation to Vinciguerra.** Section 6 of `arXiv:2609.18692` asks whether $D^{\mathrm{pass}}_{r,K}(4) > 2r-1$ and whether additional input accesses drastically increase $D^{\mathrm{pass}}_{r,K}$. The first question is not addressed here. On the second, `T3a`–`T3g` give lower bounds $D^{\mathrm{pass}}_3(t) \ge 2t-3$ for $t = 5,\dots,9$ only; the question stays open. The positive-characteristic question studied in `T1` is this repository's own extension of Vinciguerra's Theorem 3.5, which is stated for characteristic 0.
- **Prior work for `T4`.** `T4` is the classical four-step clean-product recursion applied in a balanced tree. Ben-Or and Cleve (SIAM J. Comput. 21(1), 1992, [`doi:10.1137/0221006`](https://doi.org/10.1137/0221006)) already compute every polynomial-size formula over an arbitrary ring with three registers in a neighbouring instruction set, and report earlier methods that use logarithmically many registers.

---

## 5-Second Formal Verification Proof (Verbatim `#print axioms`)

Exact output of `cd lean && lake env lean VerifyAxioms.lean` (24/24 audited declarations, archived in [`results/lean_axioms.txt`](results/lean_axioms.txt), cross-checked in CI; [`results/six_kernel_audit.txt`](results/six_kernel_audit.txt) records all 6 passing local runs across 5 distinct kernel implementations, including `con-leche --verified`, `con-ron --verified`, and `nanoda_bin 0.4.19` accepting 3,644 declarations on `Solution` and 3,502 declarations on `PalomarSolution` with `unpermitted_axiom_hard_error=true`):

```text
'Catalytic.Solution.t1_digit_sum_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1a_two_access_frobenius_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1b_f2_saturation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1c_impossibility_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1d_vinciguerra_recovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1e_extension_field_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1s_pass2_ring_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1es_pass2_gf4_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1sc_pass2_ring_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1esc_pass2_gf4_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t2_bilinear_frobenius_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t2b_distinct_operand_frobenius' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t3a_three_reg_5call_x7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t3b_three_reg_6call_x9' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t3c_three_reg_7call_x11' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t3d_three_reg_8call_x13' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t3e_exponent_chain' does not depend on any axioms
'Catalytic.Solution.t3f_global_integer_optimality' depends on axioms: [propext, Quot.sound]
'Catalytic.Solution.t3g_three_reg_9call_x15' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t3h_four_reg_powering' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t3i_streaming_frequency_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t4_balanced_multilinear_product' depends on axioms: [propext, Quot.sound]
'Catalytic.Solution.prove_all_catalytic_theorems' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.NonVacuity.nonvac_all_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Statement-Fidelity Summary (Full Table: [`docs/statement-fidelity.md`](docs/statement-fidelity.md))

| Lean Declaration (`lean/Challenge.lean`) | Literature Anchor | Non-Vacuity Witness (`NonVacuity.lean`) | Explicitly NOT Claimed |
|---|---|---|---|
| `T1`, `T1a`–`T1e`, `T1s`–`T1esc` (`InRPPass2`, `GF4`, `execRing`, `execAlg`, `FPS`) | Vinciguerra (`arXiv:2609.18692`), instruction set of Def. 2.2 with formal-polynomial cleanliness ($\Leftrightarrow$ universal char-$p$ ring execution via `T1sc`); Thm. 3.5 (characteristic 0) | `IsPrime 2,3,5,7`; `ModP 5` ($\mathrm{char}=5$); `GF4` (`GF4Hom.id`, $0 \neq 1$) | Functional (pointwise) cleanliness on $\mathbb{F}_p$; constants outside $\mathbb{F}_p$; general $\mathbb{F}_{p^e}$ ($e \ge 2$) closed form; $r \ge 3$ |
| `T2`, `T2b` (`BilinInstr`, `DistinctBilinInstr`) | Strictly bilinear & distinct-operand Def. 2.2 | `F2 = ModP 2` ($0 \neq 1$), $k = 2$, $x = 1$ | Odd characteristics |
| `T3a`–`T3i` (`Pass3InstrR`, `Pass4Instr`, `instCRingFinFun`, `prog5_x7`..`prog9_x15`, integer minimiser $t=8$ of $\log_{2t-3} t$, 4-reg powering & coordinatewise powering over $R^n$) | Vinciguerra (`arXiv:2609.18692`), Def. 2.2, Cor. 4.3.1, Cor. 5.1.1; Alekseev et al. (MFCS 2025), composition lemma (cited as Lemma 8 in `arXiv:2609.18692`; numbered Lemma 2.1 in `arXiv:2504.17412v1`) | `ModP 5, 7, 11, 13` ($0 \neq 1$) with explicit $D_5^{-1}\!\dots D_9^{-1}$, $12!^{-1}$, $6!^{-1}$ | Optimality of any 3-register exponent; bad primes dividing $D_t$ or $(\ell+1)!$; uniform $t \ge 10$; upper bounds; bit-space accounting |
| `T4_BalancedMultilinearProduct` (`CatOp`) | Zero-workspace strictly distinct bilinear ops; classical four-step clean-product recursion; Ben-Or and Cleve (1992) for a neighbouring model | `Int` ($0 \neq 1$), $d = 4$, 36 ops, clean restoration | Non-power-of-two $d$ without padding; lower-bound optimality; minimality of the register count |

---

## Core Mathematical Results

1. **Theorem T1 — Base-$p$ digit-sum characterisation of $\mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t)$, formal-polynomial cleanliness, $\mathbb{F}_p$ constants** ([`DigitSumDichotomy.lean`](lean/Catalytic/DigitSumDichotomy.lean)):
   For every prime $p$, every budget $t \ge 1$, and every univariate polynomial $f(x) = \sum_{d \ge 0} \alpha_d x^d \in \mathbb{F}_p[x]$, with "cleanly computes" meaning equality of formal polynomials in $\mathbb{F}_p[R, x]$:
   $$f \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t) \quad \Longleftrightarrow \quad \forall\, d \ge 2 \text{ with } \alpha_d \neq 0,\;\; s_p(d) \le \min(p - 1,\; t - 1).$$
   This is a self-posed extension of Vinciguerra's Theorem 3.5, which is stated for characteristic 0; the source poses no positive-characteristic question. As functions on $\mathbb{F}_p$ the statements do not apply, since $x^p = x$.
   - **T1a:** $x^{p^m} \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, 2)$ for all $m \ge 0$ ($D_{2,\mathbb{F}_p}^{\mathrm{pass}}(2) = +\infty$). This uses the identity $(R+x)^{p^m} - R^{p^m} = x^{p^m}$ and shows that the characteristic-0 lower bounds do not extend to characteristic $p$; it does not contradict the source, whose theorems are stated for characteristic 0.
   - **T1b:** With $\mathbb{F}_2$ constants, no program yields the formal polynomial $x^3$, for any $t \ge 0$ (as a function on $\mathbb{F}_2$, $x^3 = x$).
   - **T1c:** Whenever $s_p(d) \ge p$, no program with $\mathbb{F}_p$ constants yields the formal polynomial $x^d$, for any $t \ge 1$.
   - **T1d:** Large-characteristic analogue of Theorem 3.5: whenever $2 \le d < p$, $x^d \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t) \iff t \ge d + 1$. Nothing is proved over a field of characteristic 0.
   - **T1e:** With $\mathbb{F}_4$ constants the criterion changes ($x^3$ becomes computable with 4 accesses), so it is not stable under field extension.

2. **Theorem T2 — Two-access programs for $x^{2^k}$ with product-only updates in characteristic 2** ([`BilinearFrobenius.lean`](lean/Catalytic/BilinearFrobenius.lean)):
   Under bilinear updates $R_i \leftarrow R_i + R_j R_\ell$ ($j, \ell \neq i$, passive $R_0$; self-squares $R_j = R_\ell$ allowed, removed in `T2b`), for every $k \ge 1$ and every `Char2CRing` $R$, $x^{2^k}$ is cleanly computed in $k + 1$ registers, $4k - 2$ bilinear ops, and **2 input accesses**. This is repeated squaring with $(a+b)^2 = a^2 + b^2$; no lower bound is proved.

3. **Theorem T3 — Explicit three-register programs and an improved four-register powering exponent bound** ([`ThreeRegisterBreakthrough.lean`](lean/Catalytic/ThreeRegisterBreakthrough.lean)):
   Explicit Pascal-row shear loops (a sub-language of the Definition 2.2 instruction set) give $x^7 \in \mathrm{RP}(3, 5)$ ($D_5 = 576$, $\log_7 5 \approx 0.82709$), $x^9 \in \mathrm{RP}(3, 6)$ ($D_6 = 382{,}500{,}000$, $\log_9 6 \approx 0.81546$), $x^{11} \in \mathrm{RP}(3, 7)$ ($\log_{11} 7 \approx 0.81151$), $x^{13} \in \mathrm{RP}(3, 8)$ ($\log_{13} 8 \approx 0.81071$), and $x^{15} \in \mathrm{RP}(3, 9)$ ($\log_{15} 9 \approx 0.81137$), each over rings where $D_t$ is invertible. $\log_{13} 8$ is the smallest exponent among the constructed programs; `T3f` shows that $t = 8$ minimises $\log_{2t-3} t$ over integers $t \ge 4$, which is integer arithmetic, not an optimality theorem for register programs. `T3h` uses `prog8_x13` to improve the exponent of Vinciguerra's Cor. 4.3.1 at four registers from $\log_5 4 \approx 0.86135$ to $\log_{13} 8$. The improvement is in the exponent: with the stated constants, $(104/3)\,N^{0.8107}$ is below $20\,N^{0.8614}$ only for $N$ above about 52,000 (the `prog5_x7` variant $(70/3)\,N^{0.8271}$: above about 90). With five registers the source already has the smaller exponent $\log_7 4 \approx 0.7124$. The streaming bit-space bound (Cor. 5.1.1) and the non-commutative matrix-powering lift via `prog5_x7` (Thm. 5.2, $\log_7 5 \approx 0.82709$) are paper-level arguments, not Lean theorems.

4. **Theorem T4 — Balanced zero-workspace multilinear product (classical construction, formalised)** ([`BalancedProduct.lean`](lean/Catalytic/BalancedProduct.lean)):
   Over any commutative ring $R$, for $d = 2^k$, cleanly computes $x_0 \cdots x_{d-1}$ with zero clean workspace, $\log_2 d + 2$ registers, strictly pairwise-distinct indices, and exact primitive op count $(7d^2 - 4)/3$ (this count includes the $d^2$ input-access instructions). The construction is the four-step telescoping clean-product recursion applied in a balanced tree. Ben-Or and Cleve (1992) give polynomial-length three-register programs for all polynomial-size formulas in a neighbouring instruction set; whether a constant number of registers suffices in the instruction set used here is not settled, and no lower bound is proved. The register-count conjunct is part of the Lean statement from commit `1a92f47` on; at the `v1.0.1` tag it was read off the program definition.

---

## Quickstart

Prerequisites: **Lean 4.35.0** (`elan`), **Python 3.13**, **Tectonic** (CaDiCaL 2.1.2 is bundled with Lean 4.35.0).

```bash
# 1. Install pinned Python dependencies
python -m venv .venv
# Windows: .venv\Scripts\activate   |   Linux/macOS: source .venv/bin/activate
pip install -r requirements.lock.txt

# 2. Run the full end-to-end verification pipeline (Lean + tests + figures + PDF + LRAT + REUSE + SHA-256)
just reproduce
# Or on Windows PowerShell without `just`:
pwsh -NoProfile -File scripts/run_all.ps1 -Task all
# Or on Linux/macOS without `just`:
bash scripts/run_all.sh all
```

Expected result: 19/19 default Lean jobs built with 0 warnings, `leanchecker --fresh`, `leanchecker-paranoid`, `con-leche`, and `con-ron` exit 0, all 35 `pytest` / Hypothesis / mutant / differential-SAT / LRAT / REUSE / SBOM / workflow / schema / SVG / HTML5 / matrix-lift / factorization / JS Adaptive Forking PWA & CLI differential / Build Standard v1.2.0 & Playbook v1.3 consistency tests PASS, 3 deterministic PDFs generated, 0-warning Tectonic PDF compile, 100% `MANIFEST.sha256` verification, and DigiCert RFC 3161 `Verification: OK` (re-sealed cleanly on `main` after the 2026-11-26 statement audit `2a159ce`/`530bf12` and Passes 20–22; see [`ERRATA.md`](ERRATA.md)).

### Universal Zero-Dependency Adaptive Forking CLI (Any Device with Node.js)
```bash
# Accepts --flag=val, --flag val, positional args, selfcheck, CSV horizon, AND raw --stdin piping:
node docs/catalytic-engine.js selfcheck
node docs/catalytic-engine.js plan    --N=169 --p=1009
echo "LiveRAM" | node docs/catalytic-engine.js vault --stdin 91 1009
node docs/catalytic-engine.js stream  "imu_a imu_a imu_b imu_c imu_a" 20 1009
node docs/catalytic-engine.js horizon 137 scalar --csv
node docs/catalytic-engine.js verify  catalytic-proof-*.json
node docs/catalytic-engine.js bench
# Or via just: just adaptive selfcheck
```

## Usage and Examples

### Common Path — Verify Lean Proofs & Run Exact Test Suite
```bash
cd lean && lake build && lake env lean VerifyAxioms.lean && lake env leanchecker-paranoid Solution
cd .. && pytest -v tests/test_all.py
```

### Advanced Path — Export Proof Stream to External Kernels & Audit Repository
```bash
cd lean
lake env leanexport Solution -- Catalytic.Solution.prove_all_catalytic_theorems Catalytic.NonVacuity.nonvac_all_hypotheses > /tmp/sol.ndjson
lake env con-leche --verified /tmp/sol.ndjson
lake env con-ron --verified /tmp/sol.ndjson
cd ..
python scripts/check_citations.py --offline
pwsh -NoProfile -File scripts/Audit-Repo.ps1 -Path .
```

### Negative / Failure Path — Verifying Impossibility & Mutant Rejection
```bash
# Run the dedicated negative, hygiene, & mutant-killing tests (confirms x^3 over F_2 fails and corrupted certificates are rejected)
pytest -v tests/test_all.py -k "mutant or hygiene or bruteforce"
```

## Architecture, Governance & Limitations

- **Architecture & Threat Model:** [`docs/architecture.md`](docs/architecture.md), [`docs/threat-model.md`](docs/threat-model.md), [`docs/adr/`](docs/adr/)
- **Verification, Claims & Limitations:** [`CLAIMS.md`](CLAIMS.md), [`LIMITATIONS.md`](LIMITATIONS.md), [`docs/verification.md`](docs/verification.md), [`REPLICATION.md`](REPLICATION.md), [`ERRATA.md`](ERRATA.md)
- **Legal, AI Disclosure & Ethics:** [`docs/legal-and-ethics.md`](docs/legal-and-ethics.md), [`LICENSE`](LICENSE), [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md)

## Attribution & Primary Literature

- A. Vinciguerra, *An Operator Approach to Register Programs for Catalytic Computing*, [`arXiv:2609.18692`](https://arxiv.org/abs/2609.18692) (Sep 2026).
- G. Morse, *Unrestricted Boolean Multiplicative Complexity of Four-Term Binary Polynomial Multiplication: Rational Places, Hasse Jets, and the Failure of Nonlinear Feedback*, [`arXiv:2608.30238`](https://arxiv.org/abs/2608.30238) (Aug 2026).
- Y. Alekseev, Y. Filmus, I. Mertz, A. Smal, and A. Vinciguerra, *Catalytic Computing and Register Programs Beyond Log-Depth*, MFCS 2025, LIPIcs 345, pp. 6:1–6:18, [`doi:10.4230/LIPIcs.MFCS.2025.6`](https://doi.org/10.4230/LIPIcs.MFCS.2025.6) ([`arXiv:2504.17412`](https://arxiv.org/abs/2504.17412)).
- M. Ben-Or and R. Cleve, *Computing Algebraic Formulas Using a Constant Number of Registers*, SIAM J. Comput. 21(1) (1992), pp. 54–58, [`doi:10.1137/0221006`](https://doi.org/10.1137/0221006) (prior work for `T4`).
- J. Boyar and M. G. Find, *Multiplicative complexity of vector valued Boolean functions*, Theoretical Computer Science 720 (2018), pp. 36–46, [`doi:10.1016/j.tcs.2018.02.023`](https://doi.org/10.1016/j.tcs.2018.02.023).

No third-party copyrighted PDFs are redistributed in this repository.
