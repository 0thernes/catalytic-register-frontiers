<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Positive-Characteristic Dichotomy and Optimal Three-Register Exponents in Passive Catalytic Register Programs

[![Version 1.0.0](https://img.shields.io/badge/version-1.0.0-blue.svg)](VERSION)
[![Lean 4.35.0 Zero-Mathlib](https://img.shields.io/badge/Lean-4.35.0%20(zero--Mathlib)-brightgreen.svg)](lean/lean-toolchain)
[![6 Kernels Verified](https://img.shields.io/badge/kernels-6%2F6%20PASS-brightgreen.svg)](results/six_kernel_audit.txt)
[![Code License: Apache-2.0](https://img.shields.io/badge/code%20license-Apache--2.0-blue.svg)](LICENSE)
[![Docs License: CC-BY-4.0](https://img.shields.io/badge/docs%20license-CC--BY--4.0-lightgrey.svg)](LICENSE)
[![Status: Preprint — Not Peer Reviewed](https://img.shields.io/badge/status-preprint%20(not%20peer%20reviewed)-yellow.svg)](LIMITATIONS.md)

A zero-Mathlib Lean 4.35.0 formalization, exact-arithmetic verification suite, and AMS-LaTeX preprint settling the exact two-register prime-field frontier and strictly improving the three-register catalytic powering exponent of Vinciguerra (`arXiv:2609.18692`).

**Author:** Alexander S. Donahue (Independent Researcher, Spokane, WA, USA · ORCID [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648) · `0_0@0thernes.art`)  
**Maintenance status:** active independent research artifact (`v1.0.0`, 2026-11-24) · **Frozen White Paper:** [`dist/Donahue_2026_catalytic_register_frontiers.pdf`](dist/Donahue_2026_catalytic_register_frontiers.pdf)

> **Epistemic Status:** All 20 headline theorems, corollaries, and literal commutative-ring soundness bridges (`T1`, `T1a`–`T1e`, `T1s`, `T1es`, `T2`, `T2b`, `T3a`–`T3i` — including complete 4-register passive powering for all $N \ge 1$ and algebraic vector streaming frequency moments $F_D(\mathbf{f})$, `T4`) plus concrete `0 ≠ 1` non-vacuity witnesses (`NonVacuity`, including product ring `Fin 3 → ModP 13` for `T3i`) are machine-checked from first principles in **zero-Mathlib Lean 4.35.0** across **14 module files** (8,069 lines, max 1,361 lines) and **6 kernel runs / 5 independent implementations** (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche --verified`, `con-ron --verified`, `nanoda_bin 0.4.19`) with 0 forbidden tokens and 0 linter warnings. All 8/8 companion SAT UNSAT proofs are archived as ASCII LRAT certificates (`results/sat_certs/`), independently verified (`scripts/verify_lrat.py`), and cross-checked against both brute-force enumeration and a second independent CNF encoder (`tests/test_all.py`). This preprint has **not** undergone external peer review; see [`CLAIMS.md`](CLAIMS.md) (including explicit falsification criteria) and [`LIMITATIONS.md`](LIMITATIONS.md).

---

## 5-Second Formal Verification Proof (Verbatim `#print axioms`)

Exact output of `cd lean && lake env lean VerifyAxioms.lean` (22/22 audited declarations, archived in [`results/lean_axioms.txt`](results/lean_axioms.txt), cross-checked in CI; [`results/six_kernel_audit.txt`](results/six_kernel_audit.txt) records all 6 passing kernel runs including `con-leche --verified` and `con-ron --verified` accepting 3,525 declarations and `nanoda_bin 0.4.19` checking 3,838 declarations with `unpermitted_axiom_hard_error=true`):

```text
'Catalytic.Solution.t1_digit_sum_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1a_two_access_frobenius_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1b_f2_saturation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1c_impossibility_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1d_vinciguerra_recovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1e_extension_field_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1s_pass2_ring_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Catalytic.Solution.t1es_pass2_gf4_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
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
| `T1`, `T1a`–`T1e`, `T1s`, `T1es` (`InRPPass2`, `GF4`, `execRing`, `execAlg`) | Vinciguerra (`arXiv:2609.18692`), Def. 2.2, Thm. 3.5 | `IsPrime 2,3,5,7`; `ModP 5` ($\mathrm{char}=5$); `GF4` (`GF4Hom.id`, $0 \neq 1$) | General $\mathbb{F}_{p^e}$ ($e \ge 2$) closed form; $r \ge 3$ |
| `T2`, `T2b` (`BilinInstr`, `DistinctBilinInstr`) | Strictly bilinear & distinct-operand Def. 2.2 | `F2 = ModP 2` ($0 \neq 1$), $k = 2$, $x = 1$ | Odd characteristics |
| `T3a`–`T3i` (`Pass3InstrR`, `Pass4Instr`, `instCRingFinFun`, `prog5_x7`..`prog9_x15`, global $t=8$ opt, 4-reg powering & streaming $F_D$) | Vinciguerra (`arXiv:2609.18692`), Def. 2.2, Cor. 4.3.1, Cor. 5.1.1; Alekseev et al. (MFCS 2025, Lem. 8) | `ModP 5, 7, 11, 13` ($0 \neq 1$) with explicit $D_5^{-1}\!\dots D_9^{-1}$, $12!^{-1}$, $6!^{-1}$ | Bad primes dividing $D_t$ or $(\ell+1)!$; uniform $t \ge 10$; upper bounds; bit-space accounting |
| `T4_BalancedMultilinearProduct` (`CatOp`) | Zero-workspace strictly distinct bilinear ops | `Int` ($0 \neq 1$), $d = 4$, 36 ops, clean restoration | Non-power-of-two $d$ without padding; lower-bound optimality |

---

## Core Mathematical Results

1. **Theorem T1 — Complete Base-$p$ Digit-Sum Dichotomy for $\mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t)$** ([`DigitSumDichotomy.lean`](lean/Catalytic/DigitSumDichotomy.lean)):
   For every prime $p$, every budget $t \ge 1$, and every univariate polynomial $f(x) = \sum_{d \ge 0} \alpha_d x^d \in \mathbb{F}_p[x]$:
   $$f \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t) \quad \Longleftrightarrow \quad \forall\, d \ge 2 \text{ with } \alpha_d \neq 0,\;\; s_p(d) \le \min(p - 1,\; t - 1).$$
   - **T1a:** $x^{p^m} \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, 2)$ for all $m \ge 0$ ($D_{2,\mathbb{F}_p}^{\mathrm{pass}}(2) = +\infty$).
   - **T1b:** Exact $\mathbb{F}_2$ saturation: $x^3 \notin \mathrm{RP}_{\mathbb{F}_2}^{\mathrm{pass}}(2, t)$ for **all** $t \ge 0$.
   - **T1c:** Universal impossibility threshold: whenever $s_p(d) \ge p$, $x^d \notin \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t)$ for all $t \ge 1$.
   - **T1d:** Characteristic-0 recovery: whenever $2 \le d < p$, $x^d \in \mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2, t) \iff t \ge d + 1$.

2. **Theorem T2 — Strictly Bilinear 2-Access Frobenius Collapse over Characteristic 2** ([`BilinearFrobenius.lean`](lean/Catalytic/BilinearFrobenius.lean)):
   Under strictly bilinear updates $R_i \leftarrow R_i + R_j R_\ell$ ($j, \ell \neq i$, passive $R_0$), for every $k \ge 1$ and every `Char2CRing` $R$, $x^{2^k}$ is cleanly computed in $k + 1$ registers, $4k - 2$ bilinear ops, and **2 input accesses**.

3. **Theorem T3 — Strict Improvement Over Vinciguerra's 3-Register Powering, Streaming, and Matrix-Powering Exponent** ([`ThreeRegisterBreakthrough.lean`](lean/Catalytic/ThreeRegisterBreakthrough.lean)):
   Explicit Definition 2.2 Pascal-row shear loops give $x^7 \in \mathrm{RP}(3, 5)$ ($D_5 = 576$, $\log_7 5 \approx 0.82709$), $x^9 \in \mathrm{RP}(3, 6)$ ($D_6 = 382{,}500{,}000$, $\log_9 6 \approx 0.81546$), $x^{11} \in \mathrm{RP}(3, 7)$ ($\log_{11} 7 \approx 0.81151$), $x^{13} \in \mathrm{RP}(3, 8)$ ($\mathbf{\log_{13} 8 \approx 0.81071}$ — unique global integer minimizer of $\log_{2t-3} t$ for all $t \ge 4$), and $x^{15} \in \mathrm{RP}(3, 9)$ ($\log_{15} 9 \approx 0.81137$), strictly improving Vinciguerra's $\log_5 4 \approx 0.86135$ for $4$-register powering (Cor. 4.3.1) and catalytic streaming (Cor. 5.1.1) via `prog8_x13`, and tightening non-commutative matrix powering (Thm. 5.2) to $\log_7 5 \approx 0.82709$ at the exact $r = 3$ scalar register tier via `prog5_x7`.

4. **Theorem T4 — Balanced Zero-Workspace Bilinear Multilinear Product** ([`BalancedProduct.lean`](lean/Catalytic/BalancedProduct.lean)):
   Over any commutative ring $R$, for $d = 2^k$, cleanly computes $x_0 \cdots x_{d-1}$ with zero clean workspace, $\log_2 d + 2$ registers, strictly pairwise-distinct indices, and exact primitive op count $(7d^2 - 4)/3$.

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

Expected result: 17/17 Lean jobs built with 0 warnings, `leanchecker`, `leanchecker-paranoid`, `con-leche`, and `con-ron` exit 0, all 21 `pytest` / Hypothesis / mutant / differential-SAT / LRAT / REUSE / SBOM / workflow / schema / SVG / factorization / consistency tests PASS, 3 deterministic PDFs generated, 0-warning Tectonic PDF compile, 100% `MANIFEST.sha256` verification, and DigiCert RFC 3161 `Verification: OK`.

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
- J. Boyar and M. G. Find, *Multiplicative complexity of vector valued Boolean functions*, Theoretical Computer Science 720 (2018), pp. 36–46, [`doi:10.1016/j.tcs.2018.02.023`](https://doi.org/10.1016/j.tcs.2018.02.023).

No third-party copyrighted PDFs are redistributed in this repository.
