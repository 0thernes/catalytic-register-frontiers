<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Verification Ledger (`docs/verification.md`)

Maps every applicable rung of Part B of the Build Standard for LLMs (v1.1.0) and the *Defensible Independent AI Research Playbook* (v1.1) to concrete commands and evidence artifacts in `catalytic-register-frontiers`.

| Rung | Requirement | Command / Artifact | Status |
|---|---|---|---|
| B01–B02 | Clean-clone reproducible build & pinned toolchains/lockfiles | `just reproduce`, `lean/lean-toolchain`, `lean/lake-manifest.json`, `pyproject.toml`, `requirements.lock.txt` | **PASS** |
| B03 | Determinism checks | Deterministic vector PDFs (`CreationDate=None`), exact integer/rational JSON outputs verified in `tests/test_all.py` | **PASS** |
| B04–B05 | Claims ledger & falsifiable tests per claim | `CLAIMS.md` (with explicit refutation criteria) + `tests/test_all.py` | **PASS** |
| B06–B07 | Negative tests & regression tests per fixed bug | `T1b`/`T1c` impossibility proofs, `test_negative_and_regression_guards` in `tests/test_all.py` | **PASS** |
| B08 | Golden / snapshot verification | `results/exp1..4.json` + `results/lean_axioms.txt` verified against live recomputation & `MANIFEST.sha256` | **PASS** |
| B10 | Property-based tests | `hypothesis` randomized tests across `T1`–`T4` in `tests/test_all.py` | **PASS** |
| B11–B12 | Differential testing & independent reference oracle | Lean kernel proofs independently cross-checked by Python exact polynomial / finite-field evaluators + brute-force SAT encoder oracle | **PASS** |
| B13 | Mutation testing | `test_mutant_killing_certificates` in `tests/test_all.py` mutating `T1`–`T4` certificates & asserting 100% mutant kill rate | **PASS** |
| B14 | Metamorphic testing | Catalytic shift-invariance (`st -> st + delta`) and Frobenius scaling invariances verified under Hypothesis in `tests/test_all.py` | **PASS** |
| B17–B18 | Static analysis & strict type checking (report-only) | `ruff check experiments scripts tests` and `mypy experiments scripts tests` + Lean core linters (`autoImplicit=false`, `linter.unusedVariables=true`) | **PASS** |
| B22 | Formal specification and proof | Zero-Mathlib `lean/` + 6-kernel audit (`results/six_kernel_audit.txt`) + `lean/Catalytic/NonVacuity.lean` | **PASS** |
| B35–B36 | Security scanning, SBOM, & threat model | CI secret scan, `sbom.cdx.json`, `docs/threat-model.md` | **PASS** |
| B37–B38 | Release checksums & SLSA attestations | `MANIFEST.sha256` + `.github/workflows/release.yml` (`SHA256SUMS` + `actions/attest-build-provenance@v2`) | **PASS** |
| B40–B43 | Audit trail, limitations, refutation criteria, replication protocol | `docs/run-log.md`, `LIMITATIONS.md`, `CLAIMS.md`, `REPLICATION.md` | **PASS** |
| B44 | Independent replication | Clean-room self-replication logged in `REPLICATION.md`; external human replicator pending (explicitly marked) | **PARTIAL (external pending)** |
| B45 | Peer & red-team review | `docs/reviews/01-10-pass-review.md`, `docs/plan/00-redteam.md` (external peer review pending) | **PASS (internal red-team)** |

## Release Verification Commands

```bash
sha256sum -c MANIFEST.sha256
# After GitHub release v1.0.0 is published:
gh attestation verify dist/Donahue_2026_catalytic_register_frontiers.pdf --repo 0thernes/catalytic-register-frontiers
```
