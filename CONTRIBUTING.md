<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Contributing to `catalytic-register-frontiers`

Thanks for your interest. This is an independent, one-person research repository run lean under the Build Standard for LLMs (v1.2.0).

## Workflow

- Work goes straight to `main`. There are no pull-request gates, required checks, git hooks, or forced signing gates, and none will be added.
- CI runs on every push and is informational: a red run is a finding to fix in a follow-up commit, never a barrier.
- Outside contributions, counterexamples, literature pointers, or independent replications: open an issue using `.github/ISSUE_TEMPLATE/` (bug/finding, feature, or question form).

## Setup and Commands

```bash
just setup       # verify pinned Lean 4.35.0 toolchain & install Python requirements
just build       # clean-build zero-Mathlib Lean 4.35 proofs & VerifyAxioms
just test        # run pytest (exact arithmetic, Hypothesis property tests, mutant checks, SAT equivalence)
just lint        # run ruff & mypy (report-only)
just reproduce   # end-to-end clean reproduction: Lean + experiments + tests + figures + PDF + SHA-256
just audit       # score this repo against Build Standard v1.2.0 (report-only)
```

On Windows PowerShell without `just`, run `pwsh -NoProfile -File scripts/run_all.ps1 -Task all`.

## Verification Expectations

- **Lean 4.35 proofs:** Zero external dependencies, `module` header in every `.lean` file, zero `sorry` / `admit` / `native_decide` / custom `axiom` / `@[extern]`, strict 3-axiom allowlist `[propext, Classical.choice, Quot.sound]`, and explicit non-vacuity witnesses in `lean/Catalytic/NonVacuity.lean`.
- **Claims & tests:** Every mathematical or computational claim must have a tiered row in [`CLAIMS.md`](CLAIMS.md) with an explicit falsification condition, and every bug fix gets a regression test in `tests/test_all.py`.
- **Finding taxonomy:** Classify every finding as exactly one of `bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, or `blindspot` (see [`docs/glossary.md`](docs/glossary.md)).
- **Changelog:** Update [`CHANGELOG.md`](CHANGELOG.md) in the same commit.

AI agents: read [`AGENTS.md`](AGENTS.md) first.
