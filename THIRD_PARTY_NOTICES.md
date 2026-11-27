<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Third-Party Notices (`THIRD_PARTY_NOTICES.md`)

External specifications, licenses, and toolchains referenced or installed by package managers for `catalytic-register-frontiers`. No third-party copyrighted papers or PDFs are bundled in this repository.

| Component | Source / URL | License | Used for |
|---|---|---|---|
| Contributor Covenant 2.1 (`CODE_OF_CONDUCT.md`) | https://www.contributor-covenant.org/version/2/1/code_of_conduct.html | CC-BY-4.0 | Community Code of Conduct |
| Lean 4.35.0 (`lean`, `lake`, `leanchecker`, `con-leche`, `con-ron`, `nanoda_bin`) | https://github.com/leanprover/lean4 | Apache-2.0 | Formal proof kernel & external multi-kernel verification |
| CaDiCaL 2.1.2 (bundled with Lean 4.35.0 toolchain) | https://github.com/arminbiere/cadical | MIT | Exact SAT/UNSAT verification in `experiments/exp4_boolean_mc_companion.py` |
| Tectonic | https://tectonic-typesetting.github.io/ | MIT | Reproducible AMS-LaTeX PDF compilation |
| Python 3.13.12 (`pytest`, `hypothesis`, `matplotlib`, `numpy`, `scipy`, `ruff`, `mypy`) | Pinned in `requirements.lock.txt` | PSF / MIT / BSD / MPL-2.0 | Exact arithmetic, property testing, deterministic figures, static checks |
| Build Standard for LLMs v1.2.0 (`scripts/Audit-Repo.ps1`, `scripts/audit-checks.tsv`, `repo-standard.schema.json`) | Owner standard (Alex Donahue, `0thernes`) | CC-BY-4.0 / Apache-2.0 | Repository compliance scoring |
