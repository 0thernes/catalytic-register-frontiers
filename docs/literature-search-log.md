<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Literature Search & Citation Integrity Log (`docs/literature-search-log.md`)

Dated record of primary literature checks, novelty queries, and automated DOI/URL/retraction resolution (Defensible Independent AI Research Playbook Checklist #15–#16, Pass 4 & Pass 5).

## 1. Novelty & Prior-Art Search Log

| Date | Database / Source | Query / Scope | Outcome & Novelty Assessment |
|---|---|---|---|
| 2026-11-23 | arXiv (`cs.CC`) | Primary read of A. Vinciguerra, `arXiv:2609.18692v1` (Sep 16, 2026) | Confirms Vinciguerra restricts §3 lower bounds (Thms 3.2, 3.3, 3.5) to $\operatorname{char}(K) = 0$, gives $r$-register 4-call bound $x^{2r-1}$ (for $r=3$: $x^5$ at $t=4$, $\log_5 4 \approx 0.86135$), and explicitly asks in §6 whether additional input accesses increase $D_{r,K}^{\mathrm{pass}}(t)$. Our `T1`–`T3` answer both questions directly. |
| 2026-11-23 | arXiv (`cs.CC`) | Primary read of G. Morse, `arXiv:2608.30238v1` (Aug 31, 2026) | Confirms Morse settles $\mathrm{MC}_\wedge(\mathrm{Mul}_4) = 9$ (Lean 4 + Mathlib) and isolates the $n=5$ multi-defect program; Boyar–Find general $(n, m)$ quadratic-circuit optimality remains open. |
| 2026-11-23 | Web / OEIS | `"576" "382500000" OEIS OR catalytic register program` | No prior catalytic register-program sequence matching $D_5 = 576$, $D_6 = 382{,}500{,}000$ found. |
| 2026-11-23 | Web / OEIS | `"1, 8, 36, 148, 596" OEIS OR "(7*4^n - 4)/3"` | Recurrence $a_n = 4 a_{n-1} + 4, a_0 = 1$ is standard algebraically; its realization as the exact op count of a zero-workspace strictly-distinct-index balanced catalytic product tree (`T4`, $\log_2 d + 2$ registers) is framed honestly as an explicit structural construction (not overclaimed as an unproven lower bound). |
| 2026-11-23 | arXiv / Google Scholar | Positive-characteristic catalytic register programs (`RP^{pass}_{F_p}(2,t)` digit-sum dichotomy) | No prior characterization of $\mathrm{RP}_{\mathbb{F}_p}^{\mathrm{pass}}(2,t)$ via $s_p(d) \le \min(p-1, t-1)$ found as of 2026-11-23; framed conservatively as "to our knowledge, not previously characterized or formalized." |

## 2. Live Reference Resolution & Retraction Audit (Crossref / DataCite / arXiv API, 2026-11-23)

All 10 entries in `paper/references.bib` were audited against Crossref API (`api.crossref.org/works/<doi>`), DataCite/Dagstuhl, and arXiv API (`export.arxiv.org/api/query`) on 2026-11-23. **Zero retractions (`update-to: []`)** were detected. Two pre-release bibliographic errors were caught and corrected (`ERRATA.md`):

| BibTeX Key | Verified Identifier | HTTP / API Verdict | Retraction Check |
|---|---|---|---|
| `Vinciguerra2026` | `arXiv:2609.18692` | HTTP 200 + arXiv API exact match (Sep 16, 2026) | Clean (preprint) |
| `Morse2026` | `arXiv:2608.30238` | HTTP 200 + arXiv API exact match (Aug 31, 2026) | Clean (preprint) |
| `BCKLS2014` | `10.1145/2591796.2591874` | Crossref OK (STOC 2014, pp. 857–866) | `updates=[]` |
| `CookMertz2024` | `10.1145/3618260.3649664` | Crossref OK (STOC 2024, pp. 1268–1278) | `updates=[]` |
| `AFM2025` | `10.4230/LIPIcs.MFCS.2025.6` / `arXiv:2504.17412` | HTTP 200 Dagstuhl DROPS + HTTP 200 arXiv (MFCS 2025, LIPIcs 345, pp. 6:1–6:18) | Clean (corrected from pre-release draft) |
| `BenOrCleve1992` | `10.1137/0221006` | Crossref OK (SIAM J. Comput. 21(1), pp. 54–58) | `updates=[]` |
| `CoppersmithGrossman1975` | `10.1137/0129051` | Crossref OK (SIAM J. Appl. Math. 29(4), pp. 624–627) | `updates=[]` |
| `BoyarFind2018` | `10.1016/j.tcs.2018.02.023` | Crossref OK (TCS 720, pp. 36–46, 2018) | `updates=[]` (corrected from pre-release draft) |
| `Lucas1878` | `10.2307/2369308` | Crossref OK (AJM 1, pp. 184–240, 289–321, 1878) | `updates=[]` |
| `Williams2025` | `10.1145/3717823.3718225` / `arXiv:2502.17779` | Crossref OK (STOC 2025, pp. 13–23) + arXiv API 200 | `updates=[]` |
