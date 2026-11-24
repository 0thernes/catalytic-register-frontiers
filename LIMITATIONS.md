<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Limitations, Epistemic Scope, and Negative Findings (`LIMITATIONS.md`)

This document explicitly states what `catalytic-register-frontiers` **does not** prove, documents negative computational findings, and classifies discovered defects using the taxonomy `{bug, error, issue, problem, dilemma, conflict}`.

## 1. Explicit Scope Boundaries

1. **Prime fields vs. extension fields (Theorem T1):**
   Theorem `T1` (`rp_pass_two_iff`) holds unconditionally for every **prime field** $\mathbb{F}_p$. It does **not** hold verbatim for non-prime finite fields $\mathbb{F}_{p^e}$ ($e \ge 2$): as verified in `exp1_digit_sum_dichotomy.py`, over $\mathbb{F}_4$, $x^5$ is computable in $3$ accesses and $x^3$ in $4$ accesses, while $x^7$ is impossible for all $t$.
2. **Formal polynomial cleanliness vs. functional evaluation:**
   Cleanliness in Definition 2.2 is formal polynomial identity in $R[O, R_1, \dots, R_{r-1}, x]$ (equivalently, clean evaluation over every commutative $R$-algebra). If one only required pointwise agreement as functions $\mathbb{F}_p \to \mathbb{F}_p$, then $x^p \equiv x$ functionally and degree $> p - 1$ would collapse.
3. **Finite family ($t \in \{5, 6, 7, 8, 9\}$) vs. all $t \ge 4$ (Theorem T3):**
   Our Lean 4.35 proofs establish $x^7 \in \mathrm{RP}_K^{\mathrm{pass}}(3, 5)$, $x^9 \in \mathrm{RP}_K^{\mathrm{pass}}(3, 6)$, $x^{11} \in \mathrm{RP}_K^{\mathrm{pass}}(3, 7)$, and $x^{13} \in \mathrm{RP}_K^{\mathrm{pass}}(3, 8)$ (and exact Python verifies $x^{15}$ at $t = 9$). While $t = 8$ is already the unique integer global minimizer of $\log_{2t-3} t$, proving $D_{3,\mathbb{Q}}^{\mathrm{pass}}(t) = 2t - 3$ for all $t \ge 4$ (including matching upper bounds) remains open.
4. **Bad-prime restrictions for $t = 6, 7, 8$:**
   While `prog5_x7` ($\epsilon = 0.827087$) avoids only $\{2, 3\}$ (matching Vinciguerra's $t = 4$ characteristic requirement!), `prog6_x9` avoids $\{2, 3, 5, 17\}$, and `prog7_x11` / `prog8_x13` avoid two larger primes arising from clearing denominators (`538423, 2512452073` and `137, 1602207194491`). Alternative non-uniform shift sets can shift these bad primes, and all programs hold unconditionally in characteristic $0$.
5. **No $r = 4$ exponent improvement:**
   Our exploratory exact modular search over $r = 4$ triangular closed loops (`deg_v = 2, 3, 4`, `wt(w) = 3..9`, unrestricted monomials) reached $N = 7$ ($t=4$), $N = 9$ ($t=5$, $\epsilon = 0.73249$), and $N = 11$ ($t=6$, $\epsilon = 0.74722$). Because degree grew as $2t - 1$ rather than faster, this family did **not** beat Vinciguerra's $r = 4$ exponent $\log_7 4 \approx 0.71241$.
6. **Boyar–Find conjecture & SAT certificate boundary:**
   `exp4_boolean_mc_companion.py` provides supporting SAT-certified evidence (0 counterexamples across sampled degree-3 cancellations and hard $n = 4$ maps) and does **not** prove or refute Boyar–Find (TCS 720, 2018) or Morse's $n = 5$ conjecture (`arXiv:2608.30238`). While our CNF encoder is verified against an independent exhaustive brute-force enumerator on all 16 $n=2$ functions ($k=0, 1$) and canonical $n=3$ benchmarks in `tests/test_all.py`, the CaDiCaL 2.1.2 UNSAT certificates have **not** yet been replayed through CakeML's `cake_lpr` (external tool not installed locally — classified as `problem`; no Tier-1 Lean theorem depends on SAT).
7. **Peer-review & external provenance status:**
   This manuscript has **not** undergone external peer review or external second-machine human reproduction (`REPLICATION.md`). Post-push external steps (live GitHub Actions CI/SLSA attestations, Zenodo/OSF DOI minting, Software Heritage SWHID, Palomar 40-char SHA registration, OpenTimestamps `.ots` proof) remain pending publication (`ROADMAP.md`). Correctness of all Tier-1 theorems is certified independently by six Lean 4.35 verification kernels.

## 2. Classified Engineering & Discovery Log

| Type | Observation | Resolution |
|---|---|---|
| `conflict` | Legacy notes cited `0thernes LLC` and MIT vs. Nov 2026 Playbook audit (no LLC legally formed; Apache-2.0 + CC-BY-4.0). | Resolved in `docs/adr/0002-epistemic-scope-and-identity.md`: author `Alexander S. Donahue` (independent researcher), Apache-2.0 + CC-BY-4.0. |
| `bug` | `Poly3.add` initially used well-founded recursion, preventing Lean kernel `rfl` reduction on `exec3Poly`. | Rewrote `Poly3.add` via nested structural recursion (`Poly3.addAux`), enabling pure kernel `rfl` across all 6 kernels. |
| `bug` | PowerShell `Out-File -Encoding ascii` wrapped/CRLF-encoded `leanexport` lines, causing `nanoda_bin` parser panic. | Wrote raw LF binary stream via Python `subprocess`; `nanoda_bin` then checked 3,183 declarations cleanly (exit 0). |
| `issue` | Trial-division prime factoring stalled on $t=9$'s 15-digit cofactor (`638970634117961`). | Upgraded `factor_primes` in `exp2` to Miller–Rabin + Pollard-Rho; runtime dropped to < 1 s. |
| `problem` | $t=5$ with `deg_w = 3` failed to reach $N = 7$, initially looking like an anomaly. | Discovered `deg_w = 2` unlocks $x^7$ at $t=5$ with tiny `D = 576` and bad primes ONLY `{2, 3}`! |
| `dilemma` | Balancing Lean `prog8_x13` kernel reduction depth (`maxRecDepth 4096`) against external checker performance. | Verified all 6 kernels (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche`, `con-ron`, `nanoda_bin`) accept `prog8_x13` in seconds with zero `native_decide`. |
