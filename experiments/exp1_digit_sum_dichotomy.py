# SPDX-License-Identifier: Apache-2.0
"""
Experiment 1: Independent Exact Verification of Theorem T1 (Base-p Digit-Sum Dichotomy)
and Extension-Field Behavior over F_4.

Verifies over exact finite-field arithmetic (no floating point):
  1. For primes p in {2, 3, 5, 7} and degrees d = 2..120 (d = 2..100 for p = 7):
     - Whenever s_p(d) < p, the forward finite-difference weights on A = {0..s_p(d)}
       satisfy sum_{a=0}^{s} h_a (R + a*x)^d == x^d identically in F_p[R, x].
     - Exact linear-algebra rank / solvability checks confirm that:
         * for s_p(d) < p, NO subset A subseteq F_p of size <= s_p(d) can compute x^d;
         * for s_p(d) >= p, even the FULL field A = F_p cannot compute x^d!
  2. Exact extension-field comparison over F_4 = F_2[w]/(w^2 + w + 1) for d = 1..16.
"""

from __future__ import annotations

import json
import pathlib
from itertools import combinations


def digit_sum(p: int, n: int) -> int:
    s = 0
    while n > 0:
        s += n % p
        n //= p
    return s


def binom_mod_p(n: int, k: int, p: int) -> int:
    res = 1
    while n > 0 or k > 0:
        ni, ki = n % p, k % p
        if ki > ni:
            return 0
        num = 1
        den = 1
        for i in range(ki):
            num = (num * (ni - i)) % p
            den = (den * (i + 1)) % p
        res = (res * num * pow(den, p - 2, p)) % p
        n //= p
        k //= p
    return res


def rref_solvable_fp(cols: list[list[int]], rhs: list[int], p: int) -> bool:
    nrows = len(rhs)
    ncols = len(cols)
    mat = [[cols[c][r] % p for c in range(ncols)] + [rhs[r] % p] for r in range(nrows)]
    row = 0
    for col in range(ncols):
        piv = None
        for r in range(row, nrows):
            if mat[r][col] != 0:
                piv = r
                break
        if piv is None:
            continue
        mat[row], mat[piv] = mat[piv], mat[row]
        iv = pow(mat[row][col], p - 2, p)
        mat[row] = [(v * iv) % p for v in mat[row]]
        for r in range(nrows):
            if r != row and mat[r][col] != 0:
                fac = mat[r][col]
                mat[r] = [(mat[r][k] - fac * mat[row][k]) % p for k in range(ncols + 1)]
        row += 1
    for r in range(row, nrows):
        if mat[r][ncols] != 0:
            return False
    return True


def verify_prime_fields() -> dict:
    summary = {}
    for p in [2, 3, 5, 7]:
        max_d = 120 if p <= 5 else 100
        feasible_checked = 0
        impossible_checked = 0
        lower_bound_checked = 0
        phase_records: list[dict[str, int | bool | None]] = []

        for d in range(2, max_d + 1):
            s = digit_sum(p, d)
            active_js = [j for j in range(d + 1) if binom_mod_p(d, j, p) != 0]
            rhs = [1 if j == d else 0 for j in active_js]

            if s < p:
                # 1. Verify exact finite-difference sufficiency on A = {0..s}
                fact_s = 1
                for k in range(1, s + 1):
                    fact_s = (fact_s * k) % p
                inv_fact = pow(fact_s, p - 2, p)
                h = []
                for a in range(s + 1):
                    sign = -1 if ((s - a) & 1) else 1
                    ch = binom_mod_p(s, a, p)
                    h.append((inv_fact * sign * ch) % p)
                for j in range(d + 1):
                    b = binom_mod_p(d, j, p)
                    if b == 0:
                        continue
                    val = sum(h[a] * (1 if j == 0 else pow(a, j, p)) for a in range(s + 1)) % p
                    coeff = (b * val) % p
                    expected = 1 if j == d else 0
                    assert coeff == expected, f"Sufficiency failed at p={p}, d={d}, j={j}"
                feasible_checked += 1

                # 2. Verify impossibility for EVERY subset A of size s (exact tightness)
                # For small p (p <= 5) check all subsets; for p=7 check up to d=40
                if p <= 5 or d <= 40:
                    for A in combinations(range(p), s):
                        cols = [[1 if j == 0 else pow(a, j, p) for j in active_js] for a in A]
                        assert not rref_solvable_fp(cols, rhs, p), (
                            f"Lower bound violated at p={p}, d={d}, A={A}"
                        )
                    lower_bound_checked += 1
                if d <= 50:
                    phase_records.append({"d": d, "s_p": s, "min_t": s + 1, "feasible": True})
            else:
                # Verify impossibility even with ALL p elements of F_p!
                cols = [[1 if j == 0 else pow(a, j, p) for j in active_js] for a in range(p)]
                assert not rref_solvable_fp(cols, rhs, p), f"Impossibility failed at p={p}, d={d}"
                impossible_checked += 1
                if d <= 50:
                    phase_records.append({"d": d, "s_p": s, "min_t": None, "feasible": False})

        summary[f"F_{p}"] = {
            "prime": p,
            "max_d_tested": max_d,
            "feasible_degrees_verified": feasible_checked,
            "exact_lower_bound_subset_audits": lower_bound_checked,
            "impossible_degrees_verified": impossible_checked,
            "phase_diagram_d2_to_50": phase_records,
        }
        print(
            f"[VERIFIED] F_{p} (d=2..{max_d}): {feasible_checked} feasible (exact s_p+1), "
            f"{lower_bound_checked} exhaustive subset lower-bound audits, "
            f"{impossible_checked} impossible (s_p >= {p})."
        )
    return summary


def verify_extension_field_f4() -> list[dict]:
    def f4_add(a: int, b: int) -> int:
        return a ^ b

    def f4_mul(a: int, b: int) -> int:
        a0, a1 = a & 1, (a >> 1) & 1
        b0, b1 = b & 1, (b >> 1) & 1
        return ((a0 & b0) ^ (a1 & b1)) | (((a0 & b1) ^ (a1 & b0) ^ (a1 & b1)) << 1)

    def f4_pow(a: int, e: int) -> int:
        res, base = 1, a
        while e > 0:
            if e & 1:
                res = f4_mul(res, base)
            base = f4_mul(base, base)
            e >>= 1
        return res

    inv4 = {1: 1, 2: 3, 3: 2}

    def solvable_f4(cols: list[list[int]], rhs: list[int]) -> bool:
        nrows, ncols = len(rhs), len(cols)
        mat = [[cols[c][r] for c in range(ncols)] + [rhs[r]] for r in range(nrows)]
        row = 0
        for col in range(ncols):
            piv = next((r for r in range(row, nrows) if mat[r][col] != 0), None)
            if piv is None:
                continue
            mat[row], mat[piv] = mat[piv], mat[row]
            iv = inv4[mat[row][col]]
            mat[row] = [f4_mul(v, iv) for v in mat[row]]
            for r in range(nrows):
                if r != row and mat[r][col] != 0:
                    fac = mat[r][col]
                    mat[r] = [f4_add(mat[r][k], f4_mul(fac, mat[row][k])) for k in range(ncols + 1)]
            row += 1
        return all(mat[r][ncols] == 0 for r in range(row, nrows))

    records = []
    for d in range(1, 17):
        active_js = [j for j in range(d + 1) if (j & d) == j]
        rhs = [1 if j == d else 0 for j in active_js]
        min_t = None
        for t in range(1, 5):
            if any(
                solvable_f4([[1 if j == 0 else f4_pow(a, j) for j in active_js] for a in A], rhs)
                for A in combinations([0, 1, 2, 3], t)
            ):
                min_t = t
                break
        records.append({"d": d, "s_2": digit_sum(2, d), "min_t_F4": min_t})

    # Sanity assertions matching Remark on extension fields
    by_d = {r["d"]: r["min_t_F4"] for r in records}
    assert by_d[3] == 4 and by_d[5] == 3 and by_d[7] is None and by_d[10] == 3 and by_d[16] == 2
    print("[VERIFIED] F_4 extension-field spectrum (d=1..16): x^5 -> 3 calls, x^3 -> 4 calls, x^7 impossible.")
    return records


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parent.parent
    out_path = repo / "results" / "exp1_digit_sum.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    data = {
        "theorem": "T1 (Base-p Digit-Sum Dichotomy for RP^{pass}_{F_p}(2, t))",
        "prime_fields": verify_prime_fields(),
        "extension_field_F4": verify_extension_field_f4(),
    }
    out_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
