# SPDX-License-Identifier: Apache-2.0
"""
Experiment 2: Independent Exact Verification of Theorem T3
(3-Register Powering, Streaming, and Matrix-Powering Exponent Breakthrough).

Independently derives AND literally executes instruction-by-instruction in exact Z[x, u, v]
and Q[x, u, v] the passive-output 3-register catalytic programs for:
  * t = 4 -> x^5  (Vinciguerra arXiv:2609.18692 baseline, eps = log_5(4) = 0.861353)
  * t = 5 -> x^7  (NEW, deg_w=2, D=576, bad primes ONLY {2,3}, eps = log_7(5) = 0.827087)
  * t = 6 -> x^9  (NEW, deg_w=4, D=382500000, bad primes {2,3,5,17}, eps = log_9(6) = 0.815465)
  * t = 7 -> x^11 (NEW, deg_w=5, shifts=[0,1,2,3,4,5,7], eps = log_11(7) = 0.811508)
  * t = 8 -> x^13 (NEW, deg_w=6, shifts=[0..7], eps = log_13(8) = 0.810714 — OPTIMAL!)
  * t = 9 -> x^15 (NEW, deg_w=7, shifts=[0..7,9], eps = log_15(9) = 0.811229)

Also verifies exact modular execution over good prime fields F_p (p = 5, 7, 11, 13, 19)
and exact integer rational-separator inequalities for the exponent chain.
"""

from __future__ import annotations

import json
import math
import pathlib
from collections import defaultdict
from fractions import Fraction


def poly_add(p: dict, q: dict, s: Fraction = Fraction(1)) -> dict:
    r = dict(p)
    for k, v in q.items():
        nv = r.get(k, Fraction(0)) + s * v
        if nv == 0:
            r.pop(k, None)
        else:
            r[k] = nv
    return r


def poly_mul(p: dict, q: dict) -> dict:
    r: dict = defaultdict(Fraction)
    for kp, vp in p.items():
        for kq, vq in q.items():
            k = (kp[0] + kq[0], kp[1] + kq[1], kp[2] + kq[2])
            r[k] += vp * vq
    return {k: v for k, v in r.items() if v != 0}


def poly_pow(p: dict, e: int) -> dict:
    res = {(0, 0, 0): Fraction(1)}
    base = p
    while e > 0:
        if e & 1:
            res = poly_mul(res, base)
        base = poly_mul(base, base)
        e >>= 1
    return res


def solve_linear_Q(rows: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction] | None:
    m = len(rows)
    n = len(rows[0])
    A = [list(rows[i]) + [rhs[i]] for i in range(m)]
    piv_cols = []
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, m) if A[i][c] != 0), -1)
        if piv == -1:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = Fraction(1) / A[r][c]
        A[r] = [v * inv for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                fac = A[i][c]
                A[i] = [A[i][j] - fac * A[r][j] for j in range(n + 1)]
        piv_cols.append(c)
        r += 1
    if any(A[i][n] != 0 for i in range(r, m)):
        return None
    sol = [Fraction(0)] * n
    for i, c in enumerate(piv_cols):
        sol[c] = A[i][n]
    return sol


def is_probable_prime(n: int) -> bool:
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n == p:
            return True
        if n % p == 0:
            return False
    d, s = n - 1, 0
    while (d & 1) == 0:
        d >>= 1
        s += 1
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def pollard_rho(n: int) -> int:
    if n % 2 == 0:
        return 2
    for c in range(1, 50):
        x = 2
        y = 2
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d
    return n


def factor_primes(n: int) -> list[int]:
    primes: set[int] = set()
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53):
        while n % p == 0:
            primes.add(p)
            n //= p
    stack = [n] if n > 1 else []
    while stack:
        v = stack.pop()
        if v == 1:
            continue
        if is_probable_prime(v):
            primes.add(v)
            continue
        d = pollard_rho(v)
        if d == v:
            primes.add(v)
        else:
            stack.append(d)
            stack.append(v // d)
    return sorted(primes)


def lcm(a: int, b: int) -> int:
    return a // math.gcd(a, b) * b


def synthesize_and_verify_r3(t: int, shifts: list[int], deg_w: int, target_N: int) -> dict:
    fshifts = [Fraction(s) for s in shifts]
    # Lagrange annihilation weights a_m: sum_m a_m (u + s_m x)^deg_w == 0
    a = []
    for m in range(t):
        den = Fraction(1)
        for j in range(t):
            if j != m:
                den *= (fshifts[m] - fshifts[j])
        a.append(Fraction(1) / den)

    a_den = 1
    for am in a:
        a_den = lcm(a_den, am.denominator)
    a_int = [int(am * a_den) for am in a]
    Q_int = [0] * (t + 1)
    for m in range(1, t):
        Q_int[m] = Q_int[m - 1] - a_int[m - 1]
    assert Q_int[t - 1] - a_int[t - 1] == 0

    # Build intermediate states using unscaled rational Q (fast RREF!), then clear to exact integer Q_int!
    Q_rat = [Fraction(0)] * (t + 1)
    for m in range(1, t):
        Q_rat[m] = Q_rat[m - 1] - a[m - 1]

    X = {(1, 0, 0): Fraction(1)}
    U = {(0, 1, 0): Fraction(1)}
    V = {(0, 0, 1): Fraction(1)}

    states = []
    u_cur, v_cur = dict(U), dict(V)
    for k in range(t):
        states.append((dict(u_cur), dict(v_cur)))
        q_next = Q_rat[k + 1] if k + 1 < t else Fraction(0)
        if q_next != 0:
            v_cur = poly_add(v_cur, poly_pow(u_cur, deg_w), -q_next)
        alpha = shifts[(k + 1) % t] - shifts[k]
        u_cur = poly_add(u_cur, X, Fraction(alpha))
        if q_next != 0:
            v_cur = poly_add(v_cur, poly_pow(u_cur, deg_w), q_next)
    assert u_cur == U and v_cur == V

    # Solve exact rational system for F_k(u, v)
    terms, meta = [], []
    for k, (uk, vk) in enumerate(states):
        for jv in range(target_N // deg_w + 1):
            ju = target_N - deg_w * jv
            terms.append(poly_mul(poly_pow(uk, ju), poly_pow(vk, jv)))
            meta.append((k, ju, jv))

    mons = sorted({m for p in terms for m in p.keys()} | {(target_N, 0, 0)})
    rows = [[p.get(m, Fraction(0)) for p in terms] for m in mons]
    rhs = [Fraction(1) if m == (target_N, 0, 0) else Fraction(0) for m in mons]
    sol = solve_linear_Q(rows, rhs)
    assert sol is not None, f"No solution for t={t}, N={target_N}"

    # Convert to pure integer loop Q_int = a_den * Q_rat (substituting v_int = a_den * v)
    adj = [c / (a_den ** jv) for c, (_, _, jv) in zip(sol, meta)]
    out_scale = 1
    for c in adj:
        if c != 0:
            out_scale = lcm(out_scale, c.denominator)
    c_int = [int(c * out_scale) for c in adj]
    g = 0
    for v in c_int:
        g = math.gcd(g, abs(v))
    c_int = [v // g for v in c_int]
    out_scale //= g

    # Literal instruction-by-instruction symbolic replay over Z[x, u, v]
    by_state: dict[int, list[tuple[int, int, int]]] = {k: [] for k in range(t)}
    for (k, ju, jv), ci in zip(meta, c_int):
        if ci != 0:
            by_state[k].append((ju, jv, ci))

    O_reg: dict = {}
    u_reg, v_reg = dict(U), dict(V)
    accesses = 0
    basic_ops = 0
    for k in range(t):
        if by_state[k]:
            for ju, jv, ci in by_state[k]:
                O_reg = poly_add(O_reg, poly_mul(poly_pow(u_reg, ju), poly_pow(v_reg, jv)), Fraction(ci))
            basic_ops += 1
        q_next_i = Q_int[k + 1] if k + 1 < t else 0
        if q_next_i != 0:
            v_reg = poly_add(v_reg, poly_pow(u_reg, deg_w), Fraction(-q_next_i))
            basic_ops += 1
        alpha = shifts[(k + 1) % t] - shifts[k]
        u_reg = poly_add(u_reg, X, Fraction(alpha))
        accesses += 1
        if q_next_i != 0:
            v_reg = poly_add(v_reg, poly_pow(u_reg, deg_w), Fraction(q_next_i))
            basic_ops += 1

    assert u_reg == U, "Work register u not restored!"
    assert v_reg == V, "Work register v not restored!"
    assert O_reg == {(target_N, 0, 0): Fraction(out_scale)}, "Output register mismatch!"
    assert accesses == t

    bad_primes = factor_primes(out_scale)
    eps = math.log(t) / math.log(target_N)

    # Also spot-check literal modular evaluation over good small primes p not in bad_primes
    good_primes_tested = []
    for p in [5, 7, 11, 13, 19, 23]:
        if p in bad_primes:
            continue
        inv_D = pow(out_scale % p, p - 2, p)
        # Test across multiple (x, o, u, v) in F_p^4
        for x0, o0, u0, v0 in [(2 % p, 3 % p, 4 % p, 1 % p), (p - 1, 2 % p, 3 % p, p - 2)]:
            o_val, u_val, v_val = o0, u0, v0
            for k in range(t):
                for ju, jv, ci in by_state[k]:
                    o_val = (o_val + inv_D * ci * pow(u_val, ju, p) * pow(v_val, jv, p)) % p
                q_next_m = Q_int[k + 1] if k + 1 < t else 0
                if q_next_m != 0:
                    v_val = (v_val - q_next_m * pow(u_val, deg_w, p)) % p
                alpha = shifts[(k + 1) % t] - shifts[k]
                u_val = (u_val + alpha * x0) % p
                if q_next_m != 0:
                    v_val = (v_val + q_next_m * pow(u_val, deg_w, p)) % p
            assert o_val == (o0 + pow(x0, target_N, p)) % p
            assert u_val == u0 and v_val == v0
        good_primes_tested.append(p)

    print(
        f"[VERIFIED] r=3, t={t} -> x^{target_N:2d} (deg_w={deg_w}): "
        f"eps={eps:.6f}, basic_ops={basic_ops}, nz_terms={sum(len(v) for v in by_state.values())}, "
        f"bad_primes={bad_primes}, F_p_spot={good_primes_tested}"
    )
    return {
        "r": 3,
        "t": t,
        "degree": target_N,
        "deg_w": deg_w,
        "shifts": shifts,
        "Q_int": Q_int,
        "out_scale": str(out_scale),
        "bad_primes": bad_primes,
        "basic_ops": basic_ops,
        "nonzero_output_terms": sum(len(v) for v in by_state.values()),
        "exponent": round(eps, 8),
        "good_primes_verified": good_primes_tested,
    }


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parent.parent
    out_path = repo / "results" / "exp2_three_register.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)

    configs = [
        (4, [0, 1, 2, 3], 2, 5),
        (5, [0, 1, 2, 3, 4], 2, 7),
        (6, [0, 1, 2, 3, 4, 5], 4, 9),
        (7, [0, 1, 2, 3, 4, 5, 7], 5, 11),
        (8, [0, 1, 2, 3, 4, 5, 6, 7], 6, 13),
        (9, [0, 1, 2, 3, 4, 5, 6, 7, 9], 7, 15),
    ]
    programs = [synthesize_and_verify_r3(*cfg) for cfg in configs]

    # Exact integer rational-separator certification (matching Lean T3e)
    chain_checks = {
        "log13_8_lt_30_37": 8**37 < 13**30,
        "30_37_lt_log11_7": 11**30 < 7**37,
        "log11_7_lt_13_16": 7**16 < 11**13,
        "13_16_lt_log9_6": 9**13 < 6**16,
        "log9_6_lt_9_11": 6**11 < 9**9,
        "9_11_lt_log7_5": 7**9 < 5**11,
        "log7_5_lt_5_6": 5**6 < 7**5,
        "5_6_lt_log5_4": 5**5 < 4**6,
        "30_37_lt_log15_9": 15**30 < 9**37,
    }
    assert all(chain_checks.values())
    print("[VERIFIED] All 9 exact integer exponent-chain separation inequalities hold.")

    data = {
        "theorem": "T3 (3-Register Passive Catalytic Powering Breakthrough)",
        "vinciguerra_baseline_exponent": round(math.log(4) / math.log(5), 8),
        "new_optimal_exponent": round(math.log(8) / math.log(13), 8),
        "exponent_reduction": round(math.log(4) / math.log(5) - math.log(8) / math.log(13), 8),
        "programs": programs,
        "exponent_chain_exact_nat_checks": chain_checks,
    }
    out_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
