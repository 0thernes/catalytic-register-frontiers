# SPDX-License-Identifier: Apache-2.0
"""
Experiment 3: Independent Exact Verification of Theorems T2 & T4.
  - Theorem T2: Strictly bilinear passive-output 2-access Frobenius collapse in F_2[x, c_0..c_k]
    for k = 1..6 (x^2, x^4, x^8, x^16, x^32, x^64), verifying exactly 2 input accesses and 4k-2
    bilinear ops with bit-for-bit catalyst restoration.
  - Theorem T4: Balanced zero-workspace bilinear catalytic multilinear product for d = 2^k
    (k = 1..5, i.e., d = 2, 4, 8, 16, 32) using k + 2 registers and exact (7 d^2 - 4)/3 ops
    (compared against linear-chain 3 * 4^{d-1} - 2).
"""

from __future__ import annotations

import json
import pathlib
import random


def verify_t2_bilinear_frobenius() -> list[dict]:
    records = []
    for k in range(1, 7):
        deg = 1 << k
        nvars = k + 2  # var 0 = x, var 1+i = c_i

        def f2_add(a: set, b: set) -> set:
            return a ^ b

        def f2_mul(a: set, b: set) -> set:
            out: set = set()
            for ma in a:
                for mb in b:
                    m = tuple(u + v for u, v in zip(ma, mb))
                    if m in out:
                        out.remove(m)
                    else:
                        out.add(m)
            return out

        def basis(idx: int) -> set:
            t = [0] * nvars
            t[idx] = 1
            return {tuple(t)}

        X = basis(0)
        R = [basis(1 + i) for i in range(k + 1)]
        init_R = [set(r) for r in R]

        accesses = 0
        bilin_ops = 0

        # Access 1
        R[1] = f2_add(R[1], X)
        accesses += 1
        for j in range(1, k):
            R[j + 1] = f2_add(R[j + 1], f2_mul(R[j], R[j]))
            bilin_ops += 1
        R[0] = f2_add(R[0], f2_mul(R[k], R[k]))
        bilin_ops += 1
        for j in range(k - 1, 0, -1):
            R[j + 1] = f2_add(R[j + 1], f2_mul(R[j], R[j]))
            bilin_ops += 1
        # Access 2
        R[1] = f2_add(R[1], X)
        accesses += 1
        for j in range(1, k):
            R[j + 1] = f2_add(R[j + 1], f2_mul(R[j], R[j]))
            bilin_ops += 1
        R[0] = f2_add(R[0], f2_mul(R[k], R[k]))
        bilin_ops += 1
        for j in range(k - 1, 0, -1):
            R[j + 1] = f2_add(R[j + 1], f2_mul(R[j], R[j]))
            bilin_ops += 1

        x_mon = tuple(deg if i == 0 else 0 for i in range(nvars))
        assert R[0] == (init_R[0] ^ {x_mon}), f"T2 output mismatch at k={k}"
        for j in range(1, k + 1):
            assert R[j] == init_R[j], f"T2 catalyst R_{j} corrupted at k={k}"
        assert accesses == 2
        assert bilin_ops == 4 * k - 2

        records.append({
            "k": k,
            "degree": deg,
            "registers": k + 1,
            "input_accesses": accesses,
            "bilinear_ops": bilin_ops,
            "symbolic_f2_poly_verified": True,
        })
        print(
            f"[VERIFIED T2] k={k}: x^{deg:2d} in F_2[x,c] using {k+1} regs, "
            f"ONLY {accesses} input accesses, {bilin_ops} bilinear ops."
        )
    return records


def exec_balanced(xs: list[int], regs: list[int], target: int, sign: int, pool: list[int]) -> int:
    if len(xs) == 1:
        regs[target] += sign * xs[0]
        return 1
    mid = len(xs) // 2
    ra, rb, rest = pool[0], pool[1], pool[2:]
    assert target != ra and target != rb and ra != rb
    ops = 0
    regs[target] += sign * (regs[ra] * regs[rb])
    ops += 1
    ops += exec_balanced(xs[:mid], regs, ra, +1, [rb] + rest)
    regs[target] -= sign * (regs[ra] * regs[rb])
    ops += 1
    ops += exec_balanced(xs[mid:], regs, rb, +1, [ra] + rest)
    regs[target] += sign * (regs[ra] * regs[rb])
    ops += 1
    ops += exec_balanced(xs[:mid], regs, ra, -1, [rb] + rest)
    regs[target] -= sign * (regs[ra] * regs[rb])
    ops += 1
    ops += exec_balanced(xs[mid:], regs, rb, -1, [ra] + rest)
    return ops


def verify_t4_balanced_product() -> list[dict]:
    rng = random.Random(20261123)
    records = []
    for k in range(1, 6):
        d = 1 << k
        num_regs = k + 2
        expected_ops = (7 * d * d - 4) // 3
        linear_chain_ops = 3 * (4 ** (d - 1)) - 2
        trials = 25 if k <= 4 else 10
        ops = 0
        for _ in range(trials):
            xs = [rng.randint(-4, 4) for _ in range(d)]
            init = [rng.randint(-9, 9) for _ in range(num_regs)]
            regs = list(init)
            ops = exec_balanced(xs, regs, 0, +1, list(range(1, num_regs)))
            prod = 1
            for v in xs:
                prod *= v
            assert regs[0] == init[0] + prod
            assert regs[1:] == init[1:]
            assert ops == expected_ops
        records.append({
            "k": k,
            "d": d,
            "balanced_registers": num_regs,
            "linear_chain_registers": d,
            "balanced_ops": ops,
            "linear_chain_ops_str": str(linear_chain_ops),
            "trials_verified": trials,
        })
        print(
            f"[VERIFIED T4] k={k}, d={d:2d}: regs={num_regs} (vs {d}), "
            f"ops={ops:4d} (exact (7d^2-4)/3={expected_ops}, vs linear chain {linear_chain_ops})."
        )
    return records


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parent.parent
    out_path = repo / "results" / "exp3_bilinear_balanced.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    data = {
        "T2_bilinear_frobenius": verify_t2_bilinear_frobenius(),
        "T4_balanced_multilinear_product": verify_t4_balanced_product(),
    }
    out_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
