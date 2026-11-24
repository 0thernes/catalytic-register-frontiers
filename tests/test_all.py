# SPDX-License-Identifier: Apache-2.0
"""
End-to-end exact verification test suite for catalytic-register-frontiers.
Run repo-relative (`pytest -v tests/test_all.py`) for Windows bracket-path safety.
"""

from __future__ import annotations

import json
import math
import pathlib
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

from experiments.exp1_digit_sum_dichotomy import (
    binom_mod_p,
    digit_sum,
    rref_solvable_fp,
    verify_extension_field_f4,
    verify_prime_fields,
)
from experiments.exp2_three_register_breakthrough import synthesize_and_verify_r3
from experiments.exp3_bilinear_and_balanced import (
    exec_balanced,
    verify_t2_bilinear_frobenius,
    verify_t4_balanced_product,
)
from experiments.exp4_boolean_mc_companion import run_companion_audit


def test_t1_prime_field_dichotomy_exact() -> None:
    res = verify_prime_fields()
    assert set(res.keys()) == {"F_2", "F_3", "F_5", "F_7"}
    # Over F_2, only powers of 2 in 2..120 (2, 4, 8, 16, 32, 64 -> 6 degrees) are feasible!
    assert res["F_2"]["feasible_degrees_verified"] == 6
    assert res["F_2"]["impossible_degrees_verified"] == 113
    # Spot-check Lucas + digit-sum identity directly
    assert digit_sum(3, 27) == 1
    assert digit_sum(5, 29) == 5  # 29 = 1*25 + 0*5 + 4 = (104)_5
    assert digit_sum(5, 24) == 8  # 24 = 4*5 + 4 = (44)_5
    assert binom_mod_p(5, 2, 5) == 0
    assert binom_mod_p(7, 3, 2) == 1
    # Check x^3 impossible over F_2 using full field {0, 1}
    active = [0, 1, 2, 3]
    cols = [[1 if j == 0 else pow(a, j, 2) for j in active] for a in [0, 1]]
    rhs = [0, 0, 0, 1]
    assert not rref_solvable_fp(cols, rhs, 2)


def test_t1_extension_field_f4_spectrum() -> None:
    recs = verify_extension_field_f4()
    by_d = {r["d"]: r["min_t_F4"] for r in recs}
    assert by_d[1] == 2 and by_d[2] == 2 and by_d[4] == 2 and by_d[8] == 2 and by_d[16] == 2
    assert by_d[5] == 3 and by_d[10] == 3
    assert by_d[3] == 4 and by_d[6] == 4 and by_d[9] == 4 and by_d[12] == 4
    assert by_d[7] is None and by_d[11] is None and by_d[13] is None and by_d[14] is None and by_d[15] is None


def test_t2_bilinear_frobenius_exact() -> None:
    recs = verify_t2_bilinear_frobenius()
    assert len(recs) == 6
    for rec in recs:
        k = rec["k"]
        assert rec["degree"] == 1 << k
        assert rec["registers"] == k + 1
        assert rec["input_accesses"] == 2
        assert rec["bilinear_ops"] == 4 * k - 2
        assert rec["symbolic_f2_poly_verified"] is True


def test_t3_three_register_breakthrough_exact() -> None:
    p4 = synthesize_and_verify_r3(4, [0, 1, 2, 3], 2, 5)
    p5 = synthesize_and_verify_r3(5, [0, 1, 2, 3, 4], 2, 7)
    p6 = synthesize_and_verify_r3(6, [0, 1, 2, 3, 4, 5], 4, 9)
    p7 = synthesize_and_verify_r3(7, [0, 1, 2, 3, 4, 5, 7], 5, 11)
    p8 = synthesize_and_verify_r3(8, [0, 1, 2, 3, 4, 5, 6, 7], 6, 13)
    p9 = synthesize_and_verify_r3(9, [0, 1, 2, 3, 4, 5, 6, 7, 9], 7, 15)

    assert p5["out_scale"] == "576" and p5["bad_primes"] == [2, 3]
    assert p6["out_scale"] == "382500000" and p6["bad_primes"] == [2, 3, 5, 17]
    assert p7["out_scale"] == "68724637549388656012800"
    assert p8["out_scale"] == "2656207148788801777680"

    # Strict monotonic drop from Vinciguerra t=4 to global integer optimum t=8, then uptick at t=9
    assert p8["exponent"] < p7["exponent"] < p6["exponent"] < p5["exponent"] < p4["exponent"]
    assert p8["exponent"] < p9["exponent"]
    assert abs(p8["exponent"] - math.log(8) / math.log(13)) < 1e-7

    # Exact integer rational-separator inequalities (matching Lean T3e)
    assert 8**37 < 13**30 and 11**30 < 7**37
    assert 7**16 < 11**13 and 9**13 < 6**16
    assert 6**11 < 9**9 and 7**9 < 5**11
    assert 5**6 < 7**5 and 5**5 < 4**6
    assert 15**30 < 9**37


def test_t4_balanced_multilinear_product_exact() -> None:
    recs = verify_t4_balanced_product()
    assert len(recs) == 5
    for rec in recs:
        d = rec["d"]
        assert rec["balanced_ops"] == (7 * d * d - 4) // 3
        assert 3 * rec["balanced_ops"] + 4 == 7 * d * d
        assert rec["balanced_registers"] == rec["k"] + 2
    # Adversarial negative / zero inputs test
    regs = [17, -11, 23, -5, 31]
    init = list(regs)
    xs = [3, -2, 0, 5, -7, 4, -1, 2]
    ops = exec_balanced(xs, regs, 0, +1, [1, 2, 3, 4])
    assert ops == 148
    assert regs == init  # product is 0 so target unchanged and all catalysts restored!


def test_exp4_boolean_mc_companion_sat() -> None:
    res = run_companion_audit()
    assert res["boyar_find_counterexamples_found"] == 0
    assert res["hard_n4_m3_quadratic_maps_k2_unsat"] == 6
    assert res["genuine_deg3_cancellations_sampled"] > 0
    by_name = {b["name"]: b for b in res["benchmarks"]}
    assert by_name["F_4_multiplication"]["exact_mc"] == 3
    assert by_name["orthogonal_bent_pair_n4"]["exact_mc"] == 3


def test_lean_formalization_has_zero_forbidden_tokens() -> None:
    lean_dir = REPO / "lean"
    forbidden = ["sorry", "admit", "native_decide", "implemented_by", "unsafe", "@[extern"]
    lean_files = list(lean_dir.rglob("*.lean"))
    assert len(lean_files) >= 8
    for f in lean_files:
        text = f.read_text(encoding="utf-8")
        assert text.lstrip().startswith("module"), f"Missing Lean 4.35 `module` header in {f}"
        for tok in forbidden:
            assert tok not in text, f"Forbidden token `{tok}` found in {f}"


def test_results_json_artifacts_valid() -> None:
    for fname in [
        "exp1_digit_sum.json",
        "exp2_three_register.json",
        "exp3_bilinear_balanced.json",
        "exp4_boolean_mc.json",
    ]:
        p = REPO / "results" / fname
        if p.exists():
            parsed = json.loads(p.read_text(encoding="utf-8"))
            assert isinstance(parsed, dict)
