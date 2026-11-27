# SPDX-License-Identifier: Apache-2.0
"""
End-to-end exact verification, Hypothesis property-based, certificate mutant-killing,
and brute-force SAT encoder equivalence test suite for catalytic-register-frontiers.
Run repo-relative (`pytest -v tests/test_all.py`) for Windows bracket-path safety.
"""

from __future__ import annotations

import json
import math
import os
import pathlib
import re
import sys

from hypothesis import given, settings
from hypothesis import strategies as st

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
from experiments.exp4_boolean_mc_companion import (
    eval_anf,
    find_cadical,
    run_companion_audit,
    synthesize_multi_output_mc,
)
from scripts.check_citations import BIB_PATH, check_offline
from scripts.check_reuse import verify_reuse
from scripts.verify_lrat import verify_lrat


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


@settings(max_examples=75, deadline=None)
@given(
    p=st.sampled_from([2, 3, 5, 7, 11]),
    d=st.integers(min_value=0, max_value=250),
    k=st.integers(min_value=0, max_value=250),
)
def test_hypothesis_t1_lucas_and_digit_sum(p: int, d: int, k: int) -> None:
    """Property-based & differential oracle test (Build Standard B10, B12)."""
    assert binom_mod_p(d, k, p) == math.comb(d, k) % p
    if d >= 1:
        assert 1 <= digit_sum(p, d) <= d
    assert digit_sum(p, p ** (k % 5)) == 1


@settings(max_examples=60, deadline=None)
@given(
    xs=st.lists(st.integers(min_value=-20, max_value=20), min_size=4, max_size=4),
    init_regs=st.lists(st.integers(min_value=-50, max_value=50), min_size=4, max_size=4),
    delta=st.lists(st.integers(min_value=-30, max_value=30), min_size=4, max_size=4),
    sign=st.sampled_from([-1, 1]),
)
def test_hypothesis_t4_metamorphic_catalytic_invariance(
    xs: list[int], init_regs: list[int], delta: list[int], sign: int
) -> None:
    """Property-based + metamorphic shift-invariance check for T4 (Build Standard B10, B14)."""
    regs1 = list(init_regs)
    regs2 = [r + d for r, d in zip(init_regs, delta)]
    ops1 = exec_balanced(xs, regs1, 0, sign, [1, 2, 3])
    ops2 = exec_balanced(xs, regs2, 0, sign, [1, 2, 3])
    expected_prod = sign * math.prod(xs)
    assert ops1 == 36 and ops2 == 36
    assert regs1[0] - init_regs[0] == expected_prod
    assert regs2[0] - (init_regs[0] + delta[0]) == expected_prod
    # Exact catalytic restoration on all non-target registers
    assert regs1[1:] == init_regs[1:]
    assert regs2[1:] == [r + d for r, d in zip(init_regs[1:], delta[1:])]


def test_mutant_killing_certificates() -> None:
    """Mutation testing on mathematical certificates (Build Standard B13):
    every injected mutant across T1, T3, and T4 must be detected and rejected."""
    mutants_killed = 0

    # Mutant 1 (T1): Attempting to solve x^d with s_p(d) >= p over full F_p must fail.
    for p, bad_d in [(2, 3), (3, 5), (5, 29)]:  # s_2(3)=2, s_3(5)=3, s_5(29)=5
        active = [j for j in range(bad_d + 1) if binom_mod_p(bad_d, j, p) != 0]
        cols = [[1 if j == 0 else pow(a, j, p) for j in active] for a in range(p)]
        rhs = [0] * (len(active) - 1) + [1]
        assert not rref_solvable_fp(cols, rhs, p)
        mutants_killed += 1

    # Mutant 2 (T3): Perturbing a shift vector of prog5_x7 breaks degree-7 solvability.
    mutated_t3_failed = False
    try:
        synthesize_and_verify_r3(5, [0, 1, 2, 3, 3], 2, 7)
    except (AssertionError, ValueError, ZeroDivisionError):
        mutated_t3_failed = True
    assert mutated_t3_failed
    mutants_killed += 1

    # Mutant 3 (T4): Flipping the sign of the product must fail equality against +prod(xs).
    regs = [10, 20, 30, 40]
    xs = [2, 3, 5, 7]
    exec_balanced(xs, regs, 0, -1, [1, 2, 3])
    assert regs[0] != 10 + math.prod(xs)
    assert regs[0] == 10 - math.prod(xs)
    mutants_killed += 1

    assert mutants_killed == 5


def _bruteforce_mc_reachable_n2() -> dict[int, set[tuple[int, ...]]]:
    """Independent brute-force oracle for exact MC_AND on all 16 Boolean functions of n=2."""
    n = 2
    N = 1 << n
    # Affine span: {0, 1, x0, x1, 1^x0, 1^x1, x0^x1, 1^x0^x1}
    inputs = [tuple((x >> i) & 1 for x in range(N)) for i in range(n)]
    const1 = (1,) * N

    def lin_span(basis: list[tuple[int, ...]]) -> set[tuple[int, ...]]:
        res = {(0,) * N}
        for b in basis:
            res = res | {tuple(a ^ c for a, c in zip(v, b)) for v in res}
        return res

    s0 = lin_span([const1] + inputs)
    s1: set[tuple[int, ...]] = set(s0)
    for u in s0:
        for v in s0:
            g = tuple(a & b for a, b in zip(u, v))
            s1 |= lin_span([const1] + inputs + [g])
    return {0: s0, 1: s1}


def test_sat_encoder_bruteforce_equivalence() -> None:
    """Playbook #14 & Build Standard B12: verify exp4's CNF encoder agrees 100% with
    an independent brute-force ground-truth enumerator on all 16 functions for n=2 (k=0, 1)
    and canonical n=3 benchmarks (k=1, 2)."""
    cadical = find_cadical()
    oracle = _bruteforce_mc_reachable_n2()
    # Exhaustive check across all 16 Boolean functions on n=2 for k=0 and k=1
    for tt_int in range(16):
        tt = tuple((tt_int >> x) & 1 for x in range(4))
        for k in (0, 1):
            expected = "SAT" if tt in oracle[k] else "UNSAT"
            got = synthesize_multi_output_mc([list(tt)], 2, k, cadical, timeout=5.0)
            assert got == expected, f"CNF encoder mismatch on n=2 tt={tt}, k={k}: {got} != {expected}"

    # Canonical n=3 checks: x0*x1*x2 has exact MC_AND = 2 (UNSAT at k=1, SAT at k=2)
    cube3 = eval_anf([0b111], 3)
    assert synthesize_multi_output_mc([cube3], 3, 1, cadical, timeout=5.0) == "UNSAT"
    assert synthesize_multi_output_mc([cube3], 3, 2, cadical, timeout=5.0) == "SAT"
    # Majority-3 = x0*x1 ^ x0*x2 ^ x1*x2 = (x0^x2)*(x1^x2) ^ x2 has exact MC_AND = 1
    maj3 = eval_anf([0b011, 0b101, 0b110], 3)
    assert synthesize_multi_output_mc([maj3], 3, 0, cadical, timeout=5.0) == "UNSAT"
    assert synthesize_multi_output_mc([maj3], 3, 1, cadical, timeout=5.0) == "SAT"


def test_lean_formalization_and_governance_hygiene() -> None:
    """Negative & regression guard (B06, B07): zero forbidden tokens in all 15 proof/solution
    modules, standalone PalomarChallenge.lean unimported & <= 1000 lines, all Lean files use
    `module`, axioms strictly within the 3 standard Lean axioms, and citations verified."""
    lean_dir = REPO / "lean"
    pat = re.compile(r"\b(sorry|admit|native_decide|implemented_by|unsafe)\b|^\s*axiom\b|@\[extern", re.M)
    pat_no_sorry = re.compile(r"\b(admit|native_decide|implemented_by|unsafe)\b|^\s*axiom\b|@\[extern", re.M)
    lean_files: list[pathlib.Path] = []
    for root, dirs, fnames in os.walk(lean_dir):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for fn in sorted(fnames):
            if fn.endswith(".lean"):
                lean_files.append(pathlib.Path(root) / fn)
    assert len(lean_files) == 16
    for f in lean_files:
        text = f.read_text(encoding="utf-8")
        assert text.lstrip().startswith("module"), f"Missing Lean 4.35 `module` header in {f}"
        if f.name == "PalomarChallenge.lean":
            assert not pat_no_sorry.search(text), f"Forbidden token found in {f}"
            assert not re.search(r"^\s*(?:public\s+)?import\b", text, re.M), "PalomarChallenge.lean must have zero imports"
            assert len(text.splitlines()) <= 300, "PalomarChallenge.lean exceeds Palomar 300-line preferred cap"
        else:
            assert not pat.search(text), f"Forbidden token found in {f}"
            assert "PalomarChallenge" not in text, f"Proof module {f} must never reference PalomarChallenge"

    # Verify PalomarChallenge.lean and PalomarSolution.lean definition sections match verbatim
    pc_txt = (lean_dir / "PalomarChallenge.lean").read_text(encoding="utf-8")
    ps_txt = (lean_dir / "PalomarSolution.lean").read_text(encoding="utf-8")
    pc_defs = pc_txt.split("namespace Catalytic.Palomar\n", 1)[1].split("/-! ## 7.", 1)[0].strip()
    ps_defs = ps_txt.split("namespace Catalytic.Palomar\n", 1)[1].split("\nend\n\n/-! ## Private Equivalence Bridges", 1)[0].strip()
    assert pc_defs == ps_defs, "PalomarChallenge.lean and PalomarSolution.lean definition sections drifted!"

    # Verify Palomar, comparator, soundness bridge, extension-field, and 4-register powering artifacts exist
    assert (lean_dir / "comparator.json").exists()
    assert (lean_dir / "palomar_comparator.json").exists()
    assert (lean_dir / "formalization.yaml").exists()
    assert (lean_dir / "Catalytic" / "NonVacuity.lean").exists()
    assert (lean_dir / "Catalytic" / "ExtensionFieldSeparation.lean").exists()
    assert (lean_dir / "Catalytic" / "Pass2Soundness.lean").exists()
    assert (lean_dir / "Catalytic" / "FourRegisterPowering.lean").exists()

    # Verify results/lean_axioms.txt covers all 22 declarations with zero unpermitted axioms
    ax_lines = (REPO / "results" / "lean_axioms.txt").read_text(encoding="utf-8").strip().splitlines()
    assert len(ax_lines) == 22
    for line in ax_lines:
        assert "sorryAx" not in line and "ofReduceBool" not in line and "trustCompiler" not in line

    # Regression test for ERRATA.md: ensure wrong BoyarFind2018 DOI never re-enters references.bib
    bib_text = BIB_PATH.read_text(encoding="utf-8")
    assert "10.1016/j.tcs.2018.04.017" not in bib_text
    assert "10.1016/j.tcs.2018.02.023" in bib_text
    assert "10.4230/LIPIcs.MFCS.2025.6" in bib_text
    entries, errs = check_offline(BIB_PATH)
    assert len(entries) == 10 and errs == []


def test_results_json_artifacts_valid() -> None:
    for fname in [
        "exp1_digit_sum.json",
        "exp2_three_register.json",
        "exp3_bilinear_balanced.json",
        "exp4_boolean_mc.json",
    ]:
        p = REPO / "results" / fname
        assert p.exists(), f"Missing artifact: {p}"
        parsed = json.loads(p.read_text(encoding="utf-8"))
        assert isinstance(parsed, dict)


def test_lrat_certificates_and_mutant_rejection(tmp_path: pathlib.Path) -> None:
    """Verify all 8/8 archived CaDiCaL 2.1.2 LRAT UNSAT certificates and confirm mutant rejection."""
    cert_dir = REPO / "results" / "sat_certs"
    expected_stems = [
        "f4_mul_k2",
        "orthogonal_bent_pair_k2",
        *(f"hard_n4_m3_trial{i}_k2" for i in range(6)),
    ]
    total_steps = 0
    for stem in expected_stems:
        cnf_p = cert_dir / f"{stem}.cnf"
        lrat_p = cert_dir / f"{stem}.lrat"
        assert cnf_p.exists() and lrat_p.exists(), f"Missing SAT certificate pair for {stem}"
        steps, deletions = verify_lrat(cnf_p, lrat_p)
        assert steps > 1000 and deletions > 100
        total_steps += steps
    assert total_steps > 15000

    # Mutant 1: truncate the final empty-clause derivation line -> must raise ValueError
    orig_cnf = cert_dir / "f4_mul_k2.cnf"
    orig_lines = (cert_dir / "f4_mul_k2.lrat").read_text(encoding="ascii").splitlines()
    trunc_lrat = tmp_path / "truncated.lrat"
    trunc_lrat.write_text("\n".join(orig_lines[:-1]) + "\n", encoding="ascii", newline="\n")
    raised = False
    try:
        verify_lrat(orig_cnf, trunc_lrat)
    except ValueError:
        raised = True
    assert raised, "LRAT verifier failed to reject proof missing empty clause!"

    # Mutant 2: corrupt the first derived clause hint ID -> must raise ValueError
    corrupted = list(orig_lines)
    for idx, line in enumerate(corrupted):
        parts = line.split()
        if len(parts) >= 4 and parts[1] != "d":
            zero_idx = parts.index("0", 1)
            if zero_idx + 1 < len(parts) - 1:
                parts[zero_idx + 1] = "99999999"
                corrupted[idx] = " ".join(parts)
                break
    bad_hint_lrat = tmp_path / "bad_hint.lrat"
    bad_hint_lrat.write_text("\n".join(corrupted) + "\n", encoding="ascii", newline="\n")
    raised = False
    try:
        verify_lrat(orig_cnf, bad_hint_lrat)
    except ValueError:
        raised = True
    assert raised, "LRAT verifier failed to reject corrupted RUP hint!"

    # Mutant 3: non-monotonic / reused clause ID -> must raise ValueError
    non_mono = list(orig_lines)
    for idx, line in enumerate(non_mono):
        parts = line.split()
        if len(parts) >= 4 and parts[1] != "d":
            parts[0] = "1"
            non_mono[idx] = " ".join(parts)
            break
    non_mono_lrat = tmp_path / "non_mono.lrat"
    non_mono_lrat.write_text("\n".join(non_mono) + "\n", encoding="ascii", newline="\n")
    raised = False
    try:
        verify_lrat(orig_cnf, non_mono_lrat)
    except ValueError:
        raised = True
    assert raised, "LRAT verifier failed to reject non-monotonic clause ID!"


def test_t3f_global_integer_optimality_exact() -> None:
    """Independent exact integer verification of T3f rational separator 30/37 for t=4..500."""
    assert 8**37 < 13**30
    for t in range(4, 501):
        if t == 8:
            assert (2 * t - 3) ** 30 > t**37
        else:
            assert (2 * t - 3) ** 30 < t**37


def test_t3h_four_reg_powering_exact() -> None:
    """Independent exact verification of T3h (Corollary 5.2) 4-register passive powering
    recurrence, exact base-delta finite-difference accumulation, and modular witnesses."""
    from fractions import Fraction

    def base_digits(delta: int, n: int) -> list[int]:
        ds: list[int] = []
        while n >= delta:
            ds.append(n % delta)
            n //= delta
        ds.append(n)
        return ds

    def exact_accesses(delta: int, t: int, n: int) -> int:
        # Mirrors FourRegisterPowering.fourRegPowerProg exactly:
        # C_i uses (0 if b_i == 0 else b_i + 1) * t^i accesses, accumulated MSB-first via T(L) = 2*C + 2*T(rest)
        ds = base_digits(delta, n)
        cs = [(0 if b == 0 else b + 1) * (t**i) for i, b in enumerate(ds)]
        acc = 0
        for c_i in cs:  # LSB-first corresponds to folding MSB-first list from the right
            acc = 2 * c_i + 2 * acc
        return acc

    for n in (1, 2, 7, 13, 20, 35, 168, 169, 1000, 12345):
        ds13 = base_digits(13, n)
        ell13 = len(ds13) - 1
        assert 13**ell13 <= n < 13 ** (ell13 + 1)
        acc13 = exact_accesses(13, 8, n)
        assert 3 * acc13 < 104 * (8**ell13), f"T3h prog8_x13 bound violated at N={n}"

        ds7 = base_digits(7, n)
        ell7 = len(ds7) - 1
        assert 7**ell7 <= n < 7 ** (ell7 + 1)
        acc7 = exact_accesses(7, 5, n)
        assert 3 * acc7 < 70 * (5**ell7), f"T3h prog5_x7 bound violated at N={n}"

    # Verify multivariate Cook-Mertz finite difference recovers exact x^N over Q on random catalytic u
    for delta, n in ((13, 20), (13, 175), (7, 20), (7, 58)):
        ds = base_digits(delta, n)
        ys = [Fraction(3) ** (b * (delta**i)) for i, b in enumerate(ds)]
        u0 = Fraction(5, 7)
        m = len(ys)

        def mdiff(vals: list[Fraction], u: Fraction) -> Fraction:
            if not vals:
                return u**m
            return mdiff(vals[1:], u + vals[0]) - mdiff(vals[1:], u)

        got = mdiff(ys, u0) / math.factorial(m)
        assert got == Fraction(3) ** n

    # Verify concrete NonVacuity modular witnesses for T3h over F_13 and F_7 at N = 20
    D8 = 2656207148788801777680
    assert (10 * D8) % 13 == 1 and (12 * math.factorial(12)) % 13 == 1 and (7 * 2) % 13 == 1
    assert (6 * math.factorial(6)) % 7 == 1 and (4 * 2) % 7 == 1
    assert 720 * 720 == 576 * 900

    # Verify T3i pointwise product-ring streaming frequency moment F_D(f) = sum_i f_i^D
    for vec, moment in (([2, 0, 5, 3], 13), ([1, 4, 2, 1, 3], 20)):
        ds_m = base_digits(13, moment)
        m_len = len(ds_m)
        u_vec = [Fraction(i + 2, 7) for i in range(len(vec))]
        o_vec = [Fraction(3 * i - 1, 5) for i in range(len(vec))]
        coord_out: list[Fraction] = []
        for idx, f_i in enumerate(vec):
            ys_i = [Fraction(f_i) ** (b * (13**j)) for j, b in enumerate(ds_m)]

            def mdiff_vec(vals: list[Fraction], u_val: Fraction, deg: int) -> Fraction:
                if not vals:
                    return u_val**deg
                return mdiff_vec(vals[1:], u_val + vals[0], deg) - mdiff_vec(vals[1:], u_val, deg)

            coord_out.append(o_vec[idx] + mdiff_vec(ys_i, u_vec[idx], m_len) / math.factorial(m_len))
        assert sum(coord_out) == sum(o_vec) + sum(Fraction(f_i) ** moment for f_i in vec)
        assert 3 * exact_accesses(13, 8, moment) < 104 * (8 ** (m_len - 1))


def test_manifest_and_reuse_hygiene() -> None:
    """Guard against cache files leaking into MANIFEST.sha256 and confirm 100% REUSE/SPDX."""
    assert (REPO / "REUSE.toml").exists()
    total, inline_n, reuse_errors = verify_reuse(REPO)
    assert total >= 120 and inline_n >= 70 and reuse_errors == [], f"REUSE errors: {reuse_errors}"
    manifest_text = (REPO / "MANIFEST.sha256").read_text(encoding="utf-8")
    forbidden_prefixes = (
        ".hypothesis/",
        ".pytest_cache/",
        ".mypy_cache/",
        ".ruff_cache/",
        "lean/.lake/",
        ".venv/",
    )
    listed: set[str] = set()
    for raw in manifest_text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        _, rel = line.split("  ", 1)
        listed.add(rel)
        for bad in forbidden_prefixes:
            assert not rel.startswith(bad), f"Cache artifact leaked into MANIFEST.sha256: {rel}"
    assert ".env.example" in listed, ".env.example must be tracked and hashed in MANIFEST.sha256"


def _independent_direct_parity_cnf_mc(
    outputs: list[list[int]], n: int, k: int, cadical_bin: str
) -> str:
    """
    Completely independent second CNF encoder for XAG multiplicative complexity
    (Playbook Checklist #14 differential check against exp4's chained-XOR encoder):
      - Allocates gate-evaluation wires FIRST and selector bits LAST (opposite order).
      - Encodes every linear XOR sum directly via full parity truth-table clauses
        (zero auxiliary XOR chain variables!) whenever fanin <= 6.
    """
    import itertools
    import subprocess
    import tempfile

    m = len(outputs)
    N = 1 << n
    var_cnt = 0

    def nv() -> int:
        nonlocal var_cnt
        var_cnt += 1
        return var_cnt

    clauses: list[list[int]] = []

    def add_direct_xor(lhs_terms: list[int], target_bit: int) -> None:
        """Enforce XOR(lhs_terms) == target_bit using direct parity cubes (split only if len > 6)."""
        terms = list(lhs_terms)
        while len(terms) > 6:
            chunk = terms[:5]
            rest = terms[5:]
            aux = nv()
            # XOR(chunk + [aux]) == 0
            add_direct_xor(chunk + [aux], 0)
            terms = [aux] + rest
        if not terms:
            if target_bit == 1:
                clauses.append([])
            return
        for assign in itertools.product((0, 1), repeat=len(terms)):
            if (sum(assign) & 1) != target_bit:
                # Forbid this assignment: literal is -v if assign==1 else +v
                clauses.append([-v if b == 1 else v for v, b in zip(terms, assign)])

    # Allocate evaluation variables FIRST (reversed layout from exp4)
    g_val = [[nv() for _ in range(k)] for _ in range(N)]
    l_val = [[nv() for _ in range(k)] for _ in range(N)]
    r_val = [[nv() for _ in range(k)] for _ in range(N)]

    # Selector variables SECOND
    sL = [[nv() for _ in range(n + j)] for j in range(k)]
    sR = [[nv() for _ in range(n + j)] for j in range(k)]
    cL = [nv() for _ in range(k)]
    cR = [nv() for _ in range(k)]
    oS = [[nv() for _ in range(n + k)] for _ in range(m)]
    oC = [nv() for _ in range(m)]

    for x in range(N):
        xb = [(x >> i) & 1 for i in range(n)]
        for j in range(k):
            lt = [cL[j]] + [sL[j][i] for i in range(n) if xb[i]]
            rt = [cR[j]] + [sR[j][i] for i in range(n) if xb[i]]
            for t in range(j):
                pl = nv()
                clauses.extend([[-pl, sL[j][n + t]], [-pl, g_val[x][t]], [pl, -sL[j][n + t], -g_val[x][t]]])
                lt.append(pl)
                pr = nv()
                clauses.extend([[-pr, sR[j][n + t]], [-pr, g_val[x][t]], [pr, -sR[j][n + t], -g_val[x][t]]])
                rt.append(pr)
            # Enforce XOR(lt + [l_val[x][j]]) == 0 and XOR(rt + [r_val[x][j]]) == 0
            add_direct_xor(lt + [l_val[x][j]], 0)
            add_direct_xor(rt + [r_val[x][j]], 0)
            # AND gate: g_val[x][j] <-> l_val[x][j] & r_val[x][j]
            clauses.append([-g_val[x][j], l_val[x][j]])
            clauses.append([-g_val[x][j], r_val[x][j]])
            clauses.append([g_val[x][j], -l_val[x][j], -r_val[x][j]])

        for o in range(m):
            ot = [oC[o]] + [oS[o][i] for i in range(n) if xb[i]]
            for t in range(k):
                po = nv()
                clauses.extend([[-po, oS[o][n + t]], [-po, g_val[x][t]], [po, -oS[o][n + t], -g_val[x][t]]])
                ot.append(po)
            add_direct_xor(ot, outputs[o][x])

    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False, encoding="ascii") as tf:
        cnf_p = pathlib.Path(tf.name)
        tf.write(f"p cnf {var_cnt} {len(clauses)}\n")
        for cl in clauses:
            tf.write(" ".join(str(lit) for lit in cl) + " 0\n")
    try:
        proc = subprocess.run([cadical_bin, "-q", str(cnf_p)], capture_output=True, text=True, timeout=15.0, check=False)
        return "SAT" if proc.returncode == 10 else ("UNSAT" if proc.returncode == 20 else f"ERR({proc.returncode})")
    finally:
        cnf_p.unlink(missing_ok=True)


def test_sat_encoder_second_independent_differential() -> None:
    """Differential check against an independent direct-parity-cube CNF encoder (Playbook #14)."""
    cadical = find_cadical()
    # 1. All 16 Boolean functions on n=2 for k=0 and k=1
    for tt_mask in range(16):
        tt = [(tt_mask >> x) & 1 for x in range(4)]
        for k in (0, 1):
            r1 = synthesize_multi_output_mc([tt], 2, k, cadical)
            r2 = _independent_direct_parity_cnf_mc([tt], 2, k, cadical)
            assert r1 == r2, f"Differential mismatch at n=2 mask={tt_mask}, k={k}: {r1} vs {r2}"

    # 2. Canonical n=3 benchmarks (x0&x1, x0&x1^x2, x0&x1&x2)
    f_and2 = eval_anf([(1 << 0) | (1 << 1)], 3)
    f_and3 = eval_anf([(1 << 0) | (1 << 1) | (1 << 2)], 3)
    for fn in (f_and2, f_and3):
        for k in (1, 2):
            assert synthesize_multi_output_mc([fn], 3, k, cadical) == _independent_direct_parity_cnf_mc([fn], 3, k, cadical)

    # 3. F_4 multiplication (n=4, m=2) at k=2 (UNSAT) and k=3 (SAT)
    f4_c0 = eval_anf([(1 << 0) | (1 << 2), (1 << 1) | (1 << 3)], 4)
    f4_c1 = eval_anf([(1 << 0) | (1 << 3), (1 << 1) | (1 << 2), (1 << 1) | (1 << 3)], 4)
    assert _independent_direct_parity_cnf_mc([f4_c0, f4_c1], 4, 2, cadical) == "UNSAT"
    assert _independent_direct_parity_cnf_mc([f4_c0, f4_c1], 4, 3, cadical) == "SAT"


def test_all_metadata_schemas_valid() -> None:
    """Verify structural integrity and single-version consistency across all metadata/SBOM/schema files."""
    version = (REPO / "VERSION").read_text(encoding="utf-8").strip()
    assert re.fullmatch(r"\d+\.\d+\.\d+", version)
    assert f'version = "{version}"' in (REPO / "pyproject.toml").read_text(encoding="utf-8")
    assert f"version: {version}" in (REPO / "CITATION.cff").read_text(encoding="utf-8")
    assert f'release_version: "{version}"' in (REPO / "lean" / "formalization.yaml").read_text(encoding="utf-8")
    assert 'version: "v0.4"' in (REPO / "lean" / "formalization.yaml").read_text(encoding="utf-8")

    # Validate JSON artifacts parse cleanly with required keys
    sbom = json.loads((REPO / "sbom.cdx.json").read_text(encoding="utf-8"))
    assert sbom.get("bomFormat") == "CycloneDX" and sbom.get("specVersion") == "1.5"
    assert isinstance(sbom.get("components"), list) and len(sbom["components"]) >= 5

    zen = json.loads((REPO / ".zenodo.json").read_text(encoding="utf-8"))
    assert "title" in zen and "creators" in zen and zen["creators"][0].get("orcid") == "0009-0006-8168-9648"

    comp = json.loads((REPO / "lean" / "comparator.json").read_text(encoding="utf-8"))
    assert comp.get("challenge_module") == "Challenge" and comp.get("solution_module") == "Solution"
    assert len(comp.get("definition_names", [])) == 20
    assert len(comp.get("theorem_names", [])) == 21
    assert "Catalytic.Solution.t3h_four_reg_powering" in comp["theorem_names"]
    assert "Catalytic.Challenge.T3h_FourRegPowering" in comp["definition_names"]
    assert "Catalytic.Solution.t3i_streaming_frequency_moment" in comp["theorem_names"]
    assert "Catalytic.Challenge.T3i_StreamingFrequencyMoment" in comp["definition_names"]

    for schema_name in ("repo-standard.schema.json", "project.schema.json"):
        sch = json.loads((REPO / schema_name).read_text(encoding="utf-8"))
        assert sch.get("type") == "object" and "required" in sch

    # Validate project.yaml covers all 95 Build Pipeline Models v1.0.0 steps with documented n/a reasons
    proj_text = (REPO / "project.yaml").read_text(encoding="utf-8")
    steps = re.findall(r'^  (P\d+\.\d+): \{status: ([\w/]+)(?:, note: "([^"]*)")?\}', proj_text, re.M)
    assert len(steps) == 95
    for step_id, status, note in steps:
        assert status in {"todo", "doing", "done", "n/a"}, f"Invalid status {status} on {step_id}"
        if status == "n/a":
            assert len(note.strip()) >= 8, f"n/a step {step_id} missing justification note"


def test_doc_citation_and_workflow_consistency() -> None:
    """Pass 5–6 anti-staleness, encoding, link-integrity, and cross-artifact consistency guard:
    - All BibTeX entries are cited in paper/main.tex, zero undefined refs, all 3 figures cited.
    - arXiv metadata abstract obeys the 1,920-character arXiv submission limit.
    - No stale theorem/module/line/kernel counts in active canonical docs.
    - All local blueprint links in docs/index.html match files deployed by pages.yml.
    - CI, POSIX runner, Windows runner, and REPLICATION.md invoke con-leche/con-ron inside `lake env`.
    - Zero UTF-8 BOMs, zero CRLF line endings across git-tracked text files.
    - Zero broken relative Markdown links across all tracked .md files and project.yaml.
    - Social preview SVG header pill is wide enough to prevent text clipping.
    """
    import subprocess

    tex = (REPO / "paper" / "main.tex").read_text(encoding="utf-8")
    bib = BIB_PATH.read_text(encoding="utf-8")
    bib_keys = set(re.findall(r"@\w+\{([^,]+),", bib))
    cited_keys: set[str] = set()
    for grp in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}", tex):
        for k in grp.split(","):
            cited_keys.add(k.strip())
    assert bib_keys == cited_keys, f"Bib/cite mismatch: uncited={bib_keys - cited_keys}, missing={cited_keys - bib_keys}"

    labels = set(re.findall(r"\\label\{([^}]+)\}", tex))
    refs = set(re.findall(r"\\(?:eq)?ref\{([^}]+)\}", tex))
    assert not (refs - labels), f"Undefined LaTeX refs: {refs - labels}"
    for fig_lbl in ("fig:T1", "fig:T3", "fig:T2T4"):
        assert fig_lbl in refs, f"Figure label {fig_lbl} is never cited in paper prose"

    # arXiv plain-text abstract must be <= 1920 characters
    arxiv_meta = (REPO / "paper" / "arxiv_metadata.txt").read_text(encoding="utf-8")
    abstract_part = arxiv_meta.split("Abstract:\n", 1)[1].strip()
    assert len(abstract_part) <= 1920, f"arXiv abstract too long: {len(abstract_part)} > 1920"

    # Verify active docs contain no stale counts from earlier passes
    stale_tokens = (
        "longest file 1{,}026",
        "12 headline theorems",
        "12 exported theorems",
        "14/14 decls",
        "18 headline theorems",
        "20 audited declarations",
        "13 zero-Mathlib",
        "6,564 lines",
        "6{,}564 lines",
        "3,307 declarations",
        "3,614 decls",
        "19 headline theorems",
        "19 exported theorems",
        "21 audited declarations",
        "21/21 decls",
        "21/21 audited",
        "7,892 lines",
        "7{,}892 lines",
        "8,036 lines",
        "8{,}036 lines",
        "8,069 lines",
        "8{,}069 lines",
        "8,145 lines",
        "8{,}145 lines",
        "3,506 declarations",
        "3,523 declarations",
        "3,525 declarations",
        "3,819 decls",
        "3,819 declarations",
        "3,836 decls",
        "3,836 declarations",
        "3,838 decls",
        "3,838 declarations",
        "7 Lean 4.35",
        "7-kernel",
        "0.811229",
        "0.81547",
        "0001-zero-mathlib-lean-kernel.md",
        "test_negative_and_regression_guards",
    )
    for rel in (
        "paper/main.tex",
        "paper/arxiv_metadata.txt",
        "README.md",
        "AGENTS.md",
        "llms.txt",
        "repo.yaml",
        "project.yaml",
        "docs/index.html",
        "docs/verification.md",
        "docs/faq.md",
        "docs/architecture.md",
        "docs/stack-matrix.md",
        "docs/plan/02-requirements.md",
        "docs/plan/02-metrics.md",
        "docs/plan/slices.md",
        "docs/launch/announcement.md",
        "docs/launch/release-checklist.md",
        "experiments/exp2_three_register_breakthrough.py",
    ):
        txt = (REPO / rel).read_text(encoding="utf-8")
        for tok in stale_tokens:
            assert tok not in txt, f"Stale token {tok!r} found in {rel}"

    # Verify docs/index.html blueprint hrefs are all copied by .github/workflows/pages.yml
    html = (REPO / "docs" / "index.html").read_text(encoding="utf-8")
    pages = (REPO / ".github" / "workflows" / "pages.yml").read_text(encoding="utf-8")
    for href in re.findall(r'href="(blueprint/[^"]+)"', html):
        assert f"_site/{href}" in pages, f"Broken Pages blueprint link {href} not copied in pages.yml"

    # Verify CI, POSIX runner, and REPLICATION.md invoke con-leche/con-ron via `lake env`
    ci_yml = (REPO / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")
    run_sh = (REPO / "scripts" / "run_all.sh").read_text(encoding="utf-8")
    repl_md = (REPO / "REPLICATION.md").read_text(encoding="utf-8")
    assert "lake env con-leche --verified" in ci_yml and "lake env con-ron --verified" in ci_yml
    assert "lake env con-leche --verified" in run_sh and "lake env con-ron --verified" in run_sh
    assert "lake env con-leche --verified" in repl_md and "lake env con-ron --verified" in repl_md

    # Verify social-preview.svg header pill is wide enough (>= 420px) for 36-char uppercase badge
    svg_txt = (REPO / "docs" / "media" / "social-preview.svg").read_text(encoding="utf-8")
    pill_m = re.search(r'<rect x="88" y="88" width="(\d+)"', svg_txt)
    assert pill_m is not None and int(pill_m.group(1)) >= 420, "social-preview.svg header pill clips text"

    # Verify ZERO UTF-8 BOMs, ZERO CRLF in tracked text files, and ZERO broken relative Markdown links
    binary_exts = {".pdf", ".gz", ".png", ".jpg", ".tsq", ".tsr", ".ots"}
    if (REPO / ".git").exists():
        tracked = subprocess.check_output(
            ["git", "-C", str(REPO), "ls-files"], text=True, encoding="utf-8"
        ).splitlines()
        for rel in tracked:
            p = REPO / rel
            if not p.exists() or p.suffix.lower() in binary_exts:
                continue
            raw = p.read_bytes()
            assert not raw.startswith(b"\xef\xbb\xbf"), f"UTF-8 BOM detected in {rel}"
            assert b"\r\n" not in raw, f"CRLF line endings detected in {rel}"
            if p.suffix.lower() == ".md":
                md_text = raw.decode("utf-8")
                for link in re.findall(r"\[[^\]]+\]\(([^)]+)\)", md_text):
                    if link.startswith(("http://", "https://", "mailto:", "#")):
                        continue
                    target = link.split("#", 1)[0]
                    if not target:
                        continue
                    resolved = (p.parent / target).resolve()
                    assert resolved.exists(), f"Broken relative Markdown link in {rel}: {link}"


def test_pass7_svg_factorization_and_table_integrity() -> None:
    """Pass 7 permanent regression guard covering:
    1. Strict XML 1.0 validity & text-in-rect non-overflow on social-preview.svg and docs/index.html SVG.
    2. Exact prime factorizations of D_4..D_9 matching exp2_three_register.json and paper/main.tex (D_6 = 2^5*3^2*5^7*17).
    3. Verbatim integer equality of Tables 3 & 4 in paper/main.tex vs. prog5_x7 & prog6_x9 in Lean.
    4. .editorconfig LF consistency, Audit-Repo.ps1 -LiteralPath safety, and canonical full Apache-2.0 LICENSE.
    """
    import xml.etree.ElementTree as ET

    # 1. Strict XML validity and text-in-rect bounding-box audit for both SVGs
    svg_txt = (REPO / "docs" / "media" / "social-preview.svg").read_text(encoding="utf-8")
    svg_root = ET.fromstring(svg_txt)
    svg_ns = "{http://www.w3.org/2000/svg}"
    card_rects = [
        (float(r.attrib["x"]), float(r.attrib["y"]), float(r.attrib["width"]), float(r.attrib["height"]))
        for r in svg_root.iter(f"{svg_ns}rect")
        if r.attrib.get("rx") == "12"
    ]
    assert len(card_rects) == 4
    for t_el in svg_root.iter(f"{svg_ns}text"):
        txt = (t_el.text or "").strip()
        if not txt or "x" not in t_el.attrib or "y" not in t_el.attrib:
            continue
        tx, ty = float(t_el.attrib["x"]), float(t_el.attrib["y"])
        fs = float(t_el.attrib.get("font-size", "16"))
        for rx, ry, rw, rh in card_rects:
            if rx <= tx <= rx + rw and ry <= ty <= ry + rh:
                est_w = len(txt) * fs * 0.54
                assert (tx - rx) + est_w <= rw - 6.0, f"social-preview.svg text overflow: {txt!r}"

    html_txt = (REPO / "docs" / "index.html").read_text(encoding="utf-8")
    svg_m = re.search(r"<svg\b[^>]*>.*?</svg>", html_txt, re.S)
    assert svg_m is not None, "Missing inline SVG dependency graph in docs/index.html"
    bp_root = ET.fromstring(svg_m.group(0))
    bp_rects = [
        (float(r.attrib["x"]), float(r.attrib["y"]), float(r.attrib["width"]), float(r.attrib["height"]))
        for r in bp_root.iter("rect")
    ]
    assert len(bp_rects) >= 12
    for t_el in bp_root.iter("text"):
        txt = (t_el.text or "").strip()
        if not txt or "x" not in t_el.attrib or "y" not in t_el.attrib:
            continue
        tx, ty = float(t_el.attrib["x"]), float(t_el.attrib["y"])
        fs = float(t_el.attrib.get("font-size", "12.5"))
        for rx, ry, rw, rh in bp_rects:
            if rx <= tx <= rx + rw and ry <= ty <= ry + rh:
                est_w = len(txt) * fs * 0.56
                assert est_w <= rw - 6.0, f"docs/index.html SVG box overflow: {txt!r} ({est_w:.1f} > {rw})"

    # 2. Exact prime factorizations of D_4..D_9 + deterministic primality + paper/main.tex check
    def is_prime_det(n: int) -> bool:
        if n < 2:
            return False
        for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
            if n == p:
                return True
            if n % p == 0:
                return False
        d, s = n - 1, 0
        while d % 2 == 0:
            d //= 2
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

    factorizations: dict[str, tuple[int, list[tuple[int, int]]]] = {
        "4": (54, [(2, 1), (3, 3)]),
        "5": (576, [(2, 6), (3, 2)]),
        "6": (382500000, [(2, 5), (3, 2), (5, 7), (17, 1)]),
        "7": (68724637549388656012800, [(2, 9), (3, 4), (5, 2), (7, 2), (538423, 1), (2512452073, 1)]),
        "8": (2656207148788801777680, [(2, 4), (3, 2), (5, 1), (7, 5), (137, 1), (1602207194491, 1)]),
        "9": (
            876702103804656272895371895753963647960420947968000,
            [(2, 14), (3, 6), (5, 3), (7, 3), (23, 1), (5263716917, 1), (22130905714103, 1), (638970634117961, 1)],
        ),
    }
    exp2 = json.loads((REPO / "results" / "exp2_three_register.json").read_text(encoding="utf-8"))
    prog_by_t = {str(p["t"]): p for p in exp2["programs"]}
    for t_key, (d_exact, facs) in factorizations.items():
        prod = 1
        for p, e in facs:
            assert is_prime_det(p), f"Non-prime factor {p} in D_{t_key}"
            prod *= p**e
        assert prod == d_exact, f"Factorization product mismatch for D_{t_key}"
        assert t_key in prog_by_t, f"Missing t={t_key} in exp2_three_register.json"
        assert int(prog_by_t[t_key]["out_scale"]) == d_exact
        assert prog_by_t[t_key]["bad_primes"] == [p for p, _ in facs]

    tex = (REPO / "paper" / "main.tex").read_text(encoding="utf-8")
    assert r"2^5 \cdot 3^2 \cdot 5^7 \cdot 17" in tex
    assert r"2^6 \cdot 3^2 \cdot 5^6" not in tex

    # 3. Verbatim cross-check of Table 3 (prog5_x7) & Table 4 (prog6_x9) in paper/main.tex vs Lean
    lean_t3 = (REPO / "lean" / "Catalytic" / "ThreeRegisterBreakthrough.lean").read_text(encoding="utf-8")

    def parse_lean_prog(name: str, monoms: list[tuple[int, int]]) -> list[tuple[int, int, list[int]]]:
        blk_m = re.search(rf"def {name} : List Pass3Instr :=\n((?:  loopStep .*\n)+)", lean_t3)
        assert blk_m is not None, f"Could not locate {name} in ThreeRegisterBreakthrough.lean"
        rows: list[tuple[int, int, list[int]]] = []
        for line in blk_m.group(1).strip().splitlines():
            m = re.search(r"\[([^\]]+)\]\s+\(?(-?\d+)\)?\s+\(?(-?\d+)\)?", line)
            assert m is not None, f"Unparseable loopStep line: {line}"
            term_map = {(int(a), int(b)): int(c) for a, b, c in re.findall(r"\((\d+),\s*(\d+),\s*(-?\d+)\)", m.group(1))}
            rows.append((int(m.group(2)), int(m.group(3)), [term_map.get(mon, 0) for mon in monoms]))
        return rows

    def parse_tex_table(label: str, n_coeffs: int) -> list[tuple[int, int, list[int]]]:
        m = re.search(rf"\\label\{{{label}\}}.*?\\midrule\n(.*?)\\bottomrule", tex, re.S)
        assert m is not None, f"Could not locate table {label} in paper/main.tex"
        rows: list[tuple[int, int, list[int]]] = []
        for line in m.group(1).strip().splitlines():
            cells = [int(c.replace("$", "").replace("{,}", "").replace("+", "").replace(r"\\", "").strip()) for c in line.split("&")]
            assert len(cells) == 3 + n_coeffs
            rows.append((cells[1], cells[2], cells[3:]))
        return rows

    assert parse_tex_table("tab:prog5", 4) == parse_lean_prog("prog5_x7", [(7, 0), (5, 1), (3, 2), (1, 3)])
    assert parse_tex_table("tab:prog6", 3) == parse_lean_prog("prog6_x9", [(9, 0), (5, 1), (1, 2)])

    # 4. .editorconfig LF consistency, Audit-Repo.ps1 -LiteralPath safety, and canonical Apache-2.0 LICENSE
    editorconfig = (REPO / ".editorconfig").read_text(encoding="utf-8")
    assert "end_of_line = crlf" not in editorconfig.lower()
    audit_ps1 = (REPO / "scripts" / "Audit-Repo.ps1").read_text(encoding="utf-8")
    assert "Get-ChildItem -LiteralPath $Root" in audit_ps1
    lic_txt = (REPO / "LICENSE").read_text(encoding="utf-8")
    assert "TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION" in lic_txt
    assert "END OF TERMS AND CONDITIONS" in lic_txt


def test_pass8_sbom_workflow_determinism_and_reuse_strictness() -> None:
    """Pass 8 permanent regression guard covering:
    1. CycloneDX 1.5 SBOM covers 100% of pinned packages in requirements.lock.txt with exact versions + serialNumber.
    2. All 4 experiment scripts specify newline='\\n' on JSON output writes for Windows/Linux byte determinism.
    3. CI workflow verifies MANIFEST.sha256 before cross-OS figure regeneration and downloads tools to /tmp or $env:TEMP.
    4. Release workflow packages MANIFEST.sha256.ots and TIMESTAMP_AUDIT.txt alongside .tsr.
    5. run_all.sh and run_all.ps1 strictly diff VerifyAxioms.lean against results/lean_axioms.txt.
    6. NonVacuity.lean includes concrete Fin 3 -> ModP 13 witness nonvac_T3i_witness inside nonvac_all_hypotheses.
    7. REUSE conflict-strictness: zero inline-vs-REUSE.toml license conflicts across all tracked files.
    """
    # 1. SBOM 100% requirements.lock.txt parity
    sbom = json.loads((REPO / "sbom.cdx.json").read_text(encoding="utf-8"))
    assert str(sbom.get("serialNumber", "")).startswith("urn:uuid:")
    sbom_map = {c["name"].lower(): c["version"] for c in sbom["components"]}
    lock_pkgs: dict[str, str] = {}
    for raw in (REPO / "requirements.lock.txt").read_text(encoding="utf-8").splitlines():
        ln = raw.strip()
        if not ln or ln.startswith("#") or "==" not in ln:
            continue
        pkg, ver = ln.split("==", 1)
        lock_pkgs[pkg.lower()] = ver.strip()
    assert len(lock_pkgs) >= 20
    for pkg, ver in lock_pkgs.items():
        assert sbom_map.get(pkg) == ver, f"SBOM missing or mismatched {pkg}=={ver} (got {sbom_map.get(pkg)!r})"
    assert sbom_map.get("lean4") == "4.35.0" and sbom_map.get("cadical") == "2.1.2"

    # 2. All 4 experiments write LF-only JSON via newline="\n"
    for exp_name in (
        "exp1_digit_sum_dichotomy.py",
        "exp2_three_register_breakthrough.py",
        "exp3_bilinear_and_balanced.py",
        "exp4_boolean_mc_companion.py",
    ):
        src = (REPO / "experiments" / exp_name).read_text(encoding="utf-8")
        assert 'newline="\\n"' in src, f"{exp_name} missing LF newline='\\n' on JSON output write"

    # 3. CI ordering and temp-dir downloads
    ci_txt = (REPO / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")
    assert ci_txt.index("sha256sum -c MANIFEST.sha256") < ci_txt.index("python scripts/make_figures.py")
    assert "/tmp/tectonic" in ci_txt
    assert "$env:TEMP\\elan-init.ps1" in ci_txt

    # 4. Release workflow includes full timestamp bundle (.tsr, .ots, TIMESTAMP_AUDIT.txt)
    rel_txt = (REPO / ".github" / "workflows" / "release.yml").read_text(encoding="utf-8")
    for fname in ("MANIFEST.sha256.tsr", "MANIFEST.sha256.ots", "TIMESTAMP_AUDIT.txt"):
        assert fname in rel_txt, f"release.yml missing provenance file {fname}"

    # 5. Both orchestrators diff VerifyAxioms.lean against results/lean_axioms.txt
    run_sh = (REPO / "scripts" / "run_all.sh").read_text(encoding="utf-8")
    run_ps1 = (REPO / "scripts" / "run_all.ps1").read_text(encoding="utf-8")
    assert "diff -u ../results/lean_axioms.txt" in run_sh
    assert "ca-bundle.crt" in run_sh
    assert "results/lean_axioms.txt" in run_ps1 and "AXIOM DRIFT DETECTED" in run_ps1

    # 6. NonVacuity.lean witnesses T3i over Fin 3 -> ModP 13
    nv_txt = (REPO / "lean" / "Catalytic" / "NonVacuity.lean").read_text(encoding="utf-8")
    assert "theorem nonvac_T3i_witness" in nv_txt and "nonvac_T3i_witness," in nv_txt

    # 7. LIMITATIONS.md synced (no stale 3,819 or 3,838)
    lim_txt = (REPO / "LIMITATIONS.md").read_text(encoding="utf-8")
    assert "3,819" not in lim_txt and "3,838" not in lim_txt and "3,544" in lim_txt


def test_pass9_cor54_matrix_lift_and_blueprint_integrity() -> None:
    """Pass 9 permanent regression guard covering:
    1. Exact non-commutative homogeneous lift mu_7(prog5_x7) over M_2(F_11) with non-commuting
       catalytic (O_0, u_0(z), v_0(z)), verifying O_0 + A^7 and clean restoration of u_0, v_0,
       plus mu_2-lifted Cook-Mertz finite-difference A^23 over M_2(F_11) and M_3(F_11) and
       the exact scalar-register binomial identity 3m^2 + C(m^2+1,2) = 2m^2 + C(m^2+2,2) - 1.
    2. Verbatim #print axioms parity across results/lean_axioms.txt, README.md, and docs/index.html.
    3. Strict HTML5 tag balance, unique IDs, aria-pressed filter buttons, and 21 == All (21) rows
       in docs/index.html.
    4. Required-key JSON Schema checks on repo.yaml and project.yaml (stdlib-only).
    5. Anti-staleness guards on cold-start Lean build time (56.6 s / < 60 s) and maxRecDepth disclosure.
    """
    from html.parser import HTMLParser

    # 1. Exact non-commutative matrix powering lift (Corollary 5.4) over M_2(F_11)
    p = 11

    def mat_add(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
        n = len(a)
        return [[(a[i][j] + b[i][j]) % p for j in range(n)] for i in range(n)]

    def mat_scale(c: int, a: list[list[int]]) -> list[list[int]]:
        return [[(c * x) % p for x in row] for row in a]

    def mat_mul(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
        n = len(a)
        return [[sum(a[i][k] * b[k][j] for k in range(n)) % p for j in range(n)] for i in range(n)]

    def mat_pow(a: list[list[int]], e: int) -> list[list[int]]:
        n = len(a)
        res = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
        base = a
        while e > 0:
            if e & 1:
                res = mat_mul(res, base)
            base = mat_mul(base, base)
            e >>= 1
        return res

    # Basis matrices E_0..E_3 of M_2(F_11)
    basis_2: list[list[list[int]]] = [
        [[1, 0], [0, 0]],
        [[0, 1], [0, 0]],
        [[0, 0], [1, 0]],
        [[0, 0], [0, 1]],
    ]
    MatPoly = dict[tuple[int, int, int, int], int]

    def poly_add(a: MatPoly, b: MatPoly) -> MatPoly:
        out = dict(a)
        for k, v in b.items():
            nv = (out.get(k, 0) + v) % p
            if nv:
                out[k] = nv
            else:
                out.pop(k, None)
        return out

    def poly_scale(c: int, a: MatPoly) -> MatPoly:
        c %= p
        if c == 0:
            return {}
        return {k: (v * c) % p for k, v in a.items()}

    def poly_mul(a: MatPoly, b: MatPoly) -> MatPoly:
        out: MatPoly = {}
        for k1, v1 in a.items():
            for k2, v2 in b.items():
                k = (k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2], k1[3] + k2[3])
                nv = (out.get(k, 0) + v1 * v2) % p
                if nv:
                    out[k] = nv
                else:
                    out.pop(k, None)
        return out

    def poly_pow(a: MatPoly, e: int) -> MatPoly:
        res: MatPoly = {(0, 0, 0, 0): 1}
        for _ in range(e):
            res = poly_mul(res, a)
        return res

    # DP table S(alpha) = sum over all words of counts alpha of E_{w_1} ... E_{w_d}
    sym_dp: dict[tuple[int, int, int, int], list[list[int]]] = {(0, 0, 0, 0): [[1, 0], [0, 1]]}

    def sym_sum(alpha: tuple[int, int, int, int]) -> list[list[int]]:
        if alpha in sym_dp:
            return sym_dp[alpha]
        acc = [[0, 0], [0, 0]]
        for j in range(4):
            if alpha[j] > 0:
                prev = list(alpha)
                prev[j] -= 1
                acc = mat_add(acc, mat_mul(sym_sum((prev[0], prev[1], prev[2], prev[3])), basis_2[j]))
        sym_dp[alpha] = acc
        return acc

    def mu_d(poly: MatPoly, deg: int) -> list[list[int]]:
        fact_d = math.factorial(deg) % p
        out = [[0, 0], [0, 0]]
        for alpha, coeff in poly.items():
            assert sum(alpha) == deg
            denom = 1
            for ai in alpha:
                denom = (denom * math.factorial(ai)) % p
            multinom = (fact_d * pow(denom, -1, p)) % p
            weight = (coeff * pow(multinom, -1, p)) % p
            out = mat_add(out, mat_scale(weight, sym_sum(alpha)))
        return out

    # Parse literal prog5_x7 from ThreeRegisterBreakthrough.lean
    lean_t3 = (REPO / "lean" / "Catalytic" / "ThreeRegisterBreakthrough.lean").read_text(encoding="utf-8")
    blk_m = re.search(r"def prog5_x7 : List Pass3Instr :=\n((?:  loopStep .*\n)+)", lean_t3)
    assert blk_m is not None
    prog5_steps: list[tuple[list[tuple[int, int, int]], int, int]] = []
    for line in blk_m.group(1).strip().splitlines():
        m = re.search(r"\[([^\]]+)\]\s+\(?(-?\d+)\)?\s+\(?(-?\d+)\)?", line)
        assert m is not None
        terms = [(int(a), int(b), int(c)) for a, b, c in re.findall(r"\((\d+),\s*(\d+),\s*(-?\d+)\)", m.group(1))]
        prog5_steps.append((terms, int(m.group(2)), int(m.group(3))))

    mat_a = [[1, 2], [3, 5]]
    mat_o0 = [[4, 7], [2, 9]]
    assert mat_mul(mat_a, mat_o0) != mat_mul(mat_o0, mat_a)
    ell_a: MatPoly = {
        (1, 0, 0, 0): mat_a[0][0],
        (0, 1, 0, 0): mat_a[0][1],
        (0, 0, 1, 0): mat_a[1][0],
        (0, 0, 0, 1): mat_a[1][1],
    }
    u0: MatPoly = {(1, 0, 0, 0): 2, (0, 1, 0, 0): 5, (0, 0, 1, 0): 1, (0, 0, 0, 1): 8}
    v0: MatPoly = {
        (2, 0, 0, 0): 3,
        (1, 1, 0, 0): 7,
        (1, 0, 1, 0): 4,
        (1, 0, 0, 1): 9,
        (0, 2, 0, 0): 2,
        (0, 1, 1, 0): 6,
        (0, 1, 0, 1): 1,
        (0, 0, 2, 0): 5,
        (0, 0, 1, 1): 8,
        (0, 0, 0, 2): 10,
    }
    inv_d5 = pow(576, -1, p)
    o_reg = [row[:] for row in mat_o0]
    u_reg = dict(u0)
    v_reg = dict(v0)
    for terms, q_next, alpha in prog5_steps:
        f_uv: MatPoly = {}
        for du, dv, c in terms:
            term_poly = poly_mul(poly_pow(u_reg, du), poly_pow(v_reg, dv))
            f_uv = poly_add(f_uv, poly_scale(c, term_poly))
        o_reg = mat_add(o_reg, mat_scale(inv_d5, mu_d(f_uv, 7)))
        if q_next != 0:
            v_reg = poly_add(v_reg, poly_scale(-q_next, poly_pow(u_reg, 2)))
        u_reg = poly_add(u_reg, poly_scale(alpha, ell_a))
        if q_next != 0:
            v_reg = poly_add(v_reg, poly_scale(q_next, poly_pow(u_reg, 2)))
    assert o_reg == mat_add(mat_o0, mat_pow(mat_a, 7)), "mu_7(prog5_x7) failed to compute O_0 + A^7"
    assert u_reg == u0 and v_reg == v0, "mu_7(prog5_x7) failed to cleanly restore catalytic u_0, v_0"

    # Non-commutative Cook-Mertz finite-difference powering for A^23 = A^2 * (A^7)^3
    # (a) Single-catalyst mu_2-lifted over M_2(F_11) with non-commuting U_0
    f0 = mat_pow(mat_a, 2)
    f1 = mat_pow(mat_pow(mat_a, 7), 3)
    ell_u0: MatPoly = {(1, 0, 0, 0): 4, (0, 1, 0, 0): 7, (0, 0, 1, 0): 2, (0, 0, 0, 1): 9}
    ell_f0: MatPoly = {(1, 0, 0, 0): f0[0][0], (0, 1, 0, 0): f0[0][1], (0, 0, 1, 0): f0[1][0], (0, 0, 0, 1): f0[1][1]}
    ell_f1: MatPoly = {(1, 0, 0, 0): f1[0][0], (0, 1, 0, 0): f1[0][1], (0, 0, 1, 0): f1[1][0], (0, 0, 0, 1): f1[1][1]}
    cm_acc = [[0, 0], [0, 0]]
    for s0 in (0, 1):
        for s1 in (0, 1):
            sign = 1 if (2 - s0 - s1) % 2 == 0 else p - 1
            g_s = poly_add(ell_u0, poly_add(poly_scale(s0, ell_f0), poly_scale(s1, ell_f1)))
            cm_acc = mat_add(cm_acc, mat_scale(sign, mu_d(poly_pow(g_s, 2), 2)))
    assert mat_scale(pow(2, -1, p), cm_acc) == mat_pow(mat_a, 23)

    # (b) Two-factor non-commutative Cook-Mertz product on M_3(F_11) with non-commuting U_0
    a3 = [[1, 2, 0], [0, 3, 1], [4, 1, 2]]
    u3 = [[2, 0, 5], [1, 4, 3], [7, 2, 1]]
    assert mat_mul(a3, u3) != mat_mul(u3, a3)
    f3_0, f3_1 = mat_pow(a3, 2), mat_pow(mat_pow(a3, 7), 3)
    acc3 = [[0, 0, 0], [0, 0, 0], [0, 0, 0]]
    for s0 in (0, 1):
        for s1 in (0, 1):
            sign = 1 if (2 - s0 - s1) % 2 == 0 else p - 1
            t0 = mat_add(u3, mat_scale(s0, f3_0))
            t1 = mat_add(u3, mat_scale(s1, f3_1))
            acc3 = mat_add(acc3, mat_scale(sign, mat_mul(t0, t1)))
    assert acc3 == mat_pow(a3, 23)

    # Scalar-register binomial identity for Corollary 5.4(1) across m = 1..20
    for dim in range(1, 21):
        b = dim * dim
        assert 3 * b + math.comb(b + 1, 2) == 2 * b + math.comb(b + 2, 2) - 1

    # 2. Verbatim #print axioms parity across lean_axioms.txt, README.md, and docs/index.html
    axioms_txt = (REPO / "results" / "lean_axioms.txt").read_text(encoding="utf-8").strip()
    readme_txt = (REPO / "README.md").read_text(encoding="utf-8")
    html_txt = (REPO / "docs" / "index.html").read_text(encoding="utf-8")
    assert f"```text\n{axioms_txt}\n```" in readme_txt, "README.md axiom block drifted from results/lean_axioms.txt"
    assert f"<pre><code>{axioms_txt}</code></pre>" in html_txt, "docs/index.html axiom block drifted from results/lean_axioms.txt"

    # 3. Strict HTML5 tag balance, unique IDs, aria-pressed buttons, and 21 == All (21) rows
    void_tags = {"meta", "link", "br", "hr", "img", "input", "source", "area", "base", "col", "embed", "param", "track", "wbr"}

    class StrictHTMLAuditor(HTMLParser):
        def __init__(self) -> None:
            super().__init__(convert_charrefs=False)
            self.stack: list[str] = []
            self.ids: list[str] = []
            self.filter_btns: list[dict[str, str | None]] = []
            self.fam_rows: list[str] = []

        def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
            ad = dict(attrs)
            if "id" in ad and ad["id"] is not None:
                self.ids.append(ad["id"])
            if tag == "button" and ad.get("class") and "filter-btn" in (ad.get("class") or ""):
                self.filter_btns.append(ad)
            if tag == "tr" and ad.get("data-fam"):
                self.fam_rows.append(str(ad["data-fam"]))
            if tag not in void_tags:
                self.stack.append(tag)

        def handle_endtag(self, tag: str) -> None:
            if tag in void_tags:
                return
            assert self.stack and self.stack[-1] == tag, f"Mismatched HTML closing tag </{tag}> (stack={self.stack[-3:]})"
            self.stack.pop()

    auditor = StrictHTMLAuditor()
    auditor.feed(html_txt)
    auditor.close()
    assert not auditor.stack, f"Unclosed HTML tags in docs/index.html: {auditor.stack}"
    assert len(auditor.ids) == len(set(auditor.ids)), f"Duplicate HTML IDs in docs/index.html: {auditor.ids}"
    assert len(auditor.fam_rows) == 21 and "All (21)" in html_txt
    assert len(auditor.filter_btns) == 6
    assert all("aria-pressed" in b for b in auditor.filter_btns), "Filter buttons missing WCAG aria-pressed attribute"
    assert sum(1 for b in auditor.filter_btns if b.get("aria-pressed") == "true") == 1
    assert "Fin 3 &rarr; ModP 13" in html_txt or "Fin 3 → ModP 13" in html_txt

    # 4. Required-key JSON Schema checks on repo.yaml and project.yaml (stdlib-only)
    for yml_name, schema_name in (
        ("repo.yaml", "repo-standard.schema.json"),
        ("project.yaml", "project.schema.json"),
    ):
        schema = json.loads((REPO / schema_name).read_text(encoding="utf-8"))
        top_keys = set(re.findall(r"^([a-zA-Z0-9_]+):", (REPO / yml_name).read_text(encoding="utf-8"), re.M))
        missing = set(schema["required"]) - top_keys
        assert not missing, f"{yml_name} missing required schema keys: {missing}"

    # 5. Anti-staleness guards on cold-start Lean build time & maxRecDepth disclosure
    for rel in ("docs/stack-matrix.md", "project.yaml", "docs/plan/02-requirements.md"):
        txt = (REPO / rel).read_text(encoding="utf-8")
        for bad in ("< 30 s", "< 30s", "~45 s"):
            assert bad not in txt, f"Stale Lean build timing {bad!r} found in {rel}"
        assert "56.6 s" in txt and "< 60 s" in txt, f"Missing measured 56.6 s (< 60 s) cold-build timing in {rel}"
    lim_txt = (REPO / "LIMITATIONS.md").read_text(encoding="utf-8")
    assert "maxRecDepth 4096" in lim_txt and "maxRecDepth 8192" in lim_txt


def test_pass10_palomar_t4_and_provenance_integrity() -> None:
    """Pass 10 permanent regression guard addressing all 3 Palomar editorial review findings:
    1. T4 enforces explicit CatOp.usesOnly register-set containment within <= k + 2 designated
       registers in BalancedProduct.lean, Challenge.lean, PalomarChallenge.lean, and PalomarSolution.lean.
    2. Structured verification accounts (formalization.yaml, results/six_kernel_audit.txt, paper/main.tex)
       report 5 distinct completed local kernel implementations (6 runs) and retain the failed Windows
       lean4lean.exe attempt honestly as a limitation rather than a completed check.
    3. Pinned provenance documents consistently separate confirmed identifiers (Zenodo Concept DOI
       10.5281/zenodo.24517198, SWHID swh:1:snp:f960eeda6f145e54c0ac52538ace866a16e24085) from
       planned/unassigned deposits (Palomar, arXiv, HAL).
    """
    # 1. T4 register-set containment in all four Lean contract/proof files
    for rel in (
        "lean/Catalytic/BalancedProduct.lean",
        "lean/Challenge.lean",
        "lean/PalomarChallenge.lean",
        "lean/PalomarSolution.lean",
    ):
        txt = (REPO / rel).read_text(encoding="utf-8")
        assert "usesOnly" in txt, f"Missing CatOp.usesOnly register containment in {rel}"
        assert "regs.length ≤ k + 2" in txt or "designatedRegs_length_le" in txt, (
            f"Missing <= k + 2 designated register bound in {rel}"
        )

    # 2. Structured verification accounts honestly report 5 distinct kernels (6 runs) + lean4lean limitation
    fyaml = (REPO / "lean" / "formalization.yaml").read_text(encoding="utf-8")
    assert "7 Lean 4.35" not in fyaml
    assert "5" in fyaml and "6 runs" in fyaml
    assert "excluded from the completed local" in fyaml or "omitted from the completed verification count" in fyaml
    audit_txt = (REPO / "results" / "six_kernel_audit.txt").read_text(encoding="utf-8")
    assert "5 Distinct Implementations / 6 Completed Runs" in audit_txt
    assert "NOT counted among the 5 completed locally reproducible kernel implementations" in audit_txt
    assert "3,544" in audit_txt and "3,502" in audit_txt
    tex = (REPO / "paper" / "main.tex").read_text(encoding="utf-8")
    assert r"\texttt{lean4lean}" not in tex.split(r"\maketitle", 1)[0]

    # 3. Zero contradictory pre-mint archival provenance phrases across pinned docs
    contradictory = (
        "PENDING (external): Zenodo DOI",
        "PENDING (external DOI/SWHID)",
        "Awaiting owner push to GitHub",
        "planned Software Heritage SWHID",
        "Planned archival mirrors:",
        "Verified locally, release-ready for GitHub/Palomar/archival",
        "Post-push external steps (live GitHub Actions CI/SLSA attestations, Zenodo/OSF DOI minting",
    )
    for rel in (
        "README.md",
        "AGENTS.md",
        "LIMITATIONS.md",
        "ROADMAP.md",
        "CHANGELOG.md",
        "project.yaml",
        "llms-full.txt",
        "docs/operations.md",
        "docs/launch/channels.md",
        "docs/launch/release-checklist.md",
        "docs/reviews/01-10-pass-review.md",
        "lean/formalization.yaml",
    ):
        txt = (REPO / rel).read_text(encoding="utf-8")
        for bad in contradictory:
            assert bad not in txt, f"Contradictory archival provenance {bad!r} found in {rel}"
        assert "10.5281/zenodo.24517198" in txt, f"Confirmed Zenodo Concept DOI missing in {rel}"


def test_pass11_cycle3_audit_and_adaptive_fork_engine(tmp_path: pathlib.Path) -> None:
    """Pass 11 (3-Cycle Deep Audit + Adaptive Forking Universal Workbench) permanent regression guard:
    1. Paper mathematical typo guards (Definition 2.1 R_0..R_{r-1} indexing; Theorem T4 pool size k;
       Table 1 5 kernels / 6 runs parity).
    2. Lean lakefile.toml version matches VERSION (1.0.1) & T3f docstring axiom honesty.
    3. Zero residual '6 kernels' / '6 independent kernels' / '6 Lean kernels' in active canonical docs.
    4. LRAT verifier handles duplicate literals inside a unit clause without false rejection.
    5. Universal Adaptive Forking PWA files exist, manifest.webmanifest is valid JSON, pages.yml
       deploys them, every Lean prog5_x7..prog9_x15 coefficient matches docs/catalytic-engine.js
       verbatim, and live Node.js execution verifies all engines + 1-bit fault rejection + fuzzer.
    """
    import shutil
    import subprocess

    # 1. Paper mathematical & table parity guards
    tex = (REPO / "paper" / "main.tex").read_text(encoding="utf-8")
    assert r"p(R_0, \dots, R_{i-1}, R_{i+1}, \dots, R_{r-1})" in tex
    assert r"p(R_1, \dots, R_{i-1}, R_{i+1}, \dots, R_r)" not in tex
    assert r"auxiliary pool $P$ of size $k$ (total $k + 3$ registers)" in tex
    assert r"auxiliary pool $P$ of size $k - 1$" not in tex
    assert r"5 kernels / 6 runs (Table~\ref{tab:kernels})" in tex

    # 2. Lean version & T3f docstring honesty
    version = (REPO / "VERSION").read_text(encoding="utf-8").strip()
    assert f'version = "{version}"' in (REPO / "lean" / "lakefile.toml").read_text(encoding="utf-8")
    lean_t3 = (REPO / "lean" / "Catalytic" / "ThreeRegisterBreakthrough.lean").read_text(encoding="utf-8")
    assert "with zero axioms" not in lean_t3

    # 3. Zero stale '6 kernels' wording across active canonical docs
    stale_6k_re = re.compile(
        r"\b6\s+(?:independent\s+|distinct\s+|Lean\s+)?kernels?\b|6\s*/\s*6\s+(?:Independent\s+)?Kernels",
        re.I,
    )
    for rel in (
        "CLAIMS.md",
        "README.md",
        "paper/main.tex",
        "docs/index.html",
        "docs/media/social-preview.svg",
        "repo.yaml",
        "project.yaml",
        "docs/glossary.md",
        "docs/stack-matrix.md",
        "docs/verification.md",
        "docs/plan/slices.md",
        "llms.txt",
    ):
        txt = (REPO / rel).read_text(encoding="utf-8")
        assert not stale_6k_re.search(txt), f"Stale '6 kernels' wording found in {rel}"

    # 4. LRAT duplicate-literal unit clause regression guard
    dup_cnf = tmp_path / "dup_unit.cnf"
    dup_lrat = tmp_path / "dup_unit.lrat"
    dup_cnf.write_text("p cnf 1 2\n1 1 0\n-1 0\n", encoding="ascii", newline="\n")
    dup_lrat.write_text("3 0 1 2 0\n", encoding="ascii", newline="\n")
    steps, dels = verify_lrat(dup_cnf, dup_lrat)
    assert steps == 1 and dels == 0

    # 5. Adaptive Forking PWA files, Pages deployment, and verbatim Lean-to-JS coefficient parity
    js_path = REPO / "docs" / "catalytic-engine.js"
    manifest_path = REPO / "docs" / "manifest.webmanifest"
    sw_path = REPO / "docs" / "sw.js"
    assert js_path.exists() and manifest_path.exists() and sw_path.exists()
    pwa_manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert pwa_manifest.get("start_url") == "./index.html" and pwa_manifest.get("display") == "standalone"

    pages_yml = (REPO / ".github" / "workflows" / "pages.yml").read_text(encoding="utf-8")
    for asset in ("catalytic-engine.js", "manifest.webmanifest", "sw.js"):
        assert f"_site/{asset}" in pages_yml, f"pages.yml missing deployment copy for {asset}"

    js_txt = js_path.read_text(encoding="utf-8")
    for prog_name in ("prog5_x7", "prog6_x9", "prog7_x11", "prog8_x13", "prog9_x15"):
        blk_m = re.search(rf"def {prog_name} : List Pass3Instr :=\n((?:  loopStep .*\n)+)", lean_t3)
        assert blk_m is not None
        for du, dv, coeff in re.findall(r"\((\d+),\s*(\d+),\s*(-?\d+)\)", blk_m.group(1)):
            needle = f"[{du}, {dv}, {coeff}n]"
            assert needle in js_txt, f"JS engine missing Lean coefficient {needle} from {prog_name}"

    # 6. Live cross-runtime Node.js differential verification (when Node is installed)
    node_bin = shutil.which("node")
    if node_bin:
        node_check = (
            f"const E = require({json.dumps(str(js_path))});"
            "for (const t of [4,5,6,7,8,9]) {"
            "  if (!E.execPass3(t, 7n, 0n, {O0: 19n, u0: -11n, v0: 23n}).verified) process.exit(11);"
            "  if (!E.execPass3(t, 5n, 11n, {O0: 3n, u0: 7n, v0: 9n}).verified) process.exit(12);"
            "  if (E.execPass3(t, 5n, 11n, {O0: 3n, u0: 7n, v0: 9n, faultBit: true}).verified) process.exit(13);"
            "}"
            "for (const [N,p] of [[7,1009],[13,1009],[20,1009],[91,1009],[169,1009],[25,5]]) {"
            "  const r = E.execFourRegPowering(N, 7, p, {engine:'adaptive'});"
            "  if (!r.verified) process.exit(14);"
            "  if (E.execFourRegPowering(N, 7, p, {engine:'adaptive', faultBit:true}).verified) process.exit(15);"
            "}"
            "if (!E.execStreamingMoment([3,1,4,1,5,9], 20, 1009, {engine:'adaptive'}).verified) process.exit(16);"
            "if (!E.execMatrixLiftProg5([[1,2],[3,5]], 11).verified) process.exit(17);"
            "if (!E.execT2BilinearFrobenius(8, 0x57).verified) process.exit(18);"
            "if (!E.execT4BalancedProduct([2,-3,5,7,-1,2,3,-2], undefined, 1n).verified) process.exit(19);"
            "const f = E.runAdversarialFuzz(200, 20261125);"
            "if (f.failed !== 0 || f.passed !== 200) process.exit(20);"
        )
        proc = subprocess.run([node_bin, "-e", node_check], capture_output=True, text=True, timeout=30, check=False)
        assert proc.returncode == 0, f"Node.js differential check failed (rc={proc.returncode}): {proc.stderr}"


def test_pass12_deep_hardening_and_pwa_v12(tmp_path: pathlib.Path) -> None:
    """Pass 12 (Second 3-Cycle Forensic Hardening + Adaptive Forking PWA v1.2) permanent regression guard:
    1. Zero ghost 'probe12' reference in paper/main.tex; exp2_three_register.json reproduces r=4 Remark 5.5.
    2. LRAT verifier strictly rejects duplicate RAT negative hints & unknown/non-pivot RAT targets.
    3. Zero raw LaTeX in docs/index.html; square PWA icon.svg XML-valid & deployed in manifest/sw/pages.yml.
    4. Official GitHub Actions upgraded to Node-24-native major tags (checkout@v7, setup-python@v7, etc.).
    5. Live Node.js audit of catalytic-engine.js v1.2.0: N=1 (1 access), composite ring Z/mZ invertibility,
       honest large-N infeasibility (p=3), bad-prime p=137 dodge, exact Z binomExact, N=10^30 BigInt ratios,
       Catalytic Byte-Vault byte-for-byte restoration + 1-bit fault rejection, and 6-mode 300-trial fuzzer.
    """
    import shutil
    import subprocess
    import xml.etree.ElementTree as ET

    # 1. Paper Remark 5.5 & exp2 reproducible r=4 frontier
    tex = (REPO / "paper" / "main.tex").read_text(encoding="utf-8")
    assert "probe12" not in tex, "Ghost reference 'probe12' found in paper/main.tex"
    exp2 = json.loads((REPO / "results" / "exp2_three_register.json").read_text(encoding="utf-8"))
    r4 = exp2.get("r4_triangular_frontier", [])
    assert len(r4) == 2 and r4[0]["t"] == 5 and r4[0]["achieved_degree"] == 9
    assert r4[1]["t"] == 6 and r4[1]["achieved_degree"] == 11

    # 2. Strict RAT negative-hint validation in verify_lrat.py
    bad_cnf = tmp_path / "rat_dup.cnf"
    bad_lrat = tmp_path / "rat_dup.lrat"
    bad_cnf.write_text("p cnf 2 2\n-1 2 0\n-1 -2 0\n", encoding="ascii", newline="\n")
    bad_lrat.write_text("3 1 0 -1 -1 0\n4 0 3 1 2 0\n", encoding="ascii", newline="\n")
    try:
        verify_lrat(bad_cnf, bad_lrat)
    except ValueError as exc:
        assert "duplicate RAT negative hint" in str(exc)
    else:
        raise AssertionError("verify_lrat failed to reject duplicate RAT negative hint")

    # 3. PWA v1.2 hygiene: zero raw LaTeX in HTML, valid square icon.svg, network-first SW, pages.yml parity
    html = (REPO / "docs" / "index.html").read_text(encoding="utf-8")
    assert r"$O(\log N)$" not in html, "Unrendered raw LaTeX found in docs/index.html"
    assert 'href="./icon.svg"' in html
    icon_svg = REPO / "docs" / "icon.svg"
    assert icon_svg.exists()
    ET.parse(icon_svg)
    pwa_manifest = json.loads((REPO / "docs" / "manifest.webmanifest").read_text(encoding="utf-8"))
    assert any(ic.get("src") == "./icon.svg" for ic in pwa_manifest.get("icons", []))
    sw_txt = (REPO / "docs" / "sw.js").read_text(encoding="utf-8")
    assert "./icon.svg" in sw_txt and "fetch(event.request)" in sw_txt
    pages_yml = (REPO / ".github" / "workflows" / "pages.yml").read_text(encoding="utf-8")
    assert "_site/icon.svg" in pages_yml and "actions/checkout@v7" in pages_yml
    assert "actions/upload-pages-artifact@v5" in pages_yml and "actions/deploy-pages@v5" in pages_yml

    # 4. Node-24-native official GitHub Actions in ci.yml & release.yml
    ci_yml = (REPO / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")
    rel_yml = (REPO / ".github" / "workflows" / "release.yml").read_text(encoding="utf-8")
    assert "actions/checkout@v7" in ci_yml and "actions/setup-python@v7" in ci_yml
    assert "actions/attest-build-provenance@v4" in ci_yml and "actions/attest-build-provenance@v4" in rel_yml

    # 5. Live Node.js adversarial audit of catalytic-engine.js v1.2.0
    node_bin = shutil.which("node")
    if node_bin:
        js_path = REPO / "docs" / "catalytic-engine.js"
        node_check = (
            f"const E = require({json.dumps(str(js_path))});"
            "if (E.planAdaptiveFork({N:1,p:1009,workload:'scalar'}).comparison.adaptive_fork.accesses !== '1') process.exit(31);"
            "if (E.execFourRegPowering(1, 7, 1009, {engine:'adaptive'}).accesses !== 1) process.exit(32);"
            "if (E.planAdaptiveFork({N:9,p:9,workload:'scalar'}).comparison.adaptive_fork.feasible !== false) process.exit(33);"
            "if (E.planAdaptiveFork({N:5000,p:3,workload:'scalar'}).comparison.adaptive_fork.feasible !== false) process.exit(34);"
            "if (!E.execFourRegPowering(91, 42, 1009n*1013n, {engine:'adaptive'}).verified) process.exit(35);"
            "const pl137 = E.planAdaptiveFork({N:169,p:137,workload:'scalar'});"
            "if (!pl137.forkCandidates.some(c => c.id==='prog8_x13' && c.status==='pruned')) process.exit(36);"
            "if (!E.execFourRegPowering(169, 7, 137, {engine:'adaptive'}).verified) process.exit(37);"
            "if (E.binomModP(10, 4, 0) !== 210n) process.exit(38);"
            "const plHuge = E.planAdaptiveFork({N:'1000000000000000000000000000000',p:1009,workload:'scalar'});"
            "if (!plHuge.comparison.adaptive_fork.feasible || !(plHuge.speedupFactor > 1)) process.exit(39);"
            "const raw = new TextEncoder().encode('CatalyticVault:WatchPhoneLaptop');"
            "const vOk = E.execCatalyticByteVault(raw, 91, 7, 1009);"
            "const vBad = E.execCatalyticByteVault(raw, 91, 7, 1009, {faultBit:true});"
            "if (!vOk.verified || !vOk.bytesEqual || vOk.corruptedByteCount !== 0 || vBad.verified || vBad.bytesEqual) process.exit(40);"
            "const f = E.runAdversarialFuzz(300, 20261125);"
            "if (f.failed !== 0 || f.passed !== 300) process.exit(41);"
        )
        proc = subprocess.run([node_bin, "-e", node_check], capture_output=True, text=True, timeout=30, check=False)
        assert proc.returncode == 0, f"Node.js v1.2 audit failed (rc={proc.returncode}): {proc.stderr}"


def test_pass13_v13_cli_animator_and_benchmark() -> None:
    """Pass 13 permanent regression guard:
    1. Unused LaTeX packages (cleveref, multirow, mathtools) stripped from paper/main.tex.
    2. PWA v1.3 features present in docs/index.html (non-trivial T2 default k=5, interactive
       register scramble animator, live device calibration benchmark, auto-run on open).
    3. Universal zero-dependency Node.js CLI subcommands (plan, run, vault, bench) exit 0
       and emit verified JSON proofs + identical SHA-256 before/after hashes.
    """
    import shutil
    import subprocess

    tex = (REPO / "paper" / "main.tex").read_text(encoding="utf-8")
    for unused in ("cleveref", "multirow", "mathtools"):
        assert unused not in tex, f"Unused LaTeX package {unused!r} still loaded in paper/main.tex"

    html = (REPO / "docs" / "index.html").read_text(encoding="utf-8")
    assert re.search(r"Adaptive Forking Offline PWA v1\.[3-9]", html) is not None
    assert 'id="t2-k" type="number" min="1" max="12" value="5"' in html
    assert "toggleTracePlay" in html and "runDeviceBenchUI" in html

    node_bin = shutil.which("node")
    if node_bin:
        js_path = str(REPO / "docs" / "catalytic-engine.js")
        for cmd_args, check_fn in [
            (
                ["plan", "--N", "91", "--p", "1009"],
                lambda d: d["winner"]["accesses"] == "80" and d["speedupFactor"] >= 2.5,
            ),
            (
                ["run", "--N", "91", "--p", "1009", "--x", "7"],
                lambda d: d["verified"] is True and d["accesses"] == 80,
            ),
            (
                ["vault", "SmartwatchPhoneTabletLaptopDesktop", "--N", "91", "--p", "1009"],
                lambda d: d["verified"] is True
                and d["sha256Identical"] is True
                and d["sha256Before"] != d["sha256MidFlightScrambled"],
            ),
            (
                ["bench", "--iters", "2"],
                lambda d: d["verified"] is True and d["n91"]["adaptiveAccesses"] == 80 and d["vault"]["bytesPerSec"] > 0,
            ),
        ]:
            proc = subprocess.run(
                [node_bin, js_path, *cmd_args],
                capture_output=True,
                text=True,
                timeout=30,
                check=False,
            )
            assert proc.returncode == 0, f"CLI {cmd_args} failed: {proc.stderr}"
            parsed = json.loads(proc.stdout)
            assert check_fn(parsed), f"CLI {cmd_args} failed assertion: {parsed}"


def test_pass14_large_n_t1_horizon_and_cert_verifier() -> None:
    """Pass 14 permanent regression guard:
    1. Bracket-safe iterdir() in scripts/verify_lrat.py (no glob()) and local-server-safe sw.js (Promise.allSettled).
    2. Non-clobbering Tab 1 panels (#af-anim-panel, #af-bench-panel, #af-horizon-panel), Tab 2 sparkline,
       and independent certificate verifier UI in docs/index.html v1.4.
    3. Large-N T1 optimality (p=5 N=15751 -> 4 accesses; p=1009 N=1018082 -> 3 accesses), large-N base
       competition (N=50625=15^4 picks prog9_x15), arbitrary-BigInt Frobenius execution (2^16 mod 2, 1009^2 mod 1009),
       winner preservation in forkCandidates, computeAdaptiveHorizon, verifyCertificate, and dual positional/flag CLI.
    """
    import shutil
    import subprocess
    import tempfile

    lrat_src = (REPO / "scripts" / "verify_lrat.py").read_text(encoding="utf-8")
    assert ".glob(" not in lrat_src, "verify_lrat.py should use bracket-safe iterdir() instead of glob()"

    sw_src = (REPO / "docs" / "sw.js").read_text(encoding="utf-8")
    assert re.search(r"catalytic-adaptive-fork-v1\.[4-9]\.0", sw_src) is not None and "Promise.allSettled" in sw_src

    html = (REPO / "docs" / "index.html").read_text(encoding="utf-8")
    assert re.search(r"Adaptive Forking Offline PWA v1\.[4-9]", html) is not None
    for marker in ("af-anim-panel", "af-bench-panel", "af-horizon-panel", "af-cert-verify", "st-sparkline", "verifyLastCertificateUI"):
        assert marker in html, f"Missing Pass 14 v1.4 UI hook {marker!r} in docs/index.html"

    node_bin = shutil.which("node")
    if node_bin:
        js_path = str(REPO / "docs" / "catalytic-engine.js")
        node_check = (
            f"const E = require({json.dumps(js_path)});"
            "if (!/^1\\.[4-9]\\./.test(E.version)) process.exit(50);"
            "const r5 = E.planAdaptiveFork({N:15751, p:5, workload:'scalar'});"
            "if (!r5.comparison.adaptive_fork.feasible || r5.comparison.adaptive_fork.accesses !== '4') process.exit(51);"
            "const r1009 = E.planAdaptiveFork({N:1018082, p:1009, workload:'scalar'});"
            "if (!r1009.comparison.adaptive_fork.feasible || r1009.comparison.adaptive_fork.accesses !== '3') process.exit(52);"
            "const r15 = E.planAdaptiveFork({N:50625, p:0, workload:'scalar'});"
            "if (Number(r15.comparison.adaptive_fork.accesses) > Number(E.exactFourRegAccesses(15, 9, 50625))) process.exit(53);"
            "const e2 = E.execFourRegPowering(65536n, 1n, 2n, {engine:'adaptive'});"
            "if (!e2.verified || e2.accesses !== 2) process.exit(54);"
            "const e1009 = E.execFourRegPowering(1018081n, 7n, 1009n, {engine:'adaptive'});"
            "if (!e1009.verified || e1009.accesses !== 2) process.exit(55);"
            "const eT1 = E.execFourRegPowering(1018082n, 7n, 1009n, {engine:'adaptive'});"
            "if (!eT1.verified || eT1.accesses !== 3) process.exit(56);"
            "for (const N of [20, 91, 169, 1500, 50625]) {"
            "  const pl = E.planAdaptiveFork({N, p:1009, workload:'scalar'});"
            "  if (!pl.forkCandidates.some(c => c.status === 'winner')) process.exit(57);"
            "}"
            "const h = E.computeAdaptiveHorizon(137, {workload:'scalar'});"
            "if (!h.points || h.points.length < 10) process.exit(58);"
            "const f = E.runAdversarialFuzz(210, 20261125);"
            "if (f.failed !== 0 || f.passed !== 210) process.exit(59);"
        )
        proc = subprocess.run([node_bin, "-e", node_check], capture_output=True, text=True, timeout=30, check=False)
        assert proc.returncode == 0, f"Node.js v1.4 audit failed (rc={proc.returncode}): {proc.stderr}"

        # Test positional CLI arguments + horizon + verify round-trip
        p_pos = subprocess.run([node_bin, js_path, "plan", "169", "1009", "4", "scalar"], capture_output=True, text=True, timeout=30, check=False)
        assert p_pos.returncode == 0
        pos_data = json.loads(p_pos.stdout)
        assert pos_data["N"] == "169" and pos_data["winner"]["accesses"] == "128"

        p_hor = subprocess.run([node_bin, js_path, "horizon", "137", "scalar"], capture_output=True, text=True, timeout=30, check=False)
        assert p_hor.returncode == 0 and len(json.loads(p_hor.stdout)["points"]) >= 10

        p_vlt = subprocess.run([node_bin, js_path, "vault", "PositionalVaultCheck", "91", "1009"], capture_output=True, text=True, timeout=30, check=False)
        assert p_vlt.returncode == 0
        vlt_data = json.loads(p_vlt.stdout)
        assert vlt_data["verified"] is True and vlt_data["sha256Identical"] is True

        with tempfile.TemporaryDirectory(prefix="cert_verify_p14_") as td:
            cert_file = pathlib.Path(td) / "cert.json"
            cert_payload = {
                "kind": "catalytic_sha256_byte_vault",
                "N": "91",
                "p": "1009",
                "accessesPerChunk": vlt_data["accessesPerChunk"],
                "sha256Before": vlt_data["sha256Before"],
                "sha256After": vlt_data["sha256After"],
                "sha256Identical": True,
                "verified": True,
            }
            cert_file.write_text(json.dumps(cert_payload), encoding="utf-8", newline="\n")
            p_ver = subprocess.run([node_bin, js_path, "verify", str(cert_file)], capture_output=True, text=True, timeout=30, check=False)
            assert p_ver.returncode == 0, f"CLI verify failed: {p_ver.stderr}"
            assert json.loads(p_ver.stdout)["ok"] is True


def test_pass15_planner_executor_csp_and_autopilot() -> None:
    """Pass 15 permanent regression guard:
    1. Strict zero-exfiltration Content-Security-Policy meta tag & Adaptive Auto-Pilot / async Byte-Vault in docs/index.html v1.5.
    2. Explicit engine='prog9_x15' dispatch, 100% JSON-serializable planAdaptiveFork() (no raw BigInt leaks),
       large-N composite planner-executor base alignment (N=50625=15^4 -> internalPlan.t=9), strict hex digest
       tamper rejection in verifyCertificate(), and async chunked execCatalyticByteVaultAsync() parity.
    """
    import shutil
    import subprocess

    html = (REPO / "docs" / "index.html").read_text(encoding="utf-8")
    assert 'http-equiv="Content-Security-Policy"' in html
    assert "connect-src 'self'" in html
    assert re.search(r"Adaptive Forking Offline PWA v1\.[5-9]", html) is not None
    assert "toggleAdaptiveAutopilot" in html and "execCatalyticByteVaultAsync" in html

    sw_src = (REPO / "docs" / "sw.js").read_text(encoding="utf-8")
    assert re.search(r"catalytic-adaptive-fork-v1\.[5-9]\.0", sw_src) is not None

    node_bin = shutil.which("node")
    if node_bin:
        js_path = str(REPO / "docs" / "catalytic-engine.js")
        node_check = (
            f"const E = require({json.dumps(js_path)});"
            "(async () => {"
            "  if (!/^1\\.[5-9]\\./.test(E.version)) process.exit(60);"
            "  const r9 = E.execFourRegPowering(15, 7, 1009, {engine:'prog9_x15'});"
            "  if (!r9.verified || r9.engineUsed !== 'prog9_x15') process.exit(61);"
            "  for (const [N, p] of [[15751, 5], [1018082, 1009], [50625, 1009], [50625, 1009*1013]]) {"
            "    const pl = E.planAdaptiveFork({N, p, workload:'scalar'});"
            "    JSON.stringify(pl);"
            "  }"
            "  const plComp = E.planAdaptiveFork({N:50625n, p:1009n*1013n, workload:'scalar'});"
            "  if (!plComp.internalPlan || plComp.internalPlan.t !== 9) process.exit(62);"
            "  const bad = E.verifyCertificate({kind:'catalytic_sha256_byte_vault', N:'91', p:'1009', accessesPerChunk:80, sha256Before:'not-hex', sha256After:'not-hex', sha256Identical:true, verified:true});"
            "  if (bad.ok !== false) process.exit(63);"
            "  const raw = new TextEncoder().encode('AsyncNonBlockingCatalyticVaultTestBuffer_64B_Exact!');"
            "  let lastPct = 0;"
            "  const aRes = await E.execCatalyticByteVaultAsync(raw, 91, 7, 1009, {onProgress: (p) => { lastPct = p.pct; }});"
            "  if (!aRes.verified || !aRes.bytesEqual || lastPct !== 100) process.exit(64);"
            "})().catch((e) => { console.error(e); process.exit(65); });"
        )
        proc = subprocess.run([node_bin, "-e", node_check], capture_output=True, text=True, timeout=30, check=False)
        assert proc.returncode == 0, f"Node.js v1.5 audit failed (rc={proc.returncode}): {proc.stderr}"


def test_pass16_matrix_cor54_parity_and_cli_stream_stdin() -> None:
    """Pass 16 permanent regression guard:
    1. Exact cor:matpow prime-characteristic invertibility in planAdaptiveFork for workload='matrix':
       prog5_x7 requires 7! invertible (p > 7, so p=7 is INVALID) and prog4_x5 requires 5! invertible (p=5 INVALID),
       while p=11 is valid.
    2. Battery-safe visibilitychange pause, portable external JSON certificate file verifier (#af-cert-file),
       and transparent matrix p=11 promotion notice in docs/index.html v1.6.
    3. Node.js CLI v1.6 `stream` subcommand and `vault --stdin` raw pipe verification.
    """
    import shutil
    import subprocess

    html = (REPO / "docs" / "index.html").read_text(encoding="utf-8")
    assert re.search(r"Adaptive Forking Offline PWA v1\.[6-9]", html) is not None
    assert "visibilitychange" in html and "verifyExternalCertificateFile" in html and "af-cert-file" in html
    sw_src = (REPO / "docs" / "sw.js").read_text(encoding="utf-8")
    assert re.search(r"catalytic-adaptive-fork-v1\.[6-9]\.0", sw_src) is not None

    node_bin = shutil.which("node")
    if node_bin:
        js_path = str(REPO / "docs" / "catalytic-engine.js")
        node_check = (
            f"const E = require({json.dumps(js_path)});"
            "if (!/^1\\.[6-9]\\./.test(E.version)) process.exit(70);"
            "const m7 = E.planAdaptiveFork({workload:'matrix', N:49, p:7, matrixDim:2});"
            "if (m7.comparison.prog5_x7_T3a.validForP !== false) process.exit(71);"
            "if (m7.comparison.adaptive_fork.feasible && /prog5_x7/i.test(m7.comparison.adaptive_fork.label)) process.exit(72);"
            "const m5 = E.planAdaptiveFork({workload:'matrix', N:25, p:5, matrixDim:2});"
            "if (m5.comparison.vinciguerra_r3_x5.validForP !== false) process.exit(73);"
            "const m11 = E.planAdaptiveFork({workload:'matrix', N:49, p:11, matrixDim:2});"
            "if (!m11.comparison.prog5_x7_T3a.validForP || !m11.comparison.adaptive_fork.feasible) process.exit(74);"
            "const m7big = E.planAdaptiveFork({workload:'matrix', N:100000, p:7, matrixDim:2});"
            "if (m7big.comparison.adaptive_fork.feasible && /prog5_x7/i.test(m7big.comparison.adaptive_fork.strategy)) process.exit(75);"
        )
        proc = subprocess.run([node_bin, "-e", node_check], capture_output=True, text=True, timeout=30, check=False)
        assert proc.returncode == 0, f"Node.js v1.6 matrix audit failed (rc={proc.returncode}): {proc.stderr}"

        # Test CLI `stream` subcommand
        p_st = subprocess.run(
            [node_bin, js_path, "stream", "imu_a imu_a imu_b imu_c imu_a imu_b", "20", "1009"],
            capture_output=True, text=True, timeout=30, check=False,
        )
        assert p_st.returncode == 0, f"CLI stream failed: {p_st.stderr}"
        st_data = json.loads(p_st.stdout)
        assert st_data["verified"] is True and st_data["sumExact"] is True and st_data["allCatalystsRestored"] is True

        # Test CLI `vault --stdin` raw stdin piping
        p_in = subprocess.run(
            [node_bin, js_path, "vault", "--stdin", "91", "1009"],
            input=b"SatelliteIMU:Roll=0.02|Pitch=-0.01|CRC=OK\n",
            capture_output=True, timeout=30, check=False,
        )
        assert p_in.returncode == 0, f"CLI vault --stdin failed: {p_in.stderr.decode('utf-8', 'replace')}"
        in_data = json.loads(p_in.stdout.decode("utf-8"))
        assert in_data["verified"] is True and in_data["sha256Identical"] is True and in_data["borrowedBytes"] == 42


def test_pass17_nan_bounds_and_v17_report_preview() -> None:
    """Pass 17 permanent regression guard:
    1. All NaN / float / non-integer / out-of-range hostile inputs sanitized via safeInt across
       docs/catalytic-engine.js v1.7.0 (execT2BilinearFrobenius, execCatalyticByteVault,
       execCatalyticByteVaultAsync, runDeviceBenchmark, runAdversarialFuzz, planAdaptiveFork,
       computeAdaptiveHorizon, evalT1Oracle, execStreamingMoment, and try/catch verifyCertificate).
    2. docs/index.html v1.7 adds 1-click Watch 320px / Phone 390px Device Preview Switcher,
       visible CSP: Zero-Exfiltration badge, 1-click Export Printable Proof Report (.html),
       streaming Moment Order D <= 500 JS guard, and NaN-safe randomizeMatrix/runFuzzerLive.
    """
    import shutil
    import subprocess

    html = (REPO / "docs" / "index.html").read_text(encoding="utf-8")
    assert re.search(r"Adaptive Forking Offline PWA v1\.[7-9]", html) is not None
    assert "CSP: Zero-Exfiltration" in html
    assert "setDevicePreview" in html and "preview-watch" in html
    assert "exportProofReportHtml" in html
    assert "D > 500" in html
    assert "Math.max(11, parseInt(" not in html

    sw_src = (REPO / "docs" / "sw.js").read_text(encoding="utf-8")
    assert re.search(r"catalytic-adaptive-fork-v1\.[7-9]\.0", sw_src) is not None

    node_bin = shutil.which("node")
    if node_bin:
        js_path = str(REPO / "docs" / "catalytic-engine.js")
        node_check = (
            f"const E = require({json.dumps(js_path)});"
            "(async () => {"
            "  if (!/^1\\.[7-9]\\./.test(E.version) || typeof E.safeInt !== 'function') process.exit(80);"
            "  for (const badK of [NaN, 2.5, Infinity, -1, 'abc']) {"
            "    let okErr = false;"
            "    try { E.execT2BilinearFrobenius(badK, 87); } catch (e) { okErr = /integer/i.test(e.message); }"
            "    if (!okErr) process.exit(81);"
            "  }"
            "  const buf = new Uint8Array([1, 2, 3, 4, 5, 6]);"
            "  const v1 = E.execCatalyticByteVault(buf, 13, 7, 1009, {maxChunks: NaN});"
            "  const v2 = await E.execCatalyticByteVaultAsync(buf, 13, 7, 1009, {maxChunks: 'bad', yieldEveryMs: NaN});"
            "  if (v1.borrowedBytes !== 6 || !v1.verified || v2.borrowedBytes !== 6 || !v2.verified) process.exit(82);"
            "  const b = E.runDeviceBenchmark({iters: NaN});"
            "  if (!b.verified || !Number.isFinite(b.n91.adaptiveMs) || b.iters !== 6) process.exit(83);"
            "  const f = E.runAdversarialFuzz(NaN, NaN);"
            "  if (f.trials !== 500 || f.failed !== 0 || f.passed !== 500) process.exit(84);"
            "  const pm = E.planAdaptiveFork({workload:'matrix', N:49, p:11, matrixDim: NaN});"
            "  if (/NaN/.test(JSON.stringify(pm))) process.exit(85);"
            "  const t1 = E.evalT1Oracle(5, 25, NaN);"
            "  if (!Number.isInteger(t1.t)) process.exit(86);"
            "  let stErr = false; try { E.execStreamingMoment([1, 2], 5, 1); } catch (_) { stErr = true; }"
            "  if (!stErr) process.exit(87);"
            "  for (const badCert of [null, undefined, 'x', {}, {kind:'adaptive_fork_4reg', N:'abc', p:'1009', x:'7'}, {kind:'catalytic_sha256_byte_vault', N:'bad', p:'1009'}]) {"
            "    const r = E.verifyCertificate(badCert);"
            "    if (r.ok !== false) process.exit(88);"
            "  }"
            "})().catch((e) => { console.error(e); process.exit(89); });"
        )
        proc = subprocess.run([node_bin, "-e", node_check], capture_output=True, text=True, timeout=30, check=False)
        assert proc.returncode == 0, f"Node.js v1.7 hostile NaN/bounds audit failed (rc={proc.returncode}): {proc.stderr}"


def test_pass18_null_safety_cli_eq_selfcheck_and_v18_ui() -> None:
    """Pass 18 permanent regression guard:
    1. Null-safe opts handling across all 11 exported API functions in docs/catalytic-engine.js v1.8.0,
       strict 2x2 matrix shape validation in execMatrixLiftProg5 (preventing silent truncation),
       Array.isArray + d <= 64 guard in execT4BalancedProduct, and 12-case differential runSelfCheck().
    2. CLI --flag=value parsing (`plan --N=169 --p=1009`), `selfcheck` subcommand, `--help` exit 0,
       and unknown command non-zero exit 1.
    3. PWA v1.8 UI hooks (Visual Catalytic Byte-Diff Matrix, 1-Tap Simulate Tampered Cert, 1-Tap
       12-Proof Self-Check), sw.js v1.8.0, and manifest.webmanifest `id` + `shortcuts`.
    """
    import shutil
    import subprocess

    html = (REPO / "docs" / "index.html").read_text(encoding="utf-8")
    assert re.search(r"Adaptive Forking Offline PWA v1\.[89]", html) is not None
    for marker in ("renderByteDiffMatrix", "runSelfCheckUI", "testTamperedCertificateUI", "byte-matrix"):
        assert marker in html, f"Missing Pass 18 v1.8 UI marker {marker!r}"

    sw_src = (REPO / "docs" / "sw.js").read_text(encoding="utf-8")
    assert re.search(r"catalytic-adaptive-fork-v1\.[89]\.0", sw_src) is not None

    man = json.loads((REPO / "docs" / "manifest.webmanifest").read_text(encoding="utf-8"))
    assert man.get("id") == "./" and len(man.get("shortcuts", [])) >= 3

    node_bin = shutil.which("node")
    if node_bin:
        js_path = str(REPO / "docs" / "catalytic-engine.js")
        node_check = (
            f"const E = require({json.dumps(js_path)});"
            "(async () => {"
            "  if (!/^1\\.[89]\\./.test(E.version) || typeof E.runSelfCheck !== 'function') process.exit(90);"
            "  E.planAdaptiveFork(); E.planAdaptiveFork(null);"
            "  E.execPass3(5, 7, 1009, null);"
            "  E.execFourRegPowering(91, 7, 1009, null);"
            "  E.execStreamingMoment([1, 2], 5, 1009, null);"
            "  E.execCatalyticByteVault(new Uint8Array([1, 2, 3]), 13, 7, 1009, null);"
            "  await E.execCatalyticByteVaultAsync(new Uint8Array([1, 2, 3]), 13, 7, 1009, null);"
            "  E.execMatrixLiftProg5([[1, 2], [3, 5]], 11, null);"
            "  E.execT2BilinearFrobenius(4, 87, null, null);"
            "  E.execT4BalancedProduct([2, 3, 5, 7], null, 1, null);"
            "  E.runDeviceBenchmark(null); E.computeAdaptiveHorizon(1009, null);"
            "  for (const badM of [[[1, 2, 3], [4, 5, 6]], [[1, 2], [3, 4], [5, 6]]]) {"
            "    let rej = false; try { E.execMatrixLiftProg5(badM, 11); } catch (_) { rej = true; }"
            "    if (!rej) process.exit(91);"
            "  }"
            "  let t4Cap = false; try { E.execT4BalancedProduct(new Array(256).fill(1)); } catch (_) { t4Cap = true; }"
            "  if (!t4Cap) process.exit(92);"
            "  const sc = E.runSelfCheck();"
            "  if (!sc.ok || sc.passed < 12 || sc.passed !== sc.total) process.exit(93);"
            "})().catch((e) => { console.error(e); process.exit(94); });"
        )
        proc = subprocess.run([node_bin, "-e", node_check], capture_output=True, text=True, timeout=30, check=False)
        assert proc.returncode == 0, f"Node.js v1.8 audit failed (rc={proc.returncode}): {proc.stderr}"

        # CLI --flag=value, selfcheck, --help, and unknown command exit codes
        p_eq = subprocess.run([node_bin, js_path, "plan", "--N=169", "--p=1009"], capture_output=True, text=True, timeout=30, check=False)
        assert p_eq.returncode == 0 and json.loads(p_eq.stdout)["N"] == "169" and json.loads(p_eq.stdout)["winner"]["accesses"] == "128"

        p_sc = subprocess.run([node_bin, js_path, "selfcheck"], capture_output=True, text=True, timeout=30, check=False)
        assert p_sc.returncode == 0 and json.loads(p_sc.stdout)["ok"] is True and json.loads(p_sc.stdout)["passed"] >= 12

        p_help = subprocess.run([node_bin, js_path, "--help"], capture_output=True, text=True, timeout=30, check=False)
        assert p_help.returncode == 0 and "selfcheck" in p_help.stdout

        p_bad = subprocess.run([node_bin, js_path, "unknown_typo_cmd"], capture_output=True, text=True, timeout=30, check=False)
        assert p_bad.returncode == 1 and "Unknown command" in p_bad.stderr


def test_pass19_ci_timeouts_7kind_certs_csv_and_v19_ui() -> None:
    """Pass 19 permanent regression guard:
    1. Explicit `timeout-minutes` on every standard job across ci.yml, pages.yml, and release.yml;
       zero duplicate 'dependency dependency' phrasing in AGENTS.md.
    2. PWA v1.9 hooks: @media print stylesheet, monotonic vaultRunId async race guard, drag-and-drop
       offline file vault, Export Horizon CSV, N=1 exact-Z handling, and portable certificate emission
       across all 5 tabs (streaming_moment_t3i, matrix_lift_prog5, t2_bilinear_frobenius, t4_balanced_product).
    3. catalytic-engine.js v1.9.0: 13/13 runSelfCheck(), independent verifyCertificate() + tamper
       rejection across all 7 certificate families, horizonToCsv(), and CLI `horizon --csv`.
    """
    import shutil
    import subprocess

    for wf_name, expected_timeouts in [("ci.yml", 2), ("pages.yml", 2), ("release.yml", 1)]:
        wf_txt = (REPO / ".github" / "workflows" / wf_name).read_text(encoding="utf-8")
        assert len(re.findall(r"timeout-minutes:\s*\d+", wf_txt)) >= expected_timeouts, f"Missing timeout-minutes in {wf_name}"

    agents_txt = (REPO / "AGENTS.md").read_text(encoding="utf-8")
    assert "dependency dependency" not in agents_txt

    html = (REPO / "docs" / "index.html").read_text(encoding="utf-8")
    assert "Adaptive Forking Offline PWA v1.9" in html
    for marker in ("@media print", "vaultRunId", "exportHorizonCsv", "drag-over", "streaming_moment_t3i", "t2_bilinear_frobenius", "t4_balanced_product"):
        assert marker in html, f"Missing Pass 19 v1.9 UI marker {marker!r}"

    sw_src = (REPO / "docs" / "sw.js").read_text(encoding="utf-8")
    assert "catalytic-adaptive-fork-v1.9.0" in sw_src

    node_bin = shutil.which("node")
    if node_bin:
        js_path = str(REPO / "docs" / "catalytic-engine.js")
        node_check = (
            f"const E = require({json.dumps(js_path)});"
            "if (E.version !== '1.9.0' || typeof E.horizonToCsv !== 'function') process.exit(100);"
            "const sc = E.runSelfCheck();"
            "if (!sc.ok || sc.passed !== 13 || sc.total !== 13) process.exit(101);"
            "const st = E.execStreamingMoment([4, 2, 1], 20, 1009);"
            "const cSt = {kind:'streaming_moment_t3i', freqVec:[4,2,1], D:'20', p:'1009', requestedEngine:'adaptive', passes:st.passes, computedFD:st.computedFD, verified:true};"
            "if (!E.verifyCertificate(cSt).ok || E.verifyCertificate({...cSt, computedFD:'99999'}).ok) process.exit(102);"
            "const t2 = E.execT2BilinearFrobenius(5, 87);"
            "const cT2 = {kind:'t2_bilinear_frobenius', k:5, x:87, initial:t2.initial, expectedR0:t2.expectedR0, verified:true};"
            "if (!E.verifyCertificate(cT2).ok || E.verifyCertificate({...cT2, expectedR0:t2.expectedR0 ^ 1}).ok) process.exit(103);"
            "const t4 = E.execT4BalancedProduct([2, -3, 5, 7]);"
            "const cT4 = {kind:'t4_balanced_product', xs:['2','-3','5','7'], initial:t4.initial, sign:'1', ops:t4.ops, expectedTarget:t4.expectedTarget, verified:true};"
            "if (!E.verifyCertificate(cT4).ok || E.verifyCertificate({...cT4, expectedTarget:'0'}).ok) process.exit(104);"
            "const csv = E.horizonToCsv(E.computeAdaptiveHorizon(137));"
            "if (!csv.startsWith('N,baseline_accesses,adaptive_accesses') || csv.trim().split('\\n').length < 15) process.exit(105);"
        )
        proc = subprocess.run([node_bin, "-e", node_check], capture_output=True, text=True, timeout=30, check=False)
        assert proc.returncode == 0, f"Node.js v1.9 audit failed (rc={proc.returncode}): {proc.stderr}"

        p_csv = subprocess.run([node_bin, js_path, "horizon", "137", "scalar", "--csv"], capture_output=True, text=True, timeout=30, check=False)
        assert p_csv.returncode == 0 and p_csv.stdout.startswith("N,baseline_accesses,adaptive_accesses") and len(p_csv.stdout.strip().splitlines()) >= 15


def test_pass20_v120_standard_and_v13_playbook() -> None:
    """Pass 20 permanent regression guard verifying Build Standard v1.2.0 & Playbook v1.3 compliance:
    1. Build Standard v1.2.0: repo.yaml standard "1.2.0", URN schema $id, all 10 finding classes
       (incl. concern, gap, hole, blindspot) in .github/labels.tsv, .github/ISSUE_TEMPLATE/bug.yml,
       CONTRIBUTING.md, docs/glossary.md, and AGENTS.md; A30 blindspot grep in audit-checks.tsv;
       release.yml SLSA attestation has continue-on-error: true.
    2. Playbook v1.3: Lean 4.35 `_native` axiom guard, `--exclude-dir=.lake`, and `leanchecker --fresh`
       in ci.yml & run_all.{sh,ps1}; CITATION.cff carries Concept DOI, v1.0.1 Version DOI, and SWHID;
       paper/main.tex carries v1.0.1 Version DOI, SWHID, "Not done by AI", and withdrawal policy;
       docs/index.html surfaces Version DOI and SWHID; docs/launch/release-checklist.md has all 43 items.
    3. Adversarial negative definition check (Playbook v1.3 #12): verifies that x^3 over F_2 (s_2(3)=2 >= 2)
       is strictly uncomputable for every budget t >= 1 across both exact Python and JS evalT1Oracle.
    """
    import shutil
    import subprocess

    ten_classes = (
        "bug",
        "error",
        "issue",
        "problem",
        "concern",
        "dilemma",
        "conflict",
        "gap",
        "hole",
        "blindspot",
    )

    repo_yaml = (REPO / "repo.yaml").read_text(encoding="utf-8")
    assert 'standard: "1.2.0"' in repo_yaml

    schema = json.loads((REPO / "repo-standard.schema.json").read_text(encoding="utf-8"))
    assert schema["$id"] == "urn:0thernes:build-standard:repo-manifest-schema:1.2.0"

    tsv = (REPO / "scripts" / "audit-checks.tsv").read_text(encoding="utf-8")
    assert "Build Standard v1.2.0" in tsv
    assert "^blindspot|name: *blindspot" in tsv

    labels_txt = (REPO / ".github" / "labels.tsv").read_text(encoding="utf-8")
    bug_yml = (REPO / ".github" / "ISSUE_TEMPLATE" / "bug.yml").read_text(encoding="utf-8")
    contrib_txt = (REPO / "CONTRIBUTING.md").read_text(encoding="utf-8")
    glossary_txt = (REPO / "docs" / "glossary.md").read_text(encoding="utf-8")
    agents_txt = (REPO / "AGENTS.md").read_text(encoding="utf-8")
    for cls in ten_classes:
        assert re.search(rf"^{cls}\t", labels_txt, re.M) is not None, f"Missing label {cls!r} in .github/labels.tsv"
        assert f'"{cls}:' in bug_yml, f"Missing dropdown class {cls!r} in bug.yml"
        assert f"`{cls}`" in contrib_txt, f"Missing class {cls!r} in CONTRIBUTING.md"
        assert f"| `{cls}` |" in glossary_txt, f"Missing class {cls!r} in docs/glossary.md"
        assert cls in agents_txt, f"Missing class {cls!r} in AGENTS.md"

    ci_txt = (REPO / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")
    assert "--exclude-dir=.lake" in ci_txt
    assert "_native" in ci_txt
    assert "leanchecker --fresh Solution" in ci_txt

    rel_txt = (REPO / ".github" / "workflows" / "release.yml").read_text(encoding="utf-8")
    assert re.search(
        r"Attest build provenance \(Sigstore SLSA\)\s+continue-on-error:\s*true\s+uses:\s*actions/attest-build-provenance@v4",
        rel_txt,
    ) is not None

    for runner in ("scripts/run_all.sh", "scripts/run_all.ps1"):
        r_txt = (REPO / runner).read_text(encoding="utf-8")
        assert "_native" in r_txt, f"Missing _native axiom guard in {runner}"
        assert "leanchecker --fresh Solution" in r_txt, f"Missing leanchecker --fresh in {runner}"

    cff = (REPO / "CITATION.cff").read_text(encoding="utf-8")
    for tok in (
        "10.5281/zenodo.24517198",
        "10.5281/zenodo.24517199",
        "swh:1:snp:f960eeda6f145e54c0ac52538ace866a16e24085",
        "type: swh",
    ):
        assert tok in cff, f"Missing {tok!r} in CITATION.cff"

    tex = (REPO / "paper" / "main.tex").read_text(encoding="utf-8")
    for tok in (
        "10.5281/zenodo.24517199",
        "f960eeda6f145e54c0ac52538ace866a16e24085",
        "Not done by AI",
        "ERRATA.md",
        "withdrawal",
    ):
        assert tok in tex, f"Missing {tok!r} in paper/main.tex"

    html = (REPO / "docs" / "index.html").read_text(encoding="utf-8")
    assert "10.5281/zenodo.24517199" in html
    assert "f960eeda6f145e54c0ac52538ace866a16e24085" in html

    checklist = (REPO / "docs" / "launch" / "release-checklist.md").read_text(encoding="utf-8")
    assert "43-Item Release Checklist" in checklist
    assert "43. [ ]" in checklist
    assert "27. [x]" in checklist

    # Adversarial negative test: x^3 over F_2 (s_2(3) = 2 >= 2) must be rejected for all t
    assert sum(int(c) for c in bin(3)[2:]) >= 2
    node_bin = shutil.which("node")
    if node_bin:
        js_path = str(REPO / "docs" / "catalytic-engine.js")
        neg_js = (
            f"const E = require({json.dumps(js_path)});"
            "for (const t of [1, 2, 3, 10, 100]) {"
            "  const r = E.evalT1Oracle(2, 3, t);"
            "  if (r.feasibleAtT !== false || r.permanentlyImpossible !== true || r.digitSum !== 2 || r.minT !== null) process.exit(110);"
            "}"
        )
        proc = subprocess.run([node_bin, "-e", neg_js], capture_output=True, text=True, timeout=30, check=False)
        assert proc.returncode == 0, f"Adversarial negative T1b check failed: {proc.stderr}"


def test_pass21_deep_hardening_zenodo_figs_lean_docstrings_and_strict_axioms() -> None:
    """Pass 21 permanent regression guard (Playbook v1.3 H08/F16/H42, Build Standard v1.2.0 RC19/RC23,
    and residual 2026-11-26 statement-audit metadata/figure/PWA/Lean-docstring cleanup):
    1. `.zenodo.json` & `pyproject.toml` carry the corrected title/description (no 'Optimal', no
       'answering open questions') and `.zenodo.json` records Concept DOI, Version DOI, and SWHID.
    2. `scripts/make_figures.py` and `docs/catalytic-engine.js` contain no 'Global optimum' or
       'Global Optimal Engine' overclaims; `ROADMAP.md` cites Build Standard v1.2.0 and Boyar-Find
       open question; `LIMITATIONS.md` lists all 10 v1.2.0 finding classes.
    3. `ci.yml`, `run_all.sh`, and `run_all.ps1` enforce modifier-aware `axiom` scanning (`H08`)
       and non-empty strict 3-axiom allowlist validation (`F16`/`H01`); `release.yml` & `AGENTS.md`
       note report-only checks (`RC19`) and public-repo attestations (`RC23`); `release-checklist.md`
       and `legal-and-ethics.md` document transcript redaction (`H42`).
    4. Lean docstrings in `Challenge.lean`, `PalomarChallenge.lean`, `DigitSumDichotomy.lean`,
       `ThreeRegisterBreakthrough.lean`, and `FourRegisterPowering.lean` have zero overclaiming
       phrases ('optimal 3-register', 'Optimal `prog8_x13`', 'achieving optimal exponent',
       'fail completely') while preserving exact 1-for-1 line counts (PalomarChallenge = 283 lines).
    """
    zen = json.loads((REPO / ".zenodo.json").read_text(encoding="utf-8"))
    assert "Optimal" not in zen["title"]
    assert "answering open questions" not in zen["description"]
    assert "no question posed there is resolved" in zen["description"]
    assert "10.5281/zenodo.24517199" in zen["notes"]
    assert "swh:1:snp:f960eeda6f145e54c0ac52538ace866a16e24085" in zen["notes"]

    pyproj = (REPO / "pyproject.toml").read_text(encoding="utf-8")
    assert "optimal 3-register" not in pyproj.lower()

    fig_src = (REPO / "scripts" / "make_figures.py").read_text(encoding="utf-8")
    assert "Global optimum" not in fig_src
    assert "Family min" in fig_src

    js_src = (REPO / "docs" / "catalytic-engine.js").read_text(encoding="utf-8")
    assert "Global Optimal Engine" not in js_src
    assert "Best Constructed Engine (t=8 -> x^13, T3d)" in js_src

    roadmap = (REPO / "ROADMAP.md").read_text(encoding="utf-8")
    assert "Build Standard v1.2.0" in roadmap
    assert "Boyar–Find conjecture" not in roadmap

    lim = (REPO / "LIMITATIONS.md").read_text(encoding="utf-8")
    for cls in ("concern", "gap", "hole", "blindspot"):
        assert cls in lim, f"Missing v1.2.0 class {cls!r} in LIMITATIONS.md"

    ci_txt = (REPO / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")
    assert "noncomputable\\s+)*axiom\\b" in ci_txt
    assert "test -s /tmp/axioms.txt" in ci_txt
    assert "Strict 3-axiom allowlist verified" in ci_txt

    sh_txt = (REPO / "scripts" / "run_all.sh").read_text(encoding="utf-8")
    assert "noncomputable\\s+)*axiom\\b" in sh_txt
    assert 'test -s "$TMP_AX"' in sh_txt
    assert "Strict 3-axiom allowlist verified" in sh_txt

    ps_txt = (REPO / "scripts" / "run_all.ps1").read_text(encoding="utf-8")
    assert "EMPTY VerifyAxioms.lean OUTPUT!" in ps_txt
    assert "Strict 3-axiom allowlist verified" in ps_txt

    rel_txt = (REPO / ".github" / "workflows" / "release.yml").read_text(encoding="utf-8")
    assert "public repositories" in rel_txt
    agents_txt = (REPO / "AGENTS.md").read_text(encoding="utf-8")
    assert "report-only" in agents_txt and "public repositories" in agents_txt

    checklist = (REPO / "docs" / "launch" / "release-checklist.md").read_text(encoding="utf-8")
    legal = (REPO / "docs" / "legal-and-ethics.md").read_text(encoding="utf-8")
    assert "scrubbed" in checklist and "scrubbed" in legal

    lean_checks = [
        ("lean/Challenge.lean", 246),
        ("lean/PalomarChallenge.lean", 283),
        ("lean/Catalytic/DigitSumDichotomy.lean", 1025),
        ("lean/Catalytic/ThreeRegisterBreakthrough.lean", 659),
        ("lean/Catalytic/FourRegisterPowering.lean", 1364),
    ]
    bad_lean_phrases = (
        "optimal 3-register",
        "Optimal `prog8_x13`",
        "achieving optimal exponent",
        "optimal exponent!",
        "fail completely",
    )
    for rel_path, expected_lines in lean_checks:
        txt = (REPO / rel_path).read_text(encoding="utf-8")
        assert len(txt.splitlines()) == expected_lines, f"Line-count drift in {rel_path}"
        for phrase in bad_lean_phrases:
            assert phrase not in txt, f"Overclaiming docstring {phrase!r} remained in {rel_path}"

