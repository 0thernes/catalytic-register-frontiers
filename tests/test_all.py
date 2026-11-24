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
    """Negative & regression guard (B06, B07): zero forbidden tokens, all 11 Lean files use
    `module`, axioms strictly within the 3 standard Lean axioms, and citations verified."""
    lean_dir = REPO / "lean"
    pat = re.compile(r"\b(sorry|admit|native_decide|implemented_by|unsafe)\b|^\s*axiom\b|@\[extern", re.M)
    lean_files: list[pathlib.Path] = []
    for root, dirs, fnames in os.walk(lean_dir):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for fn in sorted(fnames):
            if fn.endswith(".lean"):
                lean_files.append(pathlib.Path(root) / fn)
    assert len(lean_files) == 11
    for f in lean_files:
        text = f.read_text(encoding="utf-8")
        assert text.lstrip().startswith("module"), f"Missing Lean 4.35 `module` header in {f}"
        assert not pat.search(text), f"Forbidden token found in {f}"

    # Verify Palomar & comparator artifacts exist
    assert (lean_dir / "comparator.json").exists()
    assert (lean_dir / "formalization.yaml").exists()
    assert (lean_dir / "Catalytic" / "NonVacuity.lean").exists()

    # Verify results/lean_axioms.txt covers all 14 declarations with zero unpermitted axioms
    ax_lines = (REPO / "results" / "lean_axioms.txt").read_text(encoding="utf-8").strip().splitlines()
    assert len(ax_lines) == 14
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
    """Verify archived CaDiCaL 2.1.2 LRAT UNSAT certificates and confirm mutant rejection."""
    cert_dir = REPO / "results" / "sat_certs"
    for stem in ("f4_mul_k2", "orthogonal_bent_pair_k2"):
        cnf_p = cert_dir / f"{stem}.cnf"
        lrat_p = cert_dir / f"{stem}.lrat"
        assert cnf_p.exists() and lrat_p.exists(), f"Missing SAT certificate pair for {stem}"
        steps, deletions = verify_lrat(cnf_p, lrat_p)
        assert steps > 1000 and deletions > 100

    # Mutant 1: truncate the final empty-clause derivation line -> must raise ValueError
    orig_cnf = cert_dir / "f4_mul_k2.cnf"
    orig_lines = (cert_dir / "f4_mul_k2.lrat").read_text(encoding="ascii").splitlines()
    trunc_lrat = tmp_path / "truncated.lrat"
    trunc_lrat.write_text("\n".join(orig_lines[:-1]) + "\n", encoding="ascii")
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
    bad_hint_lrat.write_text("\n".join(corrupted) + "\n", encoding="ascii")
    raised = False
    try:
        verify_lrat(orig_cnf, bad_hint_lrat)
    except ValueError:
        raised = True
    assert raised, "LRAT verifier failed to reject corrupted RUP hint!"


def test_manifest_and_reuse_hygiene() -> None:
    """Guard against cache files leaking into MANIFEST.sha256 and confirm REUSE.toml + SPDX."""
    assert (REPO / "REUSE.toml").exists()
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

