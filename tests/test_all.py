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
    """Negative & regression guard (B06, B07): zero forbidden tokens, all 13 Lean files use
    `module`, axioms strictly within the 3 standard Lean axioms, and citations verified."""
    lean_dir = REPO / "lean"
    pat = re.compile(r"\b(sorry|admit|native_decide|implemented_by|unsafe)\b|^\s*axiom\b|@\[extern", re.M)
    lean_files: list[pathlib.Path] = []
    for root, dirs, fnames in os.walk(lean_dir):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for fn in sorted(fnames):
            if fn.endswith(".lean"):
                lean_files.append(pathlib.Path(root) / fn)
    assert len(lean_files) == 13
    for f in lean_files:
        text = f.read_text(encoding="utf-8")
        assert text.lstrip().startswith("module"), f"Missing Lean 4.35 `module` header in {f}"
        assert not pat.search(text), f"Forbidden token found in {f}"

    # Verify Palomar, comparator, soundness bridge, and extension-field separation artifacts exist
    assert (lean_dir / "comparator.json").exists()
    assert (lean_dir / "formalization.yaml").exists()
    assert (lean_dir / "Catalytic" / "NonVacuity.lean").exists()
    assert (lean_dir / "Catalytic" / "ExtensionFieldSeparation.lean").exists()
    assert (lean_dir / "Catalytic" / "Pass2Soundness.lean").exists()

    # Verify results/lean_axioms.txt covers all 20 declarations with zero unpermitted axioms
    ax_lines = (REPO / "results" / "lean_axioms.txt").read_text(encoding="utf-8").strip().splitlines()
    assert len(ax_lines) == 20
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


def test_t3f_global_integer_optimality_exact() -> None:
    """Independent exact integer verification of T3f rational separator 30/37 for t=4..500."""
    assert 8**37 < 13**30
    for t in range(4, 501):
        if t == 8:
            assert (2 * t - 3) ** 30 > t**37
        else:
            assert (2 * t - 3) ** 30 < t**37


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
    assert f'version: "{version}"' in (REPO / "lean" / "formalization.yaml").read_text(encoding="utf-8")

    # Validate JSON artifacts parse cleanly with required keys
    sbom = json.loads((REPO / "sbom.cdx.json").read_text(encoding="utf-8"))
    assert sbom.get("bomFormat") == "CycloneDX" and sbom.get("specVersion") == "1.5"
    assert isinstance(sbom.get("components"), list) and len(sbom["components"]) >= 5

    zen = json.loads((REPO / ".zenodo.json").read_text(encoding="utf-8"))
    assert "title" in zen and "creators" in zen and zen["creators"][0].get("orcid") == "0009-0006-8168-9648"

    comp = json.loads((REPO / "lean" / "comparator.json").read_text(encoding="utf-8"))
    assert comp.get("challenge_module") == "Challenge" and comp.get("solution_module") == "Solution"

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
    """Pass 5 anti-staleness and cross-artifact consistency guard:
    - All BibTeX entries are cited in paper/main.tex, zero undefined refs, all 3 figures cited.
    - arXiv metadata abstract obeys the 1,920-character arXiv submission limit.
    - No stale theorem/module/line counts in active canonical docs.
    - All local blueprint links in docs/index.html match files deployed by pages.yml.
    - CI and POSIX runner invoke con-leche/con-ron inside `lake env`.
    """
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
    stale_tokens = ("longest file 1{,}026", "12 headline theorems", "12 exported theorems", "14/14 decls")
    for rel in (
        "paper/main.tex",
        "paper/arxiv_metadata.txt",
        "README.md",
        "AGENTS.md",
        "llms.txt",
        "repo.yaml",
        "docs/index.html",
        "docs/plan/02-requirements.md",
        "docs/plan/slices.md",
    ):
        txt = (REPO / rel).read_text(encoding="utf-8")
        for tok in stale_tokens:
            assert tok not in txt, f"Stale token {tok!r} found in {rel}"

    # Verify docs/index.html blueprint hrefs are all copied by .github/workflows/pages.yml
    html = (REPO / "docs" / "index.html").read_text(encoding="utf-8")
    pages = (REPO / ".github" / "workflows" / "pages.yml").read_text(encoding="utf-8")
    for href in re.findall(r'href="(blueprint/[^"]+)"', html):
        assert f"_site/{href}" in pages, f"Broken Pages blueprint link {href} not copied in pages.yml"

    # Verify CI and POSIX runner invoke con-leche/con-ron via `lake env`
    ci_yml = (REPO / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")
    run_sh = (REPO / "scripts" / "run_all.sh").read_text(encoding="utf-8")
    assert "lake env con-leche --verified" in ci_yml and "lake env con-ron --verified" in ci_yml
    assert "lake env con-leche --verified" in run_sh and "lake env con-ron --verified" in run_sh



