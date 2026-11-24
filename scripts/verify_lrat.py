# SPDX-License-Identifier: Apache-2.0
"""
Standalone exact ASCII LRAT (Linear Resolution Asymmetric Tautology) UNSAT proof
verifier for archived CaDiCaL 2.1.2 certificates in ``results/sat_certs/``.

Checks every addition (RUP or RAT) and deletion step against the original DIMACS
CNF clauses and verifies derivation of the empty clause (contradiction).

Note on trust base: this script is an independent Python reference verifier
written to audit archived SAT certificates locally alongside tests/test_all.py.
For maximum formal assurance in external CI, CakeML's formally verified
``cake_lpr`` binary can replay the exact same ``.cnf`` and ``.lrat`` files.
No Tier-1 Lean theorem in this repository depends on SAT solving.
"""

from __future__ import annotations

import pathlib
import sys


def parse_dimacs_cnf(cnf_path: pathlib.Path) -> tuple[int, dict[int, list[int]]]:
    """Parse a DIMACS CNF file into (num_vars, {1-based clause_id: [literals]})."""
    num_vars = 0
    expected_clauses: int | None = None
    clauses: dict[int, list[int]] = {}
    current: list[int] = []
    clause_id = 0

    for raw in cnf_path.read_text(encoding="ascii").splitlines():
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p "):
            parts = line.split()
            if len(parts) < 4 or parts[1] != "cnf":
                raise ValueError(f"Malformed DIMACS header: {line}")
            num_vars = int(parts[2])
            expected_clauses = int(parts[3])
            continue
        for tok in line.split():
            lit = int(tok)
            if lit == 0:
                clause_id += 1
                clauses[clause_id] = current
                current = []
            else:
                if abs(lit) > num_vars and num_vars > 0:
                    raise ValueError(f"Literal {lit} exceeds declared num_vars={num_vars}")
                current.append(lit)

    if current:
        raise ValueError("Unterminated clause at end of DIMACS CNF file")
    if expected_clauses is not None and len(clauses) != expected_clauses:
        raise ValueError(
            f"Clause count mismatch: header declared {expected_clauses}, parsed {len(clauses)}"
        )
    return num_vars, clauses


def _check_rup_chain(
    clauses: dict[int, list[int]],
    assumed_false: set[int],
    hints: list[int],
    step_id: int,
) -> bool:
    """
    Propagate unit clauses along ``hints`` starting from the partial assignment
    where every literal in ``assumed_false`` is False (and its negation is True).
    Returns True iff a falsified clause (conflict) is reached.
    """
    false_lits = set(assumed_false)
    for hid in hints:
        if hid <= 0:
            raise ValueError(f"Step {step_id}: expected positive RUP hint, got {hid}")
        if hid not in clauses:
            raise ValueError(f"Step {step_id}: hint references unknown/deleted clause {hid}")
        clause = clauses[hid]
        unassigned: list[int] = []
        satisfied = False
        for lit in clause:
            if -lit in false_lits:
                satisfied = True
                break
            if lit not in false_lits:
                unassigned.append(lit)
        if satisfied:
            raise ValueError(f"Step {step_id}: hint clause {hid} is already satisfied")
        if not unassigned:
            return True
        if len(unassigned) > 1:
            raise ValueError(
                f"Step {step_id}: hint clause {hid} is not unit (unassigned={unassigned})"
            )
        # Unit literal u must be True -> -u is False
        false_lits.add(-unassigned[0])
    return False


def verify_lrat(cnf_path: pathlib.Path, lrat_path: pathlib.Path) -> tuple[int, int]:
    """
    Verify an ASCII LRAT proof against a DIMACS CNF file.

    Returns ``(derived_steps, deleted_clauses)`` on success; raises ``ValueError``
    on any invalid proof step or if the empty clause is never derived.
    """
    _, clauses = parse_dimacs_cnf(cnf_path)
    max_clause_id = max(clauses.keys(), default=0)
    derived_steps = 0
    deleted_clauses = 0
    derived_empty = False

    for line_no, raw in enumerate(lrat_path.read_text(encoding="ascii").splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        tokens = line.split()
        if len(tokens) < 2:
            raise ValueError(f"Line {line_no}: malformed LRAT line: {line}")
        step_id = int(tokens[0])

        if tokens[1] == "d":
            if tokens[-1] != "0":
                raise ValueError(f"Line {line_no}: deletion line missing terminating 0")
            for tok in tokens[2:-1]:
                cid = int(tok)
                if cid not in clauses:
                    raise ValueError(
                        f"Line {line_no}: cannot delete unknown/already-deleted clause {cid}"
                    )
                del clauses[cid]
                deleted_clauses += 1
            continue

        ints = [int(t) for t in tokens[1:]]
        try:
            first_zero = ints.index(0)
        except ValueError as exc:
            raise ValueError(f"Line {line_no}: missing literal terminator 0") from exc
        new_clause = ints[:first_zero]
        rest = ints[first_zero + 1 :]
        if not rest or rest[-1] != 0:
            raise ValueError(f"Line {line_no}: missing hint terminator 0")
        hints = rest[:-1]

        if step_id <= max_clause_id or step_id in clauses:
            raise ValueError(
                f"Line {line_no}: non-monotonic or duplicate clause id {step_id} (max_id={max_clause_id})"
            )

        # Split hints into initial positive RUP chain and optional RAT blocks (negative IDs)
        neg_positions = [i for i, h in enumerate(hints) if h < 0]
        if not neg_positions:
            assumed_false = set(new_clause)
            # Check for tautology (contradictory assumed literals)
            is_taut = any(-lit in assumed_false for lit in assumed_false)
            if not is_taut and not _check_rup_chain(clauses, assumed_false, hints, step_id):
                raise ValueError(f"Line {line_no} (step {step_id}): RUP check failed to conflict")
        else:
            if not new_clause:
                raise ValueError(f"Line {line_no} (step {step_id}): empty clause cannot use RAT")
            pivot = new_clause[0]
            rup_prefix = hints[: neg_positions[0]]
            base_false = set(new_clause)
            # Propagate RUP prefix first
            rup_false = set(base_false)
            prefix_conflict = False
            for hid in rup_prefix:
                if hid <= 0:
                    raise ValueError(f"Step {step_id}: expected positive RUP-prefix hint, got {hid}")
                if hid not in clauses:
                    raise ValueError(f"Step {step_id}: unknown RUP-prefix hint {hid}")
                cl = clauses[hid]
                unassigned = []
                sat = False
                for lit in cl:
                    if -lit in rup_false:
                        sat = True
                        break
                    if lit not in rup_false:
                        unassigned.append(lit)
                if sat:
                    raise ValueError(f"Step {step_id}: satisfied clause {hid} in RAT prefix")
                if not unassigned:
                    prefix_conflict = True
                    break
                if len(unassigned) > 1:
                    raise ValueError(f"Step {step_id}: non-unit clause {hid} in RAT prefix")
                rup_false.add(-unassigned[0])

            if not prefix_conflict:
                # Every active clause containing -pivot must be covered by a negative hint
                rat_map: dict[int, list[int]] = {}
                for idx_i, pos in enumerate(neg_positions):
                    target_id = -hints[pos]
                    end_pos = (
                        neg_positions[idx_i + 1] if idx_i + 1 < len(neg_positions) else len(hints)
                    )
                    rat_map[target_id] = hints[pos + 1 : end_pos]

                for cid, cl in clauses.items():
                    if -pivot not in cl:
                        continue
                    if cid not in rat_map:
                        raise ValueError(
                            f"Step {step_id}: RAT missing resolvent hint for clause {cid}"
                        )
                    res_false = set(rup_false)
                    taut = False
                    for lit in cl:
                        if lit == -pivot:
                            continue
                        if -lit in res_false:
                            taut = True
                            break
                        res_false.add(lit)
                    if taut:
                        continue
                    if not _check_rup_chain(clauses, res_false, rat_map[cid], step_id):
                        raise ValueError(
                            f"Step {step_id}: RAT resolvent with clause {cid} failed to conflict"
                        )

        clauses[step_id] = new_clause
        max_clause_id = step_id
        derived_steps += 1
        if not new_clause:
            derived_empty = True
            break

    if not derived_empty:
        raise ValueError(f"LRAT proof {lrat_path.name} never derived the empty clause")
    return derived_steps, deleted_clauses


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parent.parent
    cert_dir = repo / "results" / "sat_certs"
    if len(sys.argv) == 3:
        cnf_p = pathlib.Path(sys.argv[1])
        lrat_p = pathlib.Path(sys.argv[2])
        steps, dels = verify_lrat(cnf_p, lrat_p)
        print(f"VERIFIED LRAT: {cnf_p.name} + {lrat_p.name} ({steps} steps, {dels} deletions)")
        return

    if not cert_dir.exists():
        print(f"No certificate directory found at {cert_dir}", file=sys.stderr)
        sys.exit(1)

    pairs = sorted(cert_dir.glob("*.cnf"))
    if not pairs:
        print(f"No .cnf certificates found in {cert_dir}", file=sys.stderr)
        sys.exit(1)

    for cnf_p in pairs:
        lrat_p = cnf_p.with_suffix(".lrat")
        if not lrat_p.exists():
            print(f"MISSING LRAT proof for {cnf_p.name}", file=sys.stderr)
            sys.exit(1)
        steps, dels = verify_lrat(cnf_p, lrat_p)
        print(f"[PASS] {cnf_p.name} + {lrat_p.name}: {steps} derived steps, {dels} deletions -> UNSAT verified")


if __name__ == "__main__":
    main()
