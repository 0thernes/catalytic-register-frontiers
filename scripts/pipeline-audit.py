#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Report which Build Pipeline Models artifacts exist. Report-only: always exits 0 (R1, R3).
Bracket-safe on Windows paths containing `[` / `]` via glob.escape(root).
"""

from __future__ import annotations

import csv
import glob
import os
import sys

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
tsv = os.path.join(root, "scripts", "pipeline-checks.tsv")
seen: dict[str, list[tuple[bool, str]]] = {}

with open(tsv, encoding="utf-8") as f:
    for r in csv.DictReader(f, delimiter="\t"):
        rel_pat = r["path"].replace("YYYY-MM-DD-title", "*").replace("YYYY-MM", "*")
        literal_path = os.path.join(root, rel_pat)
        if "*" in rel_pat:
            glob_pat = os.path.join(glob.escape(root), rel_pat)
            ok = bool(glob.glob(glob_pat))
        else:
            ok = os.path.exists(literal_path)
        seen.setdefault(r["phase_id"], []).append((ok, r["path"]))

for ph, items in seen.items():
    have = sum(o for o, _ in items)
    print(f"{ph}: {have}/{len(items)} artifacts present")
    for o, p in items:
        if not o:
            print(f"   missing (issue): {p}")
sys.exit(0)
