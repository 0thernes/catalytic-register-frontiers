# SPDX-License-Identifier: Apache-2.0
"""Citation hygiene and live DOI/arXiv resolution verifier for paper/references.bib.

Offline mode (default in CI/pytest) checks that every BibTeX entry has required fields,
well-formed DOIs/arXiv IDs, and matches the audited bibliography without duplicates.
Online mode (--online) queries Crossref, DataCite/doi.org, and the arXiv API to confirm
HTTP 200 resolution and zero retractions.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIB_PATH = ROOT / "paper" / "references.bib"


def parse_bib_entries(text: str) -> list[dict[str, str]]:
    entries: list[dict[str, str]] = []
    chunks = re.split(r"\n(?=@\w+\{)", text.strip())
    for chunk in chunks:
        m = re.match(r"@(\w+)\{([^,]+),", chunk.strip())
        if not m:
            continue
        entry: dict[str, str] = {"type": m.group(1), "key": m.group(2).strip()}
        for fm in re.finditer(r"^\s*(\w+)\s*=\s*\{(.*)\},?\s*$", chunk, re.M):
            entry[fm.group(1).lower()] = fm.group(2).strip()
        entries.append(entry)
    return entries


def check_offline(bib_path: Path) -> tuple[list[dict[str, str]], list[str]]:
    text = bib_path.read_text(encoding="utf-8")
    entries = parse_bib_entries(text)
    errors: list[str] = []
    seen_keys: set[str] = set()
    for e in entries:
        key = e["key"]
        if key in seen_keys:
            errors.append(f"Duplicate BibTeX key: {key}")
        seen_keys.add(key)
        for req in ("author", "title", "year"):
            if req not in e or not e[req]:
                errors.append(f"{key}: missing required field '{req}'")
        if e.get("year") and not re.fullmatch(r"\d{4}", e["year"]):
            errors.append(f"{key}: malformed publication year '{e['year']}'")
        doi_val = e.get("doi")
        if doi_val is not None:
            if not re.fullmatch(r"10\.\d{4,9}/\S+", doi_val):
                errors.append(f"{key}: malformed DOI '{doi_val}'")
        has_arxiv = bool(re.search(r"https://arxiv\.org/abs/\d{4}\.\d{4,5}", str(e)))
        if not doi_val and not has_arxiv:
            errors.append(f"{key}: missing valid DOI or arXiv URL identifier")
    if len(entries) < 8:
        errors.append(f"Expected >= 8 bibliography entries, found {len(entries)}")
    tex_path = bib_path.parent / "main.tex"
    if tex_path.exists():
        tex_txt = tex_path.read_text(encoding="utf-8")
        cited: set[str] = set()
        for grp in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}", tex_txt):
            for k in grp.split(","):
                k_clean = k.strip()
                if k_clean:
                    cited.add(k_clean)
        for missing in sorted(cited - seen_keys):
            errors.append(f"Citation key '\\cite{{{missing}}}' in {tex_path.name} not defined in {bib_path.name}")
        for uncited in sorted(seen_keys - cited):
            errors.append(f"BibTeX key '{uncited}' in {bib_path.name} is never cited in {tex_path.name}")
    return entries, errors


def check_online(entries: list[dict[str, str]]) -> list[str]:
    errors: list[str] = []
    ver_file = ROOT / "VERSION"
    ver = ver_file.read_text(encoding="utf-8").strip() if ver_file.exists() else "1.0.1"
    headers = {"User-Agent": f"catalytic-register-frontiers/{ver} (mailto:0_0@0thernes.art)"}
    for e in entries:
        key = e["key"]
        doi = e.get("doi")
        if doi:
            if doi.startswith("10.4230/"):
                url = f"https://doi.org/{doi}"
                try:
                    req = urllib.request.Request(url, headers=headers)
                    with urllib.request.urlopen(req, timeout=15) as r:
                        if r.status != 200:
                            errors.append(f"{key}: DOI {doi} returned HTTP {r.status}")
                except Exception as exc:
                    errors.append(f"{key}: DOI {doi} error: {exc}")
            else:
                url = f"https://api.crossref.org/works/{doi}"
                try:
                    req = urllib.request.Request(url, headers=headers)
                    with urllib.request.urlopen(req, timeout=15) as r:
                        msg = json.loads(r.read().decode("utf-8"))["message"]
                        if msg.get("update-to"):
                            errors.append(f"{key}: Crossref update/retraction notice present: {msg['update-to']}")
                        rel_retract = (msg.get("relation") or {}).get("is-retracted-by")
                        if rel_retract:
                            errors.append(f"{key}: Crossref is-retracted-by notice present: {rel_retract}")
                except Exception as exc:
                    errors.append(f"{key}: Crossref check failed for {doi}: {exc}")
        for arx in re.findall(r"https://arxiv\.org/abs/([0-9]+\.[0-9]+)", str(e)):
            url = f"https://arxiv.org/abs/{arx}"
            try:
                req = urllib.request.Request(url, headers=headers)
                with urllib.request.urlopen(req, timeout=15) as r:
                    if r.status != 200:
                        errors.append(f"{key}: arXiv {arx} returned HTTP {r.status}")
            except Exception as exc:
                errors.append(f"{key}: arXiv {arx} error: {exc}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description="Verify paper/references.bib integrity.")
    parser.add_argument("--online", action="store_true", help="Also verify live DOI/arXiv resolution via HTTP.")
    parser.add_argument("--offline", action="store_true", help="Run offline structural checks only (default).")
    args = parser.parse_args()

    entries, errors = check_offline(BIB_PATH)
    if args.online:
        errors.extend(check_online(entries))
    if errors:
        for err in errors:
            print(f"ERROR: {err}", file=sys.stderr)
        return 1
    mode = "offline+online" if args.online else "offline"
    print(f"Citation check PASS ({mode}): {len(entries)} entries verified cleanly.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
