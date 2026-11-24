# SPDX-License-Identifier: Apache-2.0
"""
Standalone REUSE 3.3 / SPDX license coverage verifier for catalytic-register-frontiers.

Parses ``REUSE.toml`` using Python 3.11+ stdlib ``tomllib`` and verifies that EVERY
git-tracked repository file has an allowlisted SPDX license identifier either via an
inline ``SPDX-License-Identifier:`` header or an explicit ``REUSE.toml`` annotation.
Bracket-safe on Windows paths via ``os.walk`` / ``PurePosixPath``.
"""

from __future__ import annotations

import fnmatch
import os
import pathlib
import re
import subprocess
import sys
import tomllib

ALLOWED_SPDX = {"Apache-2.0", "CC-BY-4.0", "CC0-1.0"}
INLINE_RE = re.compile(r"SPDX-License-Identifier:\s*([A-Za-z0-9.\-+]+)")


def _matches_reuse_glob(rel_posix: str, pattern: str) -> bool:
    """Match REUSE.toml glob patterns including recursive ``dir/**``."""
    if pattern.endswith("/**"):
        prefix = pattern[:-3]
        return rel_posix.startswith(prefix + "/")
    if "/" not in pattern:
        return "/" not in rel_posix and fnmatch.fnmatchcase(rel_posix, pattern)
    return fnmatch.fnmatchcase(rel_posix, pattern)


def _list_repo_files(repo: pathlib.Path) -> list[str]:
    if (repo / ".git").exists():
        out = subprocess.check_output(
            ["git", "-C", str(repo), "ls-files"],
            text=True,
            encoding="utf-8",
        )
        return sorted(line.strip() for line in out.splitlines() if line.strip())
    skip_dirs = {
        ".git",
        ".venv",
        ".lake",
        "__pycache__",
        ".pytest_cache",
        ".mypy_cache",
        ".ruff_cache",
        ".hypothesis",
    }
    found: list[str] = []
    for root, dirs, files in os.walk(repo):
        dirs[:] = [d for d in dirs if d not in skip_dirs]
        for fn in files:
            rel = pathlib.Path(root, fn).relative_to(repo).as_posix()
            if rel.startswith("paper/build/"):
                continue
            found.append(rel)
    return sorted(found)


def verify_reuse(repo: pathlib.Path) -> tuple[int, int, list[str]]:
    """
    Audit REUSE 3.3 / SPDX coverage across all tracked files in ``repo``.
    Returns ``(total_files, inline_spdx_count, errors)``.
    """
    reuse_toml = repo / "REUSE.toml"
    if not reuse_toml.exists():
        return 0, 0, ["Missing REUSE.toml at repository root"]

    cfg = tomllib.loads(reuse_toml.read_text(encoding="utf-8"))
    annotations: list[tuple[list[str], str]] = []
    errors: list[str] = []

    for ann in cfg.get("annotations", []):
        spdx = str(ann.get("SPDX-License-Identifier", "")).strip()
        paths = ann.get("path", [])
        if isinstance(paths, str):
            paths = [paths]
        if spdx not in ALLOWED_SPDX:
            errors.append(f"REUSE.toml contains non-allowlisted license: {spdx}")
        annotations.append(([str(p) for p in paths], spdx))

    files = _list_repo_files(repo)
    inline_count = 0
    for rel in files:
        p = repo / rel
        inline_lic: str | None = None
        if p.exists() and p.suffix.lower() not in {
            ".pdf",
            ".gz",
            ".png",
            ".jpg",
            ".tsq",
            ".tsr",
            ".ots",
        }:
            try:
                head = p.read_text(encoding="utf-8", errors="ignore")[:800]
                m = INLINE_RE.search(head)
                if m:
                    inline_lic = m.group(1)
                    inline_count += 1
                    if inline_lic not in ALLOWED_SPDX:
                        errors.append(f"{rel}: non-allowlisted inline SPDX '{inline_lic}'")
            except OSError:
                pass

        toml_lics = [
            spdx
            for patterns, spdx in annotations
            if any(_matches_reuse_glob(rel, pat) for pat in patterns)
        ]
        if inline_lic is None and not toml_lics:
            errors.append(f"{rel}: missing both inline SPDX header and REUSE.toml annotation")

    return len(files), inline_count, errors


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parent.parent
    total, inline_n, errors = verify_reuse(repo)
    if errors:
        print(f"REUSE/SPDX AUDIT FAILED ({len(errors)} issues):", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        sys.exit(1)
    print(
        f"REUSE_SPDX_VERIFIED: {total}/{total} tracked files covered "
        f"({inline_n} inline SPDX headers + REUSE.toml)."
    )


if __name__ == "__main__":
    main()
