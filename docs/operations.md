<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Operations, Backups & Offsite Mirror (`docs/operations.md`)

## Offsite Repository Mirror & Cold Backup (Build Standard A35)

Maintain an offsite copy independent of GitHub so the commit history, Lean proofs, and frozen release artifacts survive any single host outage:

```bash
# Option 1: Push a full mirror to a secondary Git host (e.g., Codeberg or GitLab)
git remote add backup https://codeberg.org/0thernes/catalytic-register-frontiers.git
git push backup --mirror

# Option 2: Create a self-contained, verifiable offline git bundle on separate storage
git bundle create ../catalytic-register-frontiers-$(date +%Y%m%d).bundle --all
git bundle verify ../catalytic-register-frontiers-$(date +%Y%m%d).bundle
```

- **Local canonical workspace:** `Z:\[Vibe Coded (AI)]\ANTIGRAVITY\catalytic-register-frontiers` (dedicated ReFS Dev Drive).
- **Planned archival mirrors:** GitHub (`0thernes/catalytic-register-frontiers`), Software Heritage (`archive.softwareheritage.org/save`, ISO/IEC 18670 SWHID), and master research archive (`0thernes-research-archive`).
- **Last local bundle/audit refresh:** 2026-11-23.

## Deployment & Rollback

Not deployed as a live network service (`deployed: false`, `service: false` in `repo.yaml`). Static documentation Pages deployment (`.github/workflows/pages.yml`) is rebuilt deterministically from `main`; rolling back is `git revert <sha> && git push origin main`.

## Persistent Data & Backups

Stores no user data or runtime databases (`personal_data: false`). All scientific artifacts (`results/*.json`, `paper/figures/*.pdf`, `dist/*`) are deterministically regenerable from source via `just reproduce` and integrity-checked via `MANIFEST.sha256`.
