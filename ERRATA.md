<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Errata (`ERRATA.md`)

Append-only log of mathematical, formalization, bibliographic, or computational errors discovered after initial freezing.

| Date | Target | Class | Description | Resolution | Commit |
|---|---|---|---|---|---|
| 2026-11-23 | `paper/references.bib` (`BoyarFind2018`, `AFM2025`) | `error` | Pre-release Playbook Pass 5 live Crossref/PDF audit caught an incorrect DOI/title on `BoyarFind2018` (`10.1016/j.tcs.2018.04.017` resolved to an unrelated scheduling paper) and inaccurate author/title metadata on `AFM2025`. | Replaced with primary-source verified entries: Boyar & Find, *Multiplicative complexity of vector valued Boolean functions*, TCS 720 (2018), pp. 36–46, DOI `10.1016/j.tcs.2018.02.023`; Alekseev, Filmus, Mertz, Smal & Vinciguerra, *Catalytic Computing and Register Programs Beyond Log-Depth*, MFCS 2025, LIPIcs 345, pp. 6:1–6:18, DOI `10.4230/LIPIcs.MFCS.2025.6` (`arXiv:2504.17412`). Added automated `scripts/check_citations.py`. | Pre-release hardening |
| 2026-11-23 | `paper/main.tex` (`cor:streaming`, `cor:matpow`) | `error` | Pre-release primary-PDF verification against Vinciguerra (`arXiv:2609.18692`, Cor. 5.1.1 & Thm. 5.2) caught an understated regular workspace bound in `cor:streaming` and imprecise matrix-register phrasing in `cor:matpow`. | Updated `cor:streaming` workspace to $O(D \log(m+1) + \log n + \log D)$ bits matching Vinciguerra Cor. 5.1.1, and stated exact scalar register count $2m^2 + \binom{m^2+2}{2} - 1$ for general non-commutative matrices via Vinciguerra §4.4's $\ell_A(z)$ lift in `cor:matpow`. | Pre-release hardening |
