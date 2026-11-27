# SPDX-License-Identifier: Apache-2.0
"""
Deterministic publication-grade vector PDF figure generator for catalytic-register-frontiers.
Produces 3 vector PDFs in paper/figures/ with CreationDate=None for byte-level reproducibility.

Epistemic note (Playbook #14 — numerical_approximation):
  All floating-point NumPy/matplotlib calculations in this file are strictly
  ``numerical_approximation`` used solely for visual plotting of coordinates and curves.
  No theorem, inequality, or verification claim depends on floating-point arithmetic;
  every mathematical claim is proved using exact integer/rational/Lean kernel arithmetic.
"""

from __future__ import annotations

import pathlib

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

REPO = pathlib.Path(__file__).resolve().parent.parent
FIG_DIR = REPO / "paper" / "figures"
RES_DIR = REPO / "results"

# Okabe-Ito colorblind-safe palette
C_BLUE = "#0072B2"
C_ORANGE = "#D55E00"
C_GREEN = "#009E73"
C_PURPLE = "#CC79A7"
C_GOLD = "#E69F00"
C_GREY = "#555555"
C_RED = "#B2182B"


def setup_style() -> None:
    plt.rcParams.update({
        "font.family": "serif",
        "font.size": 9.5,
        "axes.titlesize": 10.5,
        "axes.labelsize": 9.5,
        "legend.fontsize": 8.2,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })


def digit_sum(p: int, n: int) -> int:
    s = 0
    while n > 0:
        s += n % p
        n //= p
    return s


def make_fig1() -> None:
    """Fig 1: Base-p Digit-Sum Phase Diagram (Theorem T1)."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.65), dpi=300)

    # Panel A: F_5 exact min calls s_5(d)+1 vs degree d in 2..50
    ds_feas, ts_feas = [], []
    ds_imp, sp_imp = [], []
    for d in range(2, 51):
        s = digit_sum(5, d)
        if s <= 4:
            ds_feas.append(d)
            ts_feas.append(s + 1)
        else:
            ds_imp.append(d)
            sp_imp.append(s + 1)

    # Characteristic-0 Vinciguerra line t = d + 1 (clipped to y <= 10.5)
    x_vinc = np.linspace(2, 9.2, 100)
    ax1.plot(x_vinc, x_vinc + 1, linestyle="--", color=C_GREY, lw=1.3,
             label=r"Char. 0 frontier $t = d + 1$ (Vinciguerra Thm. 3.5)")
    ax1.axhspan(5.5, 10.8, color=C_RED, alpha=0.08, label=r"Impossibility zone ($s_5(d) \geq 5$, no $t$ works)")
    ax1.axhline(5.5, color=C_RED, linestyle=":", lw=1.1)

    ax1.scatter(ds_feas, ts_feas, color=C_BLUE, s=26, zorder=4, label=r"Feasible over $\mathbb{F}_5$: $t_{\min} = s_5(d)+1$")
    ax1.scatter(ds_imp, [min(v, 10.2) for v in sp_imp], color=C_RED, marker="x", s=24, linewidths=1.2,
                zorder=4, label=r"No $\mathbb{F}_5$-const formal prog ($\forall t \geq 1$)")

    # Highlight Frobenius powers d = 5, 25
    for d_f in [5, 25]:
        ax1.scatter([d_f], [2], s=75, facecolors="none", edgecolors=C_GREEN, linewidths=1.7, zorder=5)
    ax1.annotate(r"$x^5, x^{25}$: 2 accesses!", xy=(25, 2), xytext=(28, 3.15),
                 fontsize=8.2, color=C_GREEN, fontweight="bold",
                 arrowprops=dict(arrowstyle="->", color=C_GREEN, lw=1.0))

    ax1.set_xlim(1, 51.5)
    ax1.set_ylim(1.2, 11.2)
    ax1.set_yticks([2, 3, 4, 5, 8])
    ax1.set_yticklabels(["2", "3", "4", "5", r"$\infty$"])
    ax1.set_xlabel(r"Monomial degree $d$ in $\mathbb{F}_5[x]$")
    ax1.set_ylabel(r"Minimum input accesses $t_{\min}(d)$")
    ax1.set_title(r"(a) Exact $\mathbb{F}_5$ Two-Register Phase Portrait")
    ax1.legend(loc="upper right", frameon=True, framealpha=0.95, fontsize=7.3)
    ax1.grid(axis="y", alpha=0.25, linestyle="-")

    # Panel B: Stacked phase breakdown across F_2, F_3, F_5, F_7, F_11 for d = 2..100
    primes = [2, 3, 5, 7, 11]
    pct_2acc, pct_mid, pct_imp = [], [], []
    total_d = 99  # d = 2..100
    for p in primes:
        c2 = sum(1 for d in range(2, 101) if digit_sum(p, d) == 1)
        cm = sum(1 for d in range(2, 101) if 2 <= digit_sum(p, d) <= p - 1)
        ci = sum(1 for d in range(2, 101) if digit_sum(p, d) >= p)
        pct_2acc.append(100.0 * c2 / total_d)
        pct_mid.append(100.0 * cm / total_d)
        pct_imp.append(100.0 * ci / total_d)

    x_idx = np.arange(len(primes))
    w = 0.56
    ax2.bar(x_idx, pct_2acc, width=w, color=C_GREEN, label=r"$s_p(d)=1$ (2 accesses: $x^{p^m}$)")
    ax2.bar(x_idx, pct_mid, width=w, bottom=pct_2acc, color=C_BLUE,
            label=r"$2 \leq s_p(d) \leq p-1$ ($s_p(d)+1$ accesses)")
    b2 = [a + b for a, b in zip(pct_2acc, pct_mid)]
    ax2.bar(x_idx, pct_imp, width=w, bottom=b2, color=C_RED, alpha=0.82,
            label=r"$s_p(d) \geq p$ (impossible $\forall t$)")

    for i, (v2, vm, vi) in enumerate(zip(pct_2acc, pct_mid, pct_imp)):
        if vi > 10:
            ax2.text(i, v2 + vm + vi / 2, f"{vi:.0f}%", ha="center", va="center",
                     color="white", fontsize=8.0, fontweight="bold")
        if vm > 12:
            ax2.text(i, v2 + vm / 2, f"{vm:.0f}%", ha="center", va="center",
                     color="white", fontsize=8.0, fontweight="bold")

    ax2.set_xticks(x_idx)
    ax2.set_xticklabels([rf"$\mathbb{{F}}_{{{p}}}$" for p in primes])
    ax2.set_ylim(0, 134)
    ax2.set_yticks([0, 20, 40, 60, 80, 100])
    ax2.set_ylabel(r"Share of degrees $d \in [2, 100]$ (%)")
    ax2.set_title(r"(b) Dichotomy Across Prime Fields ($d \in [2, 100]$)")
    ax2.legend(loc="upper center", ncol=1, frameon=True, framealpha=0.95, fontsize=7.3)
    ax2.grid(axis="y", alpha=0.25)

    fig.tight_layout(pad=1.2)
    out = FIG_DIR / "fig1_digit_sum_phase.pdf"
    fig.savefig(out, format="pdf", metadata={"CreationDate": None})
    plt.close(fig)
    print(f"Wrote {out}")


def make_fig2() -> None:
    """Fig 2: 3-Register Powering Frontier & Composition Exponent Improvement (Theorem T3)."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.65), dpi=300)

    # Panel A: Degree frontier vs t
    t_vals = np.array([2, 3, 4, 5, 6, 7, 8, 9])
    d_r2 = t_vals - 1
    t_r3_vinc = np.array([2, 3, 4])
    d_r3_vinc = np.array([1, 2, 5])
    t_r3_new = np.array([5, 6, 7, 8, 9])
    d_r3_new = np.array([7, 9, 11, 13, 15])

    ax1.plot(t_vals, d_r2, "s--", color=C_GREY, lw=1.3, markersize=4.5,
             label=r"$r=2$: $D_{2,\mathbb{Q}}^{\mathrm{pass}}(t) = t-1$ (exact)")
    ax1.plot([4, 9], [5, 15], "-", color=C_BLUE, lw=1.4, alpha=0.45)
    ax1.scatter(t_r3_vinc, d_r3_vinc, color=C_ORANGE, marker="D", s=40, zorder=5,
                label=r"$r=3$ prior (Vinciguerra Thm. 2.3: $t=4 \to x^5$)")
    ax1.scatter(t_r3_new, d_r3_new, color=C_BLUE, s=48, zorder=6,
                label=r"$r=3$ Lean-verified (Thm. T3: $x^7, x^9, x^{11}, x^{13}, x^{15}$)")

    for tv, dv in [(4, 5), (5, 7), (6, 9), (7, 11), (8, 13), (9, 15)]:
        ax1.annotate(rf"$x^{{{dv}}}$", xy=(tv, dv), xytext=(tv + 0.14, dv - 1.15),
                     fontsize=8.2, color=C_ORANGE if tv == 4 else C_BLUE, fontweight="bold")

    ax1.set_xlim(1.6, 9.75)
    ax1.set_ylim(0, 17.8)
    ax1.set_xticks(t_vals)
    ax1.set_xlabel(r"Number of input accesses $t$")
    ax1.set_ylabel(r"Achieved clean polynomial degree $N$")
    ax1.set_title(r"(a) Three-Register Frontier $D_{3,\mathbb{Q}}^{\mathrm{pass}}(t) \geq 2t - 3$")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.95, fontsize=7.1)
    ax1.grid(alpha=0.25)

    # Panel B: Composition exponent curve log(t) / log(2t - 3)
    tc = np.linspace(4.0, 13.5, 300)
    eps_c = np.log(tc) / np.log(2.0 * tc - 3.0)
    ax2.plot(tc, eps_c, "-", color=C_BLUE, lw=1.7, label=r"Curve $\varepsilon(t) = \log_{2t-3} t$")

    ti = np.arange(4, 14)
    ei = np.log(ti) / np.log(2.0 * ti - 3.0)
    ax2.scatter([4], [ei[0]], color=C_ORANGE, marker="D", s=52, zorder=5,
                label=rf"Vinciguerra ($t=4$): $\log_5 4 = {ei[0]:.5f}$")
    ax2.scatter([5, 6, 7, 9], [ei[1], ei[2], ei[3], ei[5]], color=C_BLUE, s=42, zorder=5,
                label=r"Lean-verified programs ($t=5,6,7,9$)")
    ax2.scatter([8], [ei[4]], color=C_GREEN, marker="*", s=130, zorder=6,
                label=rf"Family min ($t=8$): $\log_{{13}} 8 = {ei[4]:.5f}$")
    ax2.scatter(ti[6:], ei[6:], color=C_GREY, s=22, alpha=0.65, zorder=4,
                label=r"$t \geq 10$ (curve rises; Lean T3f $\forall t \neq 8$)")

    ax2.axhline(30.0 / 37.0, color=C_PURPLE, linestyle=":", lw=1.1,
                label=r"Lean T3f family separator $30/37 \approx 0.81081$")
    ax2.annotate(r"$\mathbf{-0.0506}$ exponent drop!" + "\n" + r"($0.86135 \to 0.81071$)",
                 xy=(8, ei[4]), xytext=(8.6, 0.836),
                 fontsize=8.0, color=C_GREEN, fontweight="bold",
                 arrowprops=dict(arrowstyle="->", color=C_GREEN, lw=1.1))

    ax2.set_xlim(3.6, 13.5)
    ax2.set_ylim(0.802, 0.870)
    ax2.set_xticks(range(4, 14))
    ax2.set_xlabel(r"Base loop input accesses $t$")
    ax2.set_ylabel(r"Powering / streaming exponent $\varepsilon(t)$")
    ax2.set_title(r"(b) Family Exponent $\log_{2t-3} t$ ($\min$ at $t=8$)")
    ax2.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=7.1)
    ax2.grid(alpha=0.25)

    fig.tight_layout(pad=1.2)
    out = FIG_DIR / "fig2_three_reg_exponent.pdf"
    fig.savefig(out, format="pdf", metadata={"CreationDate": None})
    plt.close(fig)
    print(f"Wrote {out}")


def make_fig3() -> None:
    """Fig 3: Strictly Bilinear 2-Access Frobenius (T2) & Balanced O(d^2) Product (T4)."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.2, 3.65), dpi=300)

    # Panel A: T2 — input accesses vs degree 2^k in char 2 vs char 0
    ks = np.arange(1, 7)
    degs = 2 ** ks
    bilin_ops = 4 * ks - 2
    acc_f2 = np.full_like(ks, 2)

    ax1.plot(ks, acc_f2, "o-", color=C_GREEN, lw=2.0, markersize=6,
             label=r"$\mathbb{F}_2$ bilinear cascade: 2 accesses ($\forall k \geq 1$)")
    ax1.plot(ks, bilin_ops, "s--", color=C_BLUE, lw=1.4, markersize=5,
             label=r"Bilinear ops $4k - 2$ (using $k+1$ registers)")
    ax1.axhline(4, color=C_RED, linestyle=":", lw=1.3,
                label=r"Char. 0 lower bound ($\geq 4$ accesses for $\deg \geq 3$)")
    ax1.fill_between(ks, 2, 4, color=C_GREEN, alpha=0.07)

    for k, d in zip(ks, degs):
        ax1.text(k, 0.72, rf"$x^{{{d}}}$", ha="center", va="center",
                 fontsize=7.8, color=C_GREEN, fontweight="bold")

    ax1.set_xticks(ks)
    ax1.set_xticklabels([rf"$k={k}$" for k in ks], fontsize=8.3)
    ax1.set_ylim(0, 26)
    ax1.set_xlabel(r"Frobenius tower depth $k$ (computing $x^{2^k}$)")
    ax1.set_ylabel("Instruction / access count")
    ax1.set_title(r"(a) Theorem T2: Bilinear 2-Access Collapse over $\mathbb{F}_2$")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.95, fontsize=7.4)
    ax1.grid(alpha=0.25)

    # Panel B: T4 — Balanced O(d^2) vs Linear Chain O(4^d) op count (log scale)
    ds = np.array([2, 4, 8, 16, 32])
    ops_bal = (7 * ds**2 - 4) // 3
    ops_lin = np.array([3 * (4 ** (int(d) - 1)) - 2 for d in ds], dtype=float)

    ax2.semilogy(ds, ops_lin, "s--", color=C_ORANGE, lw=1.6, markersize=5.5,
                 label=r"Linear chain: $3 \cdot 4^{d-1} - 2$ ops ($d$ regs)")
    ax2.semilogy(ds, ops_bal, "o-", color=C_BLUE, lw=2.0, markersize=6,
                 label=r"Balanced tree (Thm. T4): $(7d^2-4)/3$ ops ($\log_2 d + 2$ regs)")

    ax2.annotate(r"$d=8$: 148 ops vs. 49,150" + "\n(332x fewer ops!)",
                 xy=(8, 148), xytext=(3.0, 2.0e8),
                 fontsize=7.7, color=C_BLUE, fontweight="bold",
                 arrowprops=dict(arrowstyle="->", color=C_BLUE, lw=1.0))
    ax2.annotate(r"$d=16$: 596 vs. $3.2\times 10^9$",
                 xy=(16, 596), xytext=(17.2, 8.0e5),
                 fontsize=7.7, color=C_ORANGE, fontweight="bold",
                 arrowprops=dict(arrowstyle="->", color=C_ORANGE, lw=1.0))

    ax2.set_xticks(ds)
    ax2.set_xticklabels([f"{d}" for d in ds])
    ax2.set_xlim(1, 34)
    ax2.set_ylim(4, 2e22)
    ax2.set_xlabel(r"Multilinear product arity $d = 2^k$")
    ax2.set_ylabel("Primitive bilinear/input operations (log scale)")
    ax2.set_title(r"(b) Theorem T4: Zero-Workspace Balanced Product")
    ax2.legend(loc="upper left", frameon=True, framealpha=0.95, fontsize=7.3)
    ax2.grid(alpha=0.25)

    fig.tight_layout(pad=1.2)
    out = FIG_DIR / "fig3_bilinear_and_balanced.pdf"
    fig.savefig(out, format="pdf", metadata={"CreationDate": None})
    plt.close(fig)
    print(f"Wrote {out}")


def main() -> None:
    setup_style()
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    make_fig1()
    make_fig2()
    make_fig3()


if __name__ == "__main__":
    main()
