"""
Generates three publication-grade 300-DPI figures for Paper 98:
  1. paper/figures/fig1_dicke_moments_kurtosis.png
  2. paper/figures/fig2_operating_point_grover_sharpening.png
  3. paper/figures/fig3_reversible_router_scaling.png
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT.joinpath("src")))
import qmbs_dicke_verifier as ver

FIG_DIR = ROOT.joinpath("paper", "figures")
FIG_DIR.mkdir(parents=True, exist_ok=True)

plt.rcParams.update(
    {
        "font.family": "DejaVu Sans",
        "font.size": 9.5,
        "axes.titlesize": 10.5,
        "axes.labelsize": 9.5,
        "legend.fontsize": 8.2,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "figure.dpi": 300,
    }
)


def make_fig1() -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.5, 4.1))

    # Panel (a): Exact kappa4 vs M' across filling ratios & resonance classes vs Asari bound 12
    Ms_even = np.arange(4, 102, 2)
    Ms_4 = np.arange(4, 104, 4)
    k4_gen_half = [float(ver.exact_dicke_moments(int(M), int(M) // 2, 1)["kappa4"]) for M in Ms_even]
    k4_res4_half = [float(ver.exact_dicke_moments(int(M), int(M) // 2, int(M) // 2)["kappa4"]) for M in Ms_even]
    k4_gen_qtr = [float(ver.exact_dicke_moments(int(M), int(M) // 4, 1)["kappa4"]) for M in Ms_4]
    k4_n1 = [float(ver.exact_dicke_moments(int(M), 1, 1)["kappa4"]) for M in Ms_even]

    ax1.axhline(12.0, color="#c0392b", linestyle="--", lw=1.6, label=r"Asari et al. Hoeffding bound ($\kappa_4 \leq 12$)")
    ax1.axhline(3.0, color="#1b4f72", linestyle=":", lw=1.6, label=r"Our universal sharp bound ($\kappa_4 \leq 3$, $4\times$ tighter)")
    ax1.plot(Ms_even, k4_gen_half, color="#2980b9", lw=1.9, label=r"Exact generic ($n=M'/2$)")
    ax1.plot(Ms_even, k4_res4_half, color="#e67e22", lw=1.7, linestyle="-.", label=r"Exact $4l=2M'$ ($n=M'/2$)")
    ax1.plot(Ms_4, k4_gen_qtr, color="#27ae60", lw=1.5, label=r"Exact generic ($n=M'/4$)")
    ax1.plot(Ms_even, k4_n1, color="#8e44ad", lw=1.5, label=r"Exact $n=1$ ($\kappa_4 = 3/2$)")
    ax1.scatter([4], [3.0], color="#d35400", s=55, zorder=6, marker="D", label=r"Unique $\kappa_4=3$ point $(4,2,2)$")
    ax1.annotate(
        r"$(4,2,2)$: $\kappa_4=3$",
        xy=(4, 3.0),
        xytext=(15, 5.2),
        fontsize=8.2,
        arrowprops=dict(arrowstyle="->", color="#d35400", lw=1.0),
        color="#a04000",
    )
    ax1.annotate(
        "",
        xy=(93, 3.1),
        xytext=(93, 11.9),
        arrowprops=dict(arrowstyle="<->", color="#922b21", lw=1.3),
    )
    ax1.text(
        90.5,
        7.5,
        r"$4\times$" "\ngap",
        ha="right",
        va="center",
        fontsize=8.5,
        fontweight="bold",
        color="#922b21",
    )
    ax1.set_xlabel(r"Effective chain size $M'$")
    ax1.set_ylabel(r"Normalized fourth moment $\kappa_4 = \langle Z(l)^4\rangle/\langle Z(l)^2\rangle^2$")
    ax1.set_title("(a) Exact Kurtosis vs. Asari et al. Hoeffding Bound")
    ax1.set_ylim(0.5, 13.2)
    ax1.set_xlim(2, 102)
    ax1.grid(alpha=0.25)
    ax1.legend(loc=(0.14, 0.43), framealpha=0.95, fontsize=7.3)

    # Panel (b): Sixth moment kappa6 (<=15 vs 120) and orthogonal-projection variance kappa6 - kappa4^2 (< 6)
    k6_gen_half = [float(ver.exact_dicke_moments(int(M), int(M) // 2, 1)["kappa6"]) for M in Ms_even]
    k6_res4_half = [float(ver.exact_dicke_moments(int(M), int(M) // 2, int(M) // 2)["kappa6"]) for M in Ms_even]
    var_gen_half = [float(ver.exact_dicke_moments(int(M), int(M) // 2, 1)["excess_var"]) for M in Ms_even]
    Ms_3 = np.arange(6, 102, 3)
    var_res3_half = [float(ver.exact_dicke_moments(int(M), int(M) // 2, (2 * int(M)) // 3)["excess_var"]) for M in Ms_3]

    ax2.axhline(15.0, color="#1b4f72", linestyle=":", lw=1.5, label=r"Sharp $\kappa_6 < 15$ ($8\times$ tighter than $120$)")
    ax2.plot(Ms_even, k6_gen_half, color="#2980b9", lw=1.9, label=r"Exact $\kappa_6$ (generic, $n=M'/2$)")
    ax2.plot(Ms_even, k6_res4_half, color="#e67e22", lw=1.6, linestyle="-.", label=r"Exact $\kappa_6$ ($4l=2M'$, $n=M'/2$)")
    ax2.axhline(6.0, color="#145a32", linestyle="--", lw=1.5, label=r"Sharp variance bound $\kappa_6-\kappa_4^2 < 6$")
    ax2.plot(Ms_even, var_gen_half, color="#27ae60", lw=1.8, label=r"Exact $\kappa_6-\kappa_4^2$ (generic)")
    ax2.plot(Ms_3, var_res3_half, color="#8e44ad", lw=1.5, linestyle=":", label=r"Exact $\kappa_6-\kappa_4^2$ ($3l=2M'$)")
    ax2.set_xlabel(r"Effective chain size $M'$")
    ax2.set_ylabel(r"Normalized sixth moment & excess variance")
    ax2.set_title(r"(b) Exact $\kappa_6 < 15$ and Projection Variance $\kappa_6 - \kappa_4^2 < 6$")
    ax2.set_ylim(-0.5, 16.5)
    ax2.set_xlim(2, 102)
    ax2.grid(alpha=0.25)
    ax2.legend(loc=(0.35, 0.43), framealpha=0.95, fontsize=7.4)

    plt.tight_layout()
    fig.savefig(FIG_DIR.joinpath("fig1_dicke_moments_kurtosis.png"), dpi=300, bbox_inches="tight")
    plt.close(fig)


def make_fig2() -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.5, 4.1))
    s_grid = np.linspace(0.05, 0.50, 300)

    # Panel (a): Rigorous uniform infidelity upper bound vs Gaussian limit & Asari Eq. (S9)
    our_inf = (s_grid**4 * (4.0 + 3.0 * s_grid**2)) / (6.0 * (2.0 - s_grid**2) ** 2)
    asari_inf = (10.0 / 3.0) * (s_grid**4)
    gauss_inf = 1.0 - (2.0 * s_grid**2 * np.exp(-(s_grid**2))) / (1.0 - np.exp(-2.0 * s_grid**2))

    ax1.semilogy(s_grid, asari_inf, color="#c0392b", linestyle="--", lw=1.8, label=r"Asari et al. Eq. (S9): $\frac{10}{3}s^4$")
    ax1.semilogy(s_grid, our_inf, color="#1f618d", lw=2.1, label=r"Our Thm. B: $\frac{s^4(4+3s^2)}{6(2-s^2)^2}$")
    ax1.semilogy(s_grid, gauss_inf, color="#27ae60", linestyle=":", lw=1.8, label=r"Gaussian limit Eq. (S14)")
    ax1.axhline(0.01, color="#555555", linestyle="-.", lw=1.1, label=r"Target $\varepsilon = 0.01$")
    ax1.scatter([0.45], [(0.45**4 * (4 + 3 * 0.45**2)) / (6 * (2 - 0.45**2) ** 2)], color="#1f618d", s=50, zorder=6)
    ax1.scatter([0.495], [(0.495**4 * (4 + 3 * 0.495**2)) / (6 * (2 - 0.495**2) ** 2)], color="#d35400", s=55, marker="D", zorder=6)
    ax1.annotate(
        r"$s=0.45$: $0.00975 < 0.01$",
        xy=(0.45, 0.00975),
        xytext=(0.18, 0.0020),
        fontsize=8.0,
        arrowprops=dict(arrowstyle="->", color="#1f618d", lw=1.0),
        color="#1f618d",
    )
    ax1.annotate(
        r"$s=0.495$: $13.0\times$ sharper",
        xy=(0.495, 0.01538),
        xytext=(0.24, 0.085),
        fontsize=8.0,
        fontweight="bold",
        arrowprops=dict(arrowstyle="->", color="#d35400", lw=1.0),
        color="#a04000",
    )
    ax1.set_xlabel(r"Dimensionless rotation parameter $s = \tau\langle Z(l)^2\rangle^{1/2}$")
    ax1.set_ylabel(r"Certified uniform infidelity $1 - F$ (log scale)")
    ax1.set_title("(a) Optimal-Projection Uniform Infidelity Bound")
    ax1.set_ylim(1e-5, 0.4)
    ax1.set_xlim(0.05, 0.51)
    ax1.grid(alpha=0.25, which="both")
    ax1.legend(loc="lower right", framealpha=0.92, fontsize=7.6)

    # Panel (b): Certified p_succ & K=1 Grover amplified probability vs Asari Eq. (S15)
    our_p = s_grid**2 - s_grid**4
    asari_p = np.maximum(0.0, s_grid**2 - 4.0 * s_grid**4)
    gauss_p = 0.5 * (1.0 - np.exp(-2.0 * s_grid**2))
    our_amp1 = our_p * (3.0 - 4.0 * our_p) ** 2
    asari_amp1 = asari_p * (3.0 - 4.0 * asari_p) ** 2

    ax2.plot(s_grid, our_amp1, color="#145a32", lw=2.2, label=r"Our certified $K=1$ Grover $p_{\mathrm{amp}}^{(1)}$")
    ax2.plot(s_grid, asari_amp1, color="#e74c3c", linestyle="--", lw=1.6, label=r"Asari Eq. (S15) $K=1$ Grover $p_{\mathrm{amp}}^{(1)}$")
    ax2.plot(s_grid, our_p, color="#2980b9", lw=1.9, label=r"Our bare $p_{\mathrm{succ}} \geq s^2 - s^4$")
    ax2.plot(s_grid, gauss_p, color="#7f8c8d", linestyle=":", lw=1.5, label=r"Gaussian bare $p_{\mathrm{succ}}$")
    ax2.plot(s_grid, asari_p, color="#c0392b", linestyle="-.", lw=1.5, label=r"Asari Eq. (S15) bare $p_{\mathrm{succ}} \geq s^2 - 4s^4$")
    ax2.axvline(0.495, color="#d35400", linestyle=":", lw=1.1)
    ax2.scatter([0.495], [0.944884], color="#145a32", s=55, marker="D", zorder=6)
    ax2.scatter([0.495], [0.184988], color="#2980b9", s=45, zorder=6)
    ax2.scatter([0.495], [0.004876], color="#c0392b", s=45, zorder=6)
    ax2.annotate(
        r"$p_{\mathrm{amp}}^{(1)} \geq 0.945$" "\n" r"(vs. $0.043$, $21.8\times$)",
        xy=(0.495, 0.9449),
        xytext=(0.34, 0.56),
        fontsize=8.0,
        fontweight="bold",
        arrowprops=dict(arrowstyle="->", color="#145a32", lw=1.1),
        color="#145a32",
    )
    ax2.annotate(
        r"$37.9\times$ bare $p_{\mathrm{succ}}$",
        xy=(0.495, 0.185),
        xytext=(0.26, 0.30),
        fontsize=8.0,
        arrowprops=dict(arrowstyle="->", color="#2980b9", lw=1.0),
        color="#1f618d",
    )
    ax2.set_xlabel(r"Dimensionless rotation parameter $s$")
    ax2.set_ylabel("Certified success probability")
    ax2.set_title(r"(b) Bare $p_{\mathrm{succ}}$ & Certified Single-Round Amplification")
    ax2.set_ylim(-0.02, 1.05)
    ax2.set_xlim(0.05, 0.51)
    ax2.grid(alpha=0.25)
    ax2.legend(loc="upper left", framealpha=0.92, fontsize=7.3)

    plt.tight_layout()
    fig.savefig(FIG_DIR.joinpath("fig2_operating_point_grover_sharpening.png"), dpi=300, bbox_inches="tight")
    plt.close(fig)


def make_fig3() -> None:
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.5, 4.1))

    # Panel (a): Fredkin gate count at half filling (Onsager L = 3M'/2) vs Asari conveyor
    # Dense even grid so bit-width steps at n = 2^k and exact permanent crossover M'=184 are visible
    Mps_dense = np.unique(
        np.concatenate(
            [
                np.arange(16, 260, 2),
                (np.geomspace(260, 4096, 120).astype(int) // 2) * 2,
                np.array([182, 184, 254, 256, 510, 512, 1022, 1024, 2046, 2048, 4096]),
            ]
        )
    )
    Mps_pts = np.array([16, 32, 64, 128, 184, 256, 512, 1024, 2048, 4096], dtype=int)

    def fred_pair(arr):
        of, cf = [], []
        for Mp in arr:
            nw = int(Mp) // 2
            L = int(Mp) + nw
            B = nw.bit_length()
            of.append(B * (B * L - ((1 << B) - 1)))
            cf.append((nw * (2 * int(Mp) - nw - 1)) // 2)
        return np.array(of, dtype=float), np.array(cf, dtype=float)

    our_dense, conv_dense = fred_pair(Mps_dense)
    our_pts, conv_pts = fred_pair(Mps_pts)

    ax1.loglog(Mps_dense, conv_dense, "--", color="#c0392b", lw=1.8, label=r"Conservative conveyor $\frac{1}{2}n(2M'-n-1)$")
    ax1.loglog(Mps_dense, our_dense, "-", color="#1f618d", lw=2.0, label=r"Our MSB-to-LSB router $O(M'\log^2 n)$")
    ax1.scatter(Mps_pts, conv_pts, color="#c0392b", s=24, zorder=5)
    ax1.scatter(Mps_pts, our_pts, color="#1f618d", s=24, marker="s", zorder=5)
    ax1.axvline(184, color="#7f8c8d", linestyle=":", lw=1.1)
    idx_184 = int(np.where(Mps_pts == 184)[0][0])
    ax1.annotate(
        r"Permanent crossover" "\n" r"$M'=184$ ($12635 < 12650$)",
        xy=(184, our_pts[idx_184]),
        xytext=(20, 1.3e5),
        fontsize=7.8,
        arrowprops=dict(arrowstyle="->", color="#1f618d", lw=1.0),
        color="#1f618d",
    )
    ratio_max = conv_pts[-1] / our_pts[-1]
    ax1.annotate(
        rf"$M'=4096$: ${ratio_max:.2f}\times$ fewer",
        xy=(4096, our_pts[-1]),
        xytext=(520, 1.4e4),
        fontsize=8.2,
        fontweight="bold",
        arrowprops=dict(arrowstyle="->", color="#145a32", lw=1.1),
        color="#145a32",
    )
    ax1.set_xlabel(r"Effective chain size $M'$ (half filling $n = M'/2$)")
    ax1.set_ylabel("Fredkin (CSWAP) gate count (log scale)")
    ax1.set_title(r"(a) Subquadratic Routing $\Phi^{-1}$: Fredkin Gate Scaling")
    ax1.grid(alpha=0.25, which="both")
    ax1.legend(loc="upper left", framealpha=0.92, fontsize=8.0)

    # Panel (b): Speedup ratio (conveyor / ours) across M' and filling fractions
    for rho, lbl, col in [(0.5, r"$n = M'/2$ (half filling)", "#1f618d"),
                          (0.25, r"$n = M'/4$", "#27ae60"),
                          (0.125, r"$n = M'/8$", "#8e44ad")]:
        M_list = np.array([64, 128, 256, 512, 1024, 2048, 4096], dtype=int)
        ratios = []
        for Mp in M_list:
            nw = max(1, int(round(Mp * rho)))
            L = int(Mp) + nw
            B = nw.bit_length()
            of = B * (B * L - ((1 << B) - 1))
            cf = (nw * (2 * int(Mp) - nw - 1)) // 2
            ratios.append(cf / of)
        ax2.plot(M_list, ratios, "o-", color=col, lw=1.9, markersize=5, label=lbl)

    ax2.axhline(1.0, color="#c0392b", linestyle="--", lw=1.2, label="Break-even (1.0x)")
    ax2.set_xscale("log", base=2)
    ax2.set_xlabel(r"Effective chain size $M'$ (log$_2$ scale)")
    ax2.set_ylabel("Fredkin gate reduction factor (Conveyor / Ours)")
    ax2.set_title("(b) Routing Gate Reduction Across Filling Fractions")
    ax2.grid(alpha=0.25, which="both")
    ax2.legend(loc="upper left", framealpha=0.92, fontsize=8.0)

    plt.tight_layout()
    fig.savefig(FIG_DIR.joinpath("fig3_reversible_router_scaling.png"), dpi=300, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated all 3 300-DPI figures in paper/figures/ successfully!")
