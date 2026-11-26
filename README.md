# Exact Dicke-State Moments, Certified Single-Round Amplification, and Subquadratic Reversible Routing for Asymptotic Quantum Many-Body Scars

[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0%20(18%20theorems%2C%200%20sorry%2C%200%20Classical.choice)-blue)](lean/QmbsDickeSharp.lean)
[![Certificates](https://img.shields.io/badge/QMBS--DICKE--SHARP--1.0-16%2F16%20SHA--256%20PASS-brightgreen)](certificates/MANIFEST.sha256)
[![Tests](https://img.shields.io/badge/pytest-53%2F53%20PASS%20(30%20forgeries)-brightgreen)](tests/test_qmbs_dicke.py)
[![License: MIT / CC-BY-4.0](https://img.shields.io/badge/License-MIT%20(code)%20%2F%20CC--BY--4.0%20(paper)-lightgrey)](LICENSE)

**Author:** Lluis Eriksson  
**Target Paper Sharpened:** Y. Asari, M. Kunimi, and T. Nikuni, *Unified preparation of exact and asymptotic quantum many-body scars from Dicke states*, [arXiv:2611.33987v1](https://arxiv.org/abs/2611.33987) (Nov 2026).

## Main Results

1. **Theorem A (Exact Without-Replacement Dicke Moments & Universal Kurtosis Bounds):** Derives exact closed-form rational formulas for $\langle Z(l)^4 \rangle$ and $\langle Z(l)^6 \rangle$ across all four cosine power-sum resonance classes, proving uniformly for all $M' \ge 2$, $1 \le n \le M'-1$, $1 \le l \le M'-1$:
   - $\kappa_4 \le 3$ (**$4\times$ sharper** than Asari et al.'s $\kappa_4 \le 12$, with unique finite equality at $(M', n, l) = (4, 2, 2)$);
   - $\kappa_6 < 15$ (**$8\times$ sharper** than $\kappa_6 \le 120$);
   - $\kappa_6 - \kappa_4^2 < 6$ (**$20\times$ leading-order sharpening** of the infidelity variance).
2. **Theorem B (Optimal-Projection Infidelity Bound & Certified $K = 1$ Grover Amplification):** Proves $1 - F(s) \le \frac{s^4(4 + 3s^2)}{6(2 - s^2)^2}$ for all $0 < s < \sqrt{2}$ and $s^2 - s^4 \le p_{\mathrm{succ}}(s) \le s^2$. At Asari et al.'s operating point $s = 0.495$, this yields $p_{\mathrm{succ}} \ge 0.18499$ (**$37.94\times$ sharper** than Eq. S15), rigorously certifies single-round Grover $p_{\mathrm{amp}}^{(1)} \ge 0.94488$ with zero overshoot (**$21.8\times$ jump**), and improves the uniform infidelity bound by **$13.01\times$** (to $0.01538$). At $s = 0.45$, it certifies $1 - F \le 0.00975 < 0.01$ uniformly with $p_{\mathrm{succ}} \ge 0.16149$ (**$25.84\times$ sharper** than Eq. S11).
3. **Theorem C (Collision-Free Subquadratic Reversible Routing for $\Phi^{-1}$):** Resolves Asari et al.'s SM B.2 open problem for $3 \le n \le M'-2$ via a strictly order-preserving MSB-to-LSB binary-shift reversible router using exactly $B(BL - 2^B + 1) = O(M \log^2 n)$ Fredkin gates with zero ancilla leakage (permanent half-filling crossover at $M' = 184$; $2.74\times$ fewer Fredkin gates at $M' = 1024$ and $7.53\times$ fewer at $M' = 4096$ vs. the conservative $\Theta(M^2)$ conveyor benchmark).

## Quick Verification

```bash
# 1. Lean 4.35.0 formal verification (18 theorems, 0 sorry, 0 Classical.choice)
cd lean && lake build && lake env lean QmbsDickeSharp.lean

# 2. AST-audited zero-float exact rational certificate verification (16/16 PASS)
python src/qmbs_dicke_verifier.py certificates

# 3. Full pytest + 30 adversarial forgery attacks (53/53 PASS)
pytest -q -p no:cacheprovider
```
