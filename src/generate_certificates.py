"""
Generates the 16 exact rational SHA-256 certificates (C01-C16) and MANIFEST.sha256
for Paper 98 (schema: QMBS-DICKE-SHARP-1.0).
"""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path

from qmbs_dicke_verifier import (
    SCHEMA_ID,
    compute_cert_sha256,
    div_frac,
    exact_dicke_moments,
    replay_reversible_router_single,
    verify_directory,
)


def enc_frac(f: Fraction) -> list[int]:
    return [f.numerator, f.denominator]


def make_moment_cert(cid: str, label: str, M: int, n: int, l: int) -> dict:
    res = exact_dicke_moments(M, n, l)
    n_eff = n if 2 * n <= M else M - n
    asari_mu4 = Fraction(12 * n_eff * n_eff, 1)
    asari_mu6 = Fraction(120 * n_eff * n_eff * n_eff, 1)
    cert = {
        "schema": SCHEMA_ID,
        "cert_id": cid,
        "cert_type": "exact_moment_cert",
        "label": label,
        "M": M,
        "n": n,
        "l": l,
        "branch": res["branch"],
        "mu2": enc_frac(res["mu2"]),
        "mu4": enc_frac(res["mu4"]),
        "mu6": enc_frac(res["mu6"]),
        "kappa4": enc_frac(res["kappa4"]),
        "kappa6": enc_frac(res["kappa6"]),
        "excess_var": enc_frac(res["excess_var"]),
        "asari_mu4_ratio": enc_frac(div_frac(asari_mu4, res["mu4"])),
        "asari_mu6_ratio": enc_frac(div_frac(asari_mu6, res["mu6"])),
    }
    cert["sha256"] = compute_cert_sha256(cert)
    return cert


def make_operating_point_cert(
    cid: str, label: str, s: Fraction, target_eps: Fraction | None = None
) -> dict:
    s2 = s * s
    s4 = s2 * s2
    inf_ub = div_frac(s4 * (4 + 3 * s2), 6 * (2 - s2) * (2 - s2))
    asari_inf_ub = Fraction(10, 3) * s4
    p_lb = s2 - s4
    p_ub = s2
    asari_p_lb = s2 - 4 * s4
    p_amp1_lb = p_lb * (3 - 4 * p_lb) * (3 - 4 * p_lb)
    cert = {
        "schema": SCHEMA_ID,
        "cert_id": cid,
        "cert_type": "operating_point_cert",
        "label": label,
        "s": enc_frac(s),
        "infidelity_ub": enc_frac(inf_ub),
        "asari_infidelity_ub": enc_frac(asari_inf_ub),
        "infidelity_sharpening_ratio": enc_frac(div_frac(asari_inf_ub, inf_ub)),
        "psucc_lb": enc_frac(p_lb),
        "psucc_ub": enc_frac(p_ub),
        "asari_psucc_lb": enc_frac(asari_p_lb),
        "p_amp1_lb": enc_frac(p_amp1_lb),
    }
    if asari_p_lb > 0:
        cert["psucc_sharpening_ratio"] = enc_frac(div_frac(p_lb, asari_p_lb))
        asari_amp1 = asari_p_lb * (3 - 4 * asari_p_lb) * (3 - 4 * asari_p_lb)
        cert["asari_p_amp1_lb"] = enc_frac(asari_amp1)
    if target_eps is not None:
        cert["target_eps"] = enc_frac(target_eps)
    cert["sha256"] = compute_cert_sha256(cert)
    return cert


def make_router_exhaustive_cert(
    cid: str, label: str, mode: str, Mp: int, fixed_n: int | None = None
) -> dict:
    states_checked = 0
    max_fredkin = 0
    for mask in range(1 << Mp):
        x = [(mask >> i) & 1 for i in range(Mp)]
        nw = sum(x)
        if mode == "dwc" and nw == 0:
            continue
        if fixed_n is not None and nw != fixed_n:
            continue
        _, fc, _ = replay_reversible_router_single(x, mode)
        if fc > max_fredkin:
            max_fredkin = fc
        states_checked += 1
    cert = {
        "schema": SCHEMA_ID,
        "cert_id": cid,
        "cert_type": "reversible_router_cert",
        "subtype": "exhaustive_replay",
        "label": label,
        "mode": mode,
        "Mp": Mp,
        "fixed_n": fixed_n,
        "states_checked": states_checked,
        "max_fredkin_gates": max_fredkin,
    }
    cert["sha256"] = compute_cert_sha256(cert)
    return cert


def make_router_scaling_cert(cid: str, label: str, sizes: list[int]) -> dict:
    rows = []
    for Mp in sizes:
        nw = Mp // 2
        L = Mp + nw
        B = nw.bit_length()
        our_fredkin = B * (B * L - ((1 << B) - 1))
        conv_fredkin = (nw * (2 * Mp - nw - 1)) // 2
        rows.append(
            {
                "Mp": Mp,
                "n": nw,
                "L": L,
                "B": B,
                "our_fredkin": our_fredkin,
                "conveyor_fredkin": conv_fredkin,
                "speedup": enc_frac(Fraction(conv_fredkin, our_fredkin)),
                "beats_conveyor": our_fredkin < conv_fredkin,
            }
        )
    cert = {
        "schema": SCHEMA_ID,
        "cert_id": cid,
        "cert_type": "reversible_router_cert",
        "subtype": "macroscopic_scaling",
        "label": label,
        "rows": rows,
    }
    cert["sha256"] = compute_cert_sha256(cert)
    return cert


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    cert_dir = root.joinpath("certificates")
    cert_dir.mkdir(parents=True, exist_ok=True)

    certs = [
        ("C01_moment_M4_n2_l2_unique_k4_eq_3.json", make_moment_cert("C01", "Unique kappa4=3 attainment (4l=2M)", 4, 2, 2)),
        ("C02_moment_M6_n2_l1_generic.json", make_moment_cert("C02", "Small-M generic branch (M=6,n=2,l=1)", 6, 2, 1)),
        ("C03_moment_M6_n3_l2_res6.json", make_moment_cert("C03", "Small-M 6l=2M branch (M=6,n=3,l=2)", 6, 3, 2)),
        ("C04_moment_M6_n3_l4_res3.json", make_moment_cert("C04", "Small-M 3l=2M branch (M=6,n=3,l=4)", 6, 3, 4)),
        ("C05_moment_M12_n6_l1_asari_bench.json", make_moment_cert("C05", "Asari M=12 half-filling benchmark", 12, 6, 1)),
        ("C06_moment_M24_n12_l16_res3_closure.json", make_moment_cert("C06", "Top of 3l=2M finite closure (M=24,n=12,l=16)", 24, 12, 16)),
        ("C07_moment_M64_n32_l1_gaussian_onset.json", make_moment_cert("C07", "Asari SM A.1 M=64 half-filling benchmark", 64, 32, 1)),
        ("C08_moment_M1000_n500_l1_macroscopic.json", make_moment_cert("C08", "Macroscopic M=1000 half-filling limit", 1000, 500, 1)),
        ("C09_op_s0495_asari_eq12.json", make_operating_point_cert("C09", "Asari Eq. (12) operating point s=0.495", Fraction(99, 200))),
        ("C10_op_s045_certified_1pct.json", make_operating_point_cert("C10", "Certified 1% uniform infidelity s=0.45", Fraction(9, 20), Fraction(1, 100))),
        ("C11_op_s030_high_fidelity.json", make_operating_point_cert("C11", "High-fidelity regime s=0.30", Fraction(3, 10), Fraction(1, 500))),
        ("C12_op_s010_ultra_high_fidelity.json", make_operating_point_cert("C12", "Ultra-high-fidelity regime s=0.10", Fraction(1, 10), Fraction(1, 50000))),
        ("C13_router_onsager_Mp6_all64.json", make_router_exhaustive_cert("C13", "Exhaustive Onsager unitary router replay M'=6 (64 states)", "onsager", 6)),
        ("C14_router_dwc_Mp6_all63.json", make_router_exhaustive_cert("C14", "Exhaustive DWC unitary router replay M'=6 (63 states)", "dwc", 6)),
        ("C15_router_onsager_Mp8_n4_asari_figS2b.json", make_router_exhaustive_cert("C15", "Exhaustive Onsager half-filling M'=8, n=4 (Asari Fig S2b)", "onsager", 8, fixed_n=4)),
        ("C16_router_macroscopic_scaling.json", make_router_scaling_cert("C16", "Subquadratic MSB-to-LSB vs conveyor scaling", [128, 182, 184, 256, 512, 1024, 2048, 4096])),
    ]

    manifest_lines = []
    for fname, cert in certs:
        fpath = cert_dir.joinpath(fname)
        raw = json.dumps(cert, indent=2, sort_keys=True) + "\n"
        fpath.write_text(raw, encoding="utf-8")
        fsha = hashlib.sha256(fpath.read_bytes()).hexdigest()
        manifest_lines.append(f"{fsha}  {fname}")

    cert_dir.joinpath("MANIFEST.sha256").write_text("\n".join(manifest_lines) + "\n", encoding="utf-8")
    count = verify_directory(cert_dir)
    print(f"Generated and verified {count}/16 {SCHEMA_ID} certificates successfully!")


if __name__ == "__main__":
    main()
