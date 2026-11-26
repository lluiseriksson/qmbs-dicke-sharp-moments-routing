"""
Comprehensive test suite (including 28 adversarial forgery tests) for Paper 98
(schema: QMBS-DICKE-SHARP-1.0).
"""

from __future__ import annotations

import copy
import json
import sys
from fractions import Fraction
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT.joinpath("src")))

import qmbs_dicke_verifier as ver

CERT_DIR = ROOT.joinpath("certificates")


def load_cert(prefix: str) -> dict:
    matches = sorted(CERT_DIR.glob(f"{prefix}*.json"))
    assert len(matches) == 1, f"Expected 1 match for {prefix}, got {matches}"
    return json.loads(matches[0].read_text(encoding="utf-8"))


def rehash(cert: dict) -> dict:
    c = copy.deepcopy(cert)
    c["sha256"] = ver.compute_cert_sha256(c)
    return c


# --- Positive & Self-Audit Tests ---

def test_01_ast_zero_float_self_audit():
    ver.ast_zero_float_audit(Path(ver.__file__).resolve())


def test_02_full_certificate_directory_and_manifest():
    assert ver.verify_directory(CERT_DIR) == 16


@pytest.mark.parametrize(
    "prefix",
    [f"C{i:02d}_" for i in range(1, 17)],
)
def test_03_each_certificate_individually(prefix: str):
    cert = load_cert(prefix)
    ver.verify_certificate_dict(cert)


def test_04_exact_moments_small_M_exhaustive():
    for M in range(2, 13):
        for l in range(1, M):
            for n in range(1, M):
                res = ver.exact_dicke_moments(M, n, l)
                assert res["kappa4"] <= Fraction(3, 1)
                if res["kappa4"] == Fraction(3, 1):
                    assert (M, n, l) == (4, 2, 2)
                assert res["kappa6"] < Fraction(15, 1)
                assert Fraction(0, 1) <= res["excess_var"] < Fraction(6, 1)


def test_05_unique_kappa4_attainment_M4_n2_l2():
    res = ver.exact_dicke_moments(4, 2, 2)
    assert res["branch"] == "4l=2M"
    assert res["mu2"] == Fraction(8, 3)
    assert res["mu4"] == Fraction(64, 3)
    assert res["mu6"] == Fraction(512, 3)
    assert res["kappa4"] == Fraction(3, 1)
    assert res["kappa6"] == Fraction(9, 1)
    assert res["excess_var"] == Fraction(0, 1)


def test_06_operating_point_0495_sharp_ratios():
    c = load_cert("C09_")
    p_ratio = ver.parse_frac(c["psucc_sharpening_ratio"])
    inf_ratio = ver.parse_frac(c["infidelity_sharpening_ratio"])
    p_amp1 = ver.parse_frac(c["p_amp1_lb"])
    assert p_ratio > Fraction(379, 10)
    assert inf_ratio > Fraction(13, 1)
    assert p_amp1 > Fraction(9448, 10000)


def test_07_operating_point_045_certifies_1pct():
    c = load_cert("C10_")
    inf_ub = ver.parse_frac(c["infidelity_ub"])
    p_lb = ver.parse_frac(c["psucc_lb"])
    assert inf_ub < Fraction(1, 100)
    assert p_lb > Fraction(1614, 10000)
    assert p_lb * 160 > Fraction(25, 1)


def test_08_router_exhaustive_M7_onsager_and_dwc():
    for mask in range(1 << 7):
        x = [(mask >> i) & 1 for i in range(7)]
        ver.replay_reversible_router_single(x, "onsager")
        if sum(x) >= 1:
            ver.replay_reversible_router_single(x, "dwc")


# --- 28 Adversarial Forgery Tests ---

def test_forgery_01_wrong_schema():
    c = rehash({**load_cert("C01_"), "schema": "FAKE-SCHEMA-1.0"})
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(c)


def test_forgery_02_corrupted_sha256():
    c = load_cert("C01_")
    c["sha256"] = "0" * 64
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(c)


def test_forgery_03_missing_sha256():
    c = load_cert("C01_")
    del c["sha256"]
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(c)


def test_forgery_04_unknown_cert_type():
    c = rehash({**load_cert("C01_"), "cert_type": "bogus_type"})
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(c)


def test_forgery_05_bool_smuggled_as_M():
    c = rehash({**load_cert("C01_"), "M": True})
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(c)


def test_forgery_06_bool_smuggled_as_n():
    c = rehash({**load_cert("C01_"), "n": True})
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(c)


def test_forgery_07_bool_smuggled_in_fraction():
    c = rehash({**load_cert("C09_"), "s": [True, 2]})
    with pytest.raises(ValueError):
        ver.verify_certificate_dict(c)


def test_forgery_08_negative_fraction_denominator():
    c = rehash({**load_cert("C09_"), "s": [99, -200]})
    with pytest.raises(ValueError):
        ver.verify_certificate_dict(c)


def test_forgery_09_zero_fraction_denominator():
    c = rehash({**load_cert("C09_"), "s": [99, 0]})
    with pytest.raises(ValueError):
        ver.verify_certificate_dict(c)


def test_forgery_10_float_in_fraction():
    c = rehash({**load_cert("C09_"), "s": [0.495, 1]})
    with pytest.raises(ValueError):
        ver.verify_certificate_dict(c)


def test_forgery_11_wrong_branch_label():
    c = rehash({**load_cert("C01_"), "branch": "generic"})
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(c)


def test_forgery_12_tampered_kappa4():
    c = load_cert("C05_")
    c["kappa4"] = [3, 1]
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_13_tampered_kappa6():
    c = load_cert("C05_")
    c["kappa6"] = [15, 1]
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_14_tampered_excess_var():
    c = load_cert("C05_")
    c["excess_var"] = [6, 1]
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_15_tampered_asari_mu4_ratio():
    c = load_cert("C05_")
    c["asari_mu4_ratio"] = [99, 1]
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_16_out_of_range_l():
    c = rehash({**load_cert("C02_"), "l": 6})
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(c)


def test_forgery_17_operating_point_overshoot_s_ge_half():
    c = load_cert("C09_")
    c["s"] = [1, 2]
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_18_operating_point_negative_s():
    c = load_cert("C09_")
    c["s"] = [-1, 10]
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_19_tampered_infidelity_ub():
    c = load_cert("C09_")
    c["infidelity_ub"] = [1, 1000]
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_20_tampered_psucc_lb():
    c = load_cert("C09_")
    c["psucc_lb"] = [1, 5]
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_21_tampered_p_amp1_lb():
    c = load_cert("C09_")
    c["p_amp1_lb"] = [99, 100]
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_22_failed_target_eps():
    c = load_cert("C10_")
    c["target_eps"] = [1, 1000]
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_23_router_wrong_states_checked():
    c = load_cert("C13_")
    c["states_checked"] = 63
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_24_router_wrong_max_fredkin():
    c = load_cert("C13_")
    c["max_fredkin_gates"] = 1
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_25_router_scaling_tampered_our_fredkin():
    c = load_cert("C16_")
    c["rows"][0]["our_fredkin"] = 100
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_26_router_scaling_tampered_beats_conveyor():
    c = load_cert("C16_")
    c["rows"][0]["beats_conveyor"] = True
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))


def test_forgery_27_ast_rejects_float_source(tmp_path: Path):
    bad = tmp_path.joinpath("bad_float.py")
    bad.write_text("x = 0.495\n", encoding="utf-8")
    with pytest.raises(AssertionError):
        ver.ast_zero_float_audit(bad)


def test_forgery_28_ast_rejects_div_operator(tmp_path: Path):
    bad = tmp_path.joinpath("bad_div.py")
    bad.write_text("x = 1 / 2\n", encoding="utf-8")
    with pytest.raises(AssertionError):
        ver.ast_zero_float_audit(bad)


def test_forgery_29_router_bool_smuggling():
    # Even when a field equals 0 or 1 (e.g. DWC n=1 has max_fredkin_gates=0), bool must be rejected
    c = load_cert("C16_")
    c["rows"][0]["B"] = True
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c))
    c2 = load_cert("C14_")
    c2["max_fredkin_gates"] = False
    with pytest.raises(AssertionError):
        ver.verify_certificate_dict(rehash(c2))


def test_forgery_30_ast_rejects_builtin_pow_call(tmp_path: Path):
    bad = tmp_path.joinpath("bad_pow.py")
    bad.write_text("x = pow(2, -1)\n", encoding="utf-8")
    with pytest.raises(AssertionError):
        ver.ast_zero_float_audit(bad)
