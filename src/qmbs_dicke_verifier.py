"""
Zero-float exact rational verifier for Paper 98 (schema: QMBS-DICKE-SHARP-1.0).

Independently verifies:
  1. AST self-audit: zero floating-point/complex literals, zero division (`/`),
     zero exponentiation (`**`), zero float-based libraries, zero `eval`/`exec`.
  2. `exact_moment_cert`: exact without-replacement Dicke-state moments mu2, mu4, mu6,
     kurtosis kappa4 <= 3, sixth-moment ratio kappa6 < 15, excess variance
     kappa6 - kappa4^2 < 6, and exact sharpening ratios vs Asari et al. (arXiv:2611.33987).
  3. `operating_point_cert`: exact rational verification of optimal-projection uniform
     infidelity bound s^4*(4 + 3*s^2)/(6*(2 - s^2)^2), success probability envelope
     [s^2 - s^4, s^2], single-round Grover amplification p_amp^(1) = p_lb*(3 - 4*p_lb)^2,
     and exact improvement ratios over Asari et al. Eqs. (S9), (S11), and (S15).
  4. `reversible_router_cert`: exact gate-by-gate reversible MSB-to-LSB binary-shift
     routing replay (zero target collisions, zero ancilla leakage, exact spacer expansion,
     exact Fredkin gate formula B*(B*L - 2^B + 1) vs conveyor).
"""

from __future__ import annotations

import ast
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

SCHEMA_ID = "QMBS-DICKE-SHARP-1.0"

FORBIDDEN_IMPORTS = {
    "math",
    "cmath",
    "decimal",
    "numpy",
    "scipy",
    "sympy",
    "mpmath",
    "statistics",
}
FORBIDDEN_CALLS = {"float", "complex", "eval", "exec", "from_float", "from_decimal", "pow"}


def is_strict_int(val: object) -> bool:
    return isinstance(val, int) and not isinstance(val, bool)


def parse_frac(obj: object) -> Fraction:
    if is_strict_int(obj):
        return Fraction(obj, 1)
    if (
        isinstance(obj, list)
        and len(obj) == 2
        and is_strict_int(obj[0])
        and is_strict_int(obj[1])
        and obj[1] > 0
    ):
        return Fraction(obj[0], obj[1])
    raise ValueError(f"Invalid exact rational encoding: {obj!r}")


def pow_int(base: int, exp: int) -> int:
    if not is_strict_int(base) or not is_strict_int(exp) or exp < 0:
        raise ValueError("pow_int requires integer base and non-negative integer exp")
    res = 1
    b = base
    e = exp
    while e > 0:
        if (e & 1) == 1:
            res = res * b
        b = b * b
        e = e >> 1
    return res


def pow_frac(base: Fraction, exp: int) -> Fraction:
    if not is_strict_int(exp) or exp < 0:
        raise ValueError("pow_frac requires non-negative integer exp")
    return Fraction(pow_int(base.numerator, exp), pow_int(base.denominator, exp))


def div_frac(a: Fraction, b: Fraction) -> Fraction:
    if b.numerator == 0:
        raise ZeroDivisionError("Division by zero in exact rational arithmetic")
    return Fraction(a.numerator * b.denominator, a.denominator * b.numerator)


def canonical_json_bytes(data: dict) -> bytes:
    cleaned = {k: v for k, v in data.items() if k != "sha256"}
    return json.dumps(cleaned, sort_keys=True, separators=(",", ":")).encode("utf-8")


def compute_cert_sha256(data: dict) -> str:
    return hashlib.sha256(canonical_json_bytes(data)).hexdigest()


def ast_zero_float_audit(filepath: Path) -> None:
    source = filepath.read_text(encoding="utf-8")
    tree = ast.parse(source, filename=str(filepath))
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant):
            if isinstance(node.value, (float, complex)):
                raise AssertionError(
                    f"AST audit failed at line {node.lineno}: forbidden float/complex constant {node.value!r}"
                )
        elif isinstance(node, ast.Import):
            for alias in node.names:
                root_mod = alias.name.split(".")[0]
                if root_mod in FORBIDDEN_IMPORTS:
                    raise AssertionError(
                        f"AST audit failed at line {node.lineno}: forbidden import {alias.name!r}"
                    )
        elif isinstance(node, ast.ImportFrom):
            if node.module:
                root_mod = node.module.split(".")[0]
                if root_mod in FORBIDDEN_IMPORTS:
                    raise AssertionError(
                        f"AST audit failed at line {node.lineno}: forbidden import from {node.module!r}"
                    )
        elif isinstance(node, ast.Call):
            fn = node.func
            name = None
            if isinstance(fn, ast.Name):
                name = fn.id
            elif isinstance(fn, ast.Attribute):
                name = fn.attr
            if name in FORBIDDEN_CALLS:
                raise AssertionError(
                    f"AST audit failed at line {node.lineno}: forbidden call {name!r}"
                )
        elif isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Div, ast.Pow)):
            raise AssertionError(
                f"AST audit failed at line {node.lineno}: forbidden operator {type(node.op).__name__}"
            )
        elif isinstance(node, ast.AugAssign) and isinstance(node.op, (ast.Div, ast.Pow)):
            raise AssertionError(
                f"AST audit failed at line {node.lineno}: forbidden augassign {type(node.op).__name__}"
            )


def cosine_power_sums_exact(M: int, l: int) -> tuple[str, Fraction, Fraction, Fraction, Fraction]:
    """
    Exact power sums p_k = sum_{j=1}^M cos(pi*l*(2j-1)/(2M))^k from Asari et al. Eq. (S4).
    """
    if not (is_strict_int(M) and is_strict_int(l) and M >= 2 and 1 <= l <= M - 1):
        raise ValueError("Invalid (M, l) parameters")
    p2 = Fraction(M, 2)
    if 4 * l == 2 * M:
        return "4l=2M", p2, Fraction(0, 1), Fraction(M, 4), Fraction(M, 8)
    if 6 * l == 2 * M:
        return "6l=2M", p2, Fraction(0, 1), Fraction(3 * M, 8), Fraction(9 * M, 32)
    if 3 * l == 2 * M:
        return "3l=2M", p2, Fraction(-M, 4), Fraction(3 * M, 8), Fraction(11 * M, 32)
    return "generic", p2, Fraction(0, 1), Fraction(3 * M, 8), Fraction(5 * M, 16)


def falling_ratio(M: int, n: int, r: int) -> Fraction:
    if r > n:
        return Fraction(0, 1)
    num = 1
    den = 1
    for i in range(r):
        num = num * (n - i)
        den = den * (M - i)
    return Fraction(num, den)


def exact_dicke_moments(M: int, n: int, l: int) -> dict:
    """
    Exact rational replay of <Z(l)^2>, <Z(l)^4>, <Z(l)^6> on Dicke state |D_n^M>.
    Uses first-principles falling-factorial inclusion-exclusion from p_1=0, p_2, p_3, p_4, p_6.
    """
    if not (is_strict_int(n) and 1 <= n <= M - 1):
        raise ValueError("Invalid n for Dicke state")
    branch, p2, p3, p4, p6 = cosine_power_sums_exact(M, l)

    a1 = falling_ratio(M, n, 1)
    a2 = falling_ratio(M, n, 2)
    a3 = falling_ratio(M, n, 3)
    a4 = falling_ratio(M, n, 4)
    a5 = falling_ratio(M, n, 5)
    a6 = falling_ratio(M, n, 6)

    mu2 = 4 * (a1 * p2 - a2 * p2)

    p2_sq = p2 * p2
    s4 = p4
    s31 = -p4
    s22 = p2_sq - p4
    s211 = 2 * p4 - p2_sq
    s1111 = 3 * p2_sq - 6 * p4
    mu4 = 16 * (a1 * s4 + a2 * (4 * s31 + 3 * s22) + a3 * (6 * s211) + a4 * s1111)

    p2_cu = p2_sq * p2
    p3_sq = p3 * p3
    p4_p2 = p4 * p2
    s6 = p6
    s51 = -p6
    s42 = p4_p2 - p6
    s33 = p3_sq - p6
    s411 = 2 * p6 - p4_p2
    s321 = 2 * p6 - p4_p2 - p3_sq
    s222 = p2_cu - 3 * p4_p2 + 2 * p6
    s3111 = -6 * p6 + 3 * p4_p2 + 2 * p3_sq
    s2211 = -6 * p6 + 5 * p4_p2 + 2 * p3_sq - p2_cu
    s21111 = 24 * p6 - 18 * p4_p2 - 8 * p3_sq + 3 * p2_cu
    s111111 = -120 * p6 + 90 * p4_p2 + 40 * p3_sq - 15 * p2_cu

    # Inclusion-exclusion conservation check: total sum = p_1^6 = 0
    if (
        s6
        + 6 * s51
        + 15 * s42
        + 10 * s33
        + 15 * s411
        + 60 * s321
        + 15 * s222
        + 20 * s3111
        + 45 * s2211
        + 15 * s21111
        + s111111
        != 0
    ):
        raise AssertionError("k=6 partition conservation identity failed")

    mu6 = 64 * (
        a1 * s6
        + a2 * (6 * s51 + 15 * s42 + 10 * s33)
        + a3 * (15 * s411 + 60 * s321 + 15 * s222)
        + a4 * (20 * s3111 + 45 * s2211)
        + a5 * (15 * s21111)
        + a6 * s111111
    )

    k4 = div_frac(mu4, mu2 * mu2)
    k6 = div_frac(mu6, mu2 * mu2 * mu2)
    excess_var = k6 - k4 * k4

    # Cross-check exact closed-form kurtosis formula for M >= 4
    if branch != "4l=2M" and M >= 3:
        k4_cf = Fraction(3 * (M - 1) * (2 * n * (M - n) - M), 2 * n * (M - n) * (M - 2))
        if k4 != k4_cf:
            raise AssertionError("Closed-form kurtosis mismatch (generic branch)")
    elif branch == "4l=2M" and M >= 4:
        k4_cf = Fraction((M - 1) * (3 * n * (M - n) - 2 * M), n * (M - n) * (M - 3))
        if k4 != k4_cf:
            raise AssertionError("Closed-form kurtosis mismatch (4l=2M branch)")

    return {
        "branch": branch,
        "mu2": mu2,
        "mu4": mu4,
        "mu6": mu6,
        "kappa4": k4,
        "kappa6": k6,
        "excess_var": excess_var,
    }


def verify_exact_moment_cert(cert: dict) -> None:
    M = cert["M"]
    n = cert["n"]
    l = cert["l"]
    if not (is_strict_int(M) and is_strict_int(n) and is_strict_int(l)):
        raise AssertionError("M, n, l must be strict integers")
    if not (M >= 2 and 1 <= n <= M - 1 and 1 <= l <= M - 1):
        raise AssertionError("Out-of-range (M, n, l)")

    res = exact_dicke_moments(M, n, l)
    if cert["branch"] != res["branch"]:
        raise AssertionError(f"Branch mismatch: {cert['branch']} != {res['branch']}")

    for key in ("mu2", "mu4", "mu6", "kappa4", "kappa6", "excess_var"):
        claimed = parse_frac(cert[key])
        if claimed != res[key]:
            raise AssertionError(f"{key} mismatch: {claimed} != {res[key]}")

    # Universal Theorem A bounds
    if res["kappa4"] > Fraction(3, 1):
        raise AssertionError("Theorem A violation: kappa4 > 3")
    if res["kappa4"] == Fraction(3, 1) and not (M == 4 and n == 2 and l == 2):
        raise AssertionError("Unexpected equality kappa4 = 3 outside (4, 2, 2)")
    if res["kappa6"] >= Fraction(15, 1):
        raise AssertionError("Theorem A violation: kappa6 >= 15")
    if res["excess_var"] >= Fraction(6, 1):
        raise AssertionError("Theorem A violation: kappa6 - kappa4^2 >= 6")
    if res["excess_var"] < Fraction(0, 1):
        raise AssertionError("Negative variance kappa6 - kappa4^2 < 0")

    # Compare against Asari et al. Hoeffding bounds (using n_eff = min(n, M - n))
    n_eff = n if 2 * n <= M else M - n
    asari_mu4 = Fraction(12 * n_eff * n_eff, 1)
    asari_mu6 = Fraction(120 * n_eff * n_eff * n_eff, 1)
    if res["mu4"] > asari_mu4 or res["mu6"] > asari_mu6:
        raise AssertionError("Exact moment exceeds Asari Hoeffding bound")
    if parse_frac(cert["asari_mu4_ratio"]) != div_frac(asari_mu4, res["mu4"]):
        raise AssertionError("asari_mu4_ratio mismatch")
    if parse_frac(cert["asari_mu6_ratio"]) != div_frac(asari_mu6, res["mu6"]):
        raise AssertionError("asari_mu6_ratio mismatch")


def verify_operating_point_cert(cert: dict) -> None:
    s = parse_frac(cert["s"])
    if not (s > Fraction(0, 1) and s * s < Fraction(2, 1)):
        raise AssertionError("Operating point s must satisfy 0 < s < sqrt(2)")

    s2 = s * s
    s4 = s2 * s2

    # Theorem B universal uniform infidelity upper bound: s^4*(4 + 3*s^2) / (6*(2 - s^2)^2)
    inf_ub = div_frac(s4 * (4 + 3 * s2), 6 * (2 - s2) * (2 - s2))
    asari_inf_ub = Fraction(10, 3) * s4
    inf_ratio = div_frac(asari_inf_ub, inf_ub)

    # Theorem B universal success-probability envelope [s^2 - s^4, s^2]
    p_lb = s2 - s4
    p_ub = s2
    asari_p_lb = s2 - 4 * s4

    if parse_frac(cert["infidelity_ub"]) != inf_ub:
        raise AssertionError("infidelity_ub mismatch")
    if parse_frac(cert["asari_infidelity_ub"]) != asari_inf_ub:
        raise AssertionError("asari_infidelity_ub mismatch")
    if parse_frac(cert["infidelity_sharpening_ratio"]) != inf_ratio:
        raise AssertionError("infidelity_sharpening_ratio mismatch")
    if parse_frac(cert["psucc_lb"]) != p_lb:
        raise AssertionError("psucc_lb mismatch")
    if parse_frac(cert["psucc_ub"]) != p_ub:
        raise AssertionError("psucc_ub mismatch")
    if parse_frac(cert["asari_psucc_lb"]) != asari_p_lb:
        raise AssertionError("asari_psucc_lb mismatch")

    if p_lb <= Fraction(0, 1):
        raise AssertionError("Non-positive psucc_lb")
    if p_ub >= Fraction(1, 4):
        raise AssertionError("psucc_ub >= 1/4: zero-overshoot K=1 monotonicity requires p_ub < 1/4")

    # Exact K=1 Grover amplified success probability lower bound: p_lb * (3 - 4*p_lb)^2
    p_amp1_lb = p_lb * (3 - 4 * p_lb) * (3 - 4 * p_lb)
    if parse_frac(cert["p_amp1_lb"]) != p_amp1_lb:
        raise AssertionError("p_amp1_lb mismatch")

    if asari_p_lb > Fraction(0, 1):
        p_ratio = div_frac(p_lb, asari_p_lb)
        if parse_frac(cert["psucc_sharpening_ratio"]) != p_ratio:
            raise AssertionError("psucc_sharpening_ratio mismatch")
        asari_amp1_lb = asari_p_lb * (3 - 4 * asari_p_lb) * (3 - 4 * asari_p_lb)
        if parse_frac(cert["asari_p_amp1_lb"]) != asari_amp1_lb:
            raise AssertionError("asari_p_amp1_lb mismatch")

    if "target_eps" in cert:
        eps = parse_frac(cert["target_eps"])
        if inf_ub > eps:
            raise AssertionError(f"Operating point fails target_eps: {inf_ub} > {eps}")


def replay_reversible_router_single(x: list[int], mode: str) -> tuple[list[int], int, int]:
    """
    Exact gate-by-gate reversible MSB-to-LSB binary-shift circuit replay.
    Checks:
      - zero collisions (target control bit strictly 0 before every swap),
      - exact output bitstring matching spacer insertion,
      - zero ancilla leakage after spacer-masked prefix-sum uncomputation,
      - exact Fredkin gate count B*(B*L - (2^B - 1)).
    """
    Mp = len(x)
    nw = sum(x)
    if mode == "onsager":
        L = Mp + nw
        B = nw.bit_length() if nw > 0 else 1
    elif mode == "dwc":
        if nw < 1:
            raise ValueError("DWC router requires weight n >= 1")
        L = Mp + nw - 1
        B = (nw - 1).bit_length() if nw > 1 else 0
    else:
        raise ValueError(f"Unknown router mode: {mode}")

    bit = [0] * L
    reg = [[0] * B for _ in range(L)]
    for j in range(Mp):
        bit[j] = x[j]

    # Step 1: Exclusive prefix weight computation
    pref = 0
    for j in range(Mp):
        shift = pref if mode == "onsager" else (pref if pref < nw - 1 else nw - 1)
        for r in range(B):
            reg[j][r] = reg[j][r] ^ ((shift >> r) & 1)
        pref = pref + bit[j]

    # Step 2: MSB-to-LSB controlled-SWAP (Fredkin) + unconditional SWAP stages
    fredkin_count = 0
    swap_count = 0
    for b in range(B - 1, -1, -1):
        step = 1 << b
        for p in range(L - 1 - step, -1, -1):
            if reg[p + step][b] != 0:
                raise AssertionError(f"Collision: target reg[{p + step}][{b}] != 0")
            if reg[p][b] == 1:
                bit[p], bit[p + step] = bit[p + step], bit[p]
                for r in range(B):
                    if r != b:
                        reg[p][r], reg[p + step][r] = reg[p + step][r], reg[p][r]
            fredkin_count = fredkin_count + B
            reg[p][b], reg[p + step][b] = reg[p + step][b], reg[p][b]
            swap_count = swap_count + 1

    # Step 3: Exact spacer-masked prefix-sum uncomputation
    pref_out = 0
    for p in range(L):
        if mode == "onsager":
            is_spacer = p > 0 and bit[p - 1] == 1
            shift_out = pref_out
        else:
            is_spacer = p > 0 and bit[p - 1] == 1 and pref_out < nw
            shift_out = pref_out if pref_out < nw - 1 else nw - 1
        if not is_spacer:
            for r in range(B):
                reg[p][r] = reg[p][r] ^ ((shift_out >> r) & 1)
        pref_out = pref_out + bit[p]

    for p in range(L):
        for r in range(B):
            if reg[p][r] != 0:
                raise AssertionError(f"Ancilla leak at slot {p}, bit {r}")

    # Verify exact output specification
    if mode == "onsager":
        expected = []
        for v in x:
            expected.append(v)
            if v == 1:
                expected.append(0)
        if bit != expected:
            raise AssertionError("Onsager output bitstring mismatch")
    else:
        ones_in = [j for j in range(Mp) if x[j] == 1]
        ones_out = [p for p in range(L) if bit[p] == 1]
        expected_pos = [ones_in[idx] + idx for idx in range(len(ones_in))]
        if ones_out != expected_pos:
            raise AssertionError("DWC non-adjacent excitation positions mismatch")

    expected_fredkin = B * (B * L - ((1 << B) - 1)) if B > 0 else 0
    if fredkin_count != expected_fredkin:
        raise AssertionError("Fredkin gate count formula mismatch")
    return bit, fredkin_count, swap_count


def verify_reversible_router_cert(cert: dict) -> None:
    subtype = cert["subtype"]
    if subtype == "exhaustive_replay":
        mode = cert["mode"]
        Mp = cert["Mp"]
        fixed_n = cert.get("fixed_n", None)
        if not is_strict_int(Mp) or Mp < 2 or Mp > 12:
            raise AssertionError("Invalid Mp for exhaustive replay")
        if fixed_n is not None and not is_strict_int(fixed_n):
            raise AssertionError("fixed_n must be strict int or null")

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
            states_checked = states_checked + 1

        if not is_strict_int(cert.get("states_checked")) or cert["states_checked"] != states_checked:
            raise AssertionError(
                f"states_checked mismatch: {cert.get('states_checked')!r} != {states_checked}"
            )
        if not is_strict_int(cert.get("max_fredkin_gates")) or cert["max_fredkin_gates"] != max_fredkin:
            raise AssertionError(
                f"max_fredkin_gates mismatch: {cert.get('max_fredkin_gates')!r} != {max_fredkin}"
            )
    elif subtype == "macroscopic_scaling":
        rows = cert["rows"]
        if not isinstance(rows, list) or len(rows) == 0:
            raise AssertionError("Empty macroscopic scaling rows")
        for row in rows:
            Mp = row["Mp"]
            nw = row["n"]
            if not (is_strict_int(Mp) and is_strict_int(nw) and 1 <= nw < Mp):
                raise AssertionError("Invalid (Mp, n) in scaling row")
            L = Mp + nw
            B = nw.bit_length()
            our_fredkin = B * (B * L - ((1 << B) - 1))
            conv_fredkin = (nw * (2 * Mp - nw - 1)) // 2
            speedup = Fraction(conv_fredkin, our_fredkin)
            if not (is_strict_int(row.get("L")) and is_strict_int(row.get("B"))):
                raise AssertionError("L and B must be strict ints in scaling row")
            if row["L"] != L or row["B"] != B:
                raise AssertionError("L or B mismatch in scaling row")
            if not (is_strict_int(row.get("our_fredkin")) and is_strict_int(row.get("conveyor_fredkin"))):
                raise AssertionError("Fredkin counts must be strict ints in scaling row")
            if row["our_fredkin"] != our_fredkin:
                raise AssertionError("our_fredkin mismatch in scaling row")
            if row["conveyor_fredkin"] != conv_fredkin:
                raise AssertionError("conveyor_fredkin mismatch in scaling row")
            if parse_frac(row["speedup"]) != speedup:
                raise AssertionError("speedup mismatch in scaling row")
            if row["beats_conveyor"] is not (our_fredkin < conv_fredkin):
                raise AssertionError("beats_conveyor boolean mismatch")
    else:
        raise AssertionError(f"Unknown router cert subtype: {subtype!r}")


def verify_certificate_dict(cert: dict) -> None:
    if not isinstance(cert, dict):
        raise AssertionError("Certificate must be a JSON object")
    if cert.get("schema") != SCHEMA_ID:
        raise AssertionError(f"Schema mismatch: expected {SCHEMA_ID}, got {cert.get('schema')!r}")
    if "sha256" not in cert or not isinstance(cert["sha256"], str):
        raise AssertionError("Missing sha256 field")
    expected_hash = compute_cert_sha256(cert)
    if cert["sha256"] != expected_hash:
        raise AssertionError(f"SHA-256 mismatch: {cert['sha256']} != {expected_hash}")

    ctype = cert.get("cert_type")
    if ctype == "exact_moment_cert":
        verify_exact_moment_cert(cert)
    elif ctype == "operating_point_cert":
        verify_operating_point_cert(cert)
    elif ctype == "reversible_router_cert":
        verify_reversible_router_cert(cert)
    else:
        raise AssertionError(f"Unknown cert_type: {ctype!r}")


def verify_directory(cert_dir: Path) -> int:
    ast_zero_float_audit(Path(__file__).resolve())
    manifest_path = cert_dir.joinpath("MANIFEST.sha256")
    if not manifest_path.is_file():
        raise AssertionError("Missing MANIFEST.sha256")

    manifest_entries: dict[str, str] = {}
    for line in manifest_path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        parts = line.split("  ")
        if len(parts) != 2:
            raise AssertionError(f"Malformed MANIFEST line: {line!r}")
        manifest_entries[parts[1]] = parts[0]

    json_files = sorted(cert_dir.glob("*.json"))
    if len(json_files) == 0:
        raise AssertionError("No certificate JSON files found")
    if set(f.name for f in json_files) != set(manifest_entries.keys()):
        raise AssertionError("MANIFEST file list does not match JSON directory contents")

    for jf in json_files:
        raw_bytes = jf.read_bytes()
        file_sha = hashlib.sha256(raw_bytes).hexdigest()
        if file_sha != manifest_entries[jf.name]:
            raise AssertionError(f"MANIFEST SHA-256 mismatch for {jf.name}")
        cert = json.loads(raw_bytes.decode("utf-8"))
        verify_certificate_dict(cert)

    return len(json_files)


def main() -> int:
    if len(sys.argv) != 2:
        print("Usage: python qmbs_dicke_verifier.py <certificates_dir>", file=sys.stderr)
        return 2
    cert_dir = Path(sys.argv[1])
    count = verify_directory(cert_dir)
    print(f"AST zero-float self-audit PASS | {count}/{count} {SCHEMA_ID} certificates + MANIFEST PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
