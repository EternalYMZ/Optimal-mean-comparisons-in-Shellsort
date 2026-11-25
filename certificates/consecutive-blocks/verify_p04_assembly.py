#!/usr/bin/env python3
"""Exact rational certificate for P04 Section 6, the scale assembly."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path


def certificate():
    r, a = F(107, 50), F(94, 57)
    rho = r ** 3
    beta, K = 2 ** 24, 19 * 2 ** 24
    b = [1]
    for _ in range(6):
        b.append((107 * b[-1] + 94) // 50)
    s = [v + a for v in b]
    assert (r - 1) * a == F(94, 50)
    contraction = rho ** 2 / 200 + rho / 19
    assert contraction == F(59139951685131, 59375000000000)
    assert contraction < 1

    gamma = {
        "center_1": F(17, 30) * s[3],
        "center_4": (2*s[4]/23 + 2*s[4]/10 + (s[4]+s[1])/2)/3,
        "center_10": (2*s[5]/51 + 2*s[5]/23 + (s[5]+s[2])/5)/3,
        "center_23": (2*s[6]/111 + 2*s[6]/51 + (s[6]+s[3])/12)/3,
    }
    expected = {
        "center_1": F(4777, 342),
        "center_4": F(580211, 39330),
        "center_10": F(2612449, 200583),
        "center_23": F(7718741, 645354),
    }
    assert gamma == expected
    tail1, tail2 = s[1], F(3, 4)*s[2]
    assert tail1 == F(322, 57) and tail2 == F(166, 19)
    large = F(2, 3)*(1+a/23)*(r+r*r+rho+1)
    assert large == F(615388033, 49162500) and large < 13
    groups = {
        "last_4_passes": (3*gamma["center_4"]+tail1)/4,
        "last_5_passes": (3*gamma["center_10"]+2*tail2)/5,
        "last_6_passes": (gamma["center_23"]+gamma["center_1"])/2,
    }
    assert groups["last_4_passes"] == F(654271, 52440)
    assert groups["last_5_passes"] == F(3780757, 334305)
    assert groups["last_6_passes"] == F(4183235, 322677)
    assert all(v < 13 for v in groups.values())
    assert 2*b[3] == 46 and 23 < 1 + 13*K
    total = 1 + 13*K
    assert total == 4143972353 and total < 2 ** 32
    return {
        "passed": True,
        "exact_arithmetic": True,
        "scope": "Finite scalar inequalities in manuscript Section 6.",
        "shift": str(a),
        "three_step_ratio": str(rho),
        "beta": beta,
        "K": K,
        "contraction_factor": str(contraction),
        "contraction_slack": str(1-contraction),
        "small_block_coefficients": {k:str(v) for k,v in gamma.items()},
        "tail_1_per_pass": str(tail1),
        "tail_2_per_pass": str(tail2),
        "large_center_per_pass": str(large),
        "last_group_per_pass": {k:str(v) for k,v in groups.items()},
        "total_coefficient": total,
        "clean_upper_coefficient": 2 ** 32,
        "bound": "E C <= 4143972353 n log_2(n) < 2^32 n log_2(n)",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(certificate(), ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.write_text(result)
    print(result)
