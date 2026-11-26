#!/usr/bin/env python3
"""Run python check_quotient_lower.py to replay the terminal quotient checks."""

from fractions import Fraction
from itertools import combinations, permutations
from pathlib import Path
import sys

# The release repository keeps the original insertion counter under weighted-menus.
source_dir = Path(__file__).resolve().parent
if not (source_dir / "check_selection.py").is_file():
    sys.path.append(str(source_dir.parent / "weighted-menus"))
from check_selection import insertion_pass, inversions
from periodic_catalogues import compare_scores, ladder_terms


def run_prefix(state, gaps):
    cost = 0
    for gap in gaps:
        state, _, comparisons = insertion_pass(state, gap)
        cost += comparisons
    return state, cost


def check_execution(start, e, prefix):
    before, physical_prefix = run_prefix(start, prefix)
    ideal, _, _ = insertion_pass(start, e)
    base = inversions(ideal)
    target, final_shifts, final_cost = insertion_pass(before, 1)
    assert target == tuple(sorted(start))

    class_inversions = quotient_prefix = completion = 0
    for r in range(e):
        original = start[r::e]
        gaps = [h // e for h in prefix if h // e < len(original)]
        local, cost = run_prefix(original, gaps)
        assert local == before[r::e]
        quotient_prefix += cost
        class_inversions += inversions(local)
        if not gaps or gaps[-1] != 1:
            _, _, comparisons = insertion_pass(local, 1)
            completion += comparisons

    assert physical_prefix == quotient_prefix
    assert final_shifts >= base + class_inversions
    assert completion <= class_inversions + len(start)
    assert physical_prefix + final_cost >= base + quotient_prefix + completion - len(start)


def check_all_executions():
    total = with_e = ragged_identity = 0
    for n in range(2, 8):
        for e in range(2, min(n, 5) + 1):
            multiples = tuple(reversed(range(e, n, e)))
            for length in range(len(multiples) + 1):
                for prefix in combinations(multiples, length):
                    short_identity = n % e != 0 and (n // e) * e in prefix
                    for start in permutations(range(n)):
                        check_execution(start, e, prefix)
                        total += 1
                        with_e += e in prefix
                        ragged_identity += short_identity
    assert (total, with_e, ragged_identity) == (89060, 44454, 42270)
    print(f"{total} executions: {with_e} with e, {total-with_e} without e, "
          f"{ragged_identity} with an identity pass in a shorter class.")


def divisor_chains(d):
    """All strictly descending divisibility chains from d to 1."""
    if d == 1:
        yield (1,)
    for b in range(1, d):
        if d % b == 0:
            for tail in divisor_chains(b):
                yield (d,) + tail


def check_chain_coefficients():
    # Coefficients omit the common sqrt(pi)/8. An entry a: k means k/sqrt(a).
    assert ladder_terms(12, (6, 3, 1)) == {12: 1, 6: 1, 3: 2}
    assert ladder_terms(36, (12, 4, 1)) == {36: 2, 12: 2, 4: 3}
    chains = deletions = 0
    for d in range(2, 65):
        for chain in divisor_chains(d):
            full = ladder_terms(d, chain[1:])
            e = chain[-2]
            quotient = ladder_terms(d // e, [b // e for b in chain[1:-1]])
            # The quotient cost is divided by sqrt(e), then c_e is added.
            lifted = {a * e: k for a, k in quotient.items()}
            lifted[e] = e - 1
            assert compare_scores(lifted, full) == 0
            chains += 1

            for j in range(1, len(chain) - 1):
                D, b, t = chain[j-1:j+2]
                without = ladder_terms(d, chain[1:j] + chain[j+1:])
                # Exact deletion price (b-t)*(sqrt(D)-sqrt(b))/(t*b).
                factor = Fraction(b - t, t * b)
                expected = dict(full)
                expected[D] += D * factor
                expected[b] -= b * factor
                assert compare_scores(without, expected) == 0
                assert compare_scores(without, full) > 0
                deletions += 1
    print(f"{chains} chains through d=64 satisfy the quotient recurrence; "
          f"all {deletions} single deletions have the stated positive price.")


if __name__ == "__main__":
    check_all_executions()
    check_chain_coefficients()
