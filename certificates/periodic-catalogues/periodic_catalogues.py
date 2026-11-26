#!/usr/bin/env python3
"""Sample the gap tables of P04's periodic-catalogue theorem (standard library).

Example: python periodic_catalogues.py 1000000 210 30 42 70 105 --cutoff 100
Run python periodic_catalogues.py --check for the finite execution checks.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, permutations
import json
from math import ceil, gcd
from random import Random, SystemRandom


def budget_constant(period, num_residues):
    """Smallest t with alpha <= 1/128; use an integer K >= max(4,16 beta)."""
    density = Fraction(period, num_residues)
    t = 0
    while True:
        D = 2**t
        m = 3*t + 3
        alpha = (2*m - 1)*density*8/D + Fraction(4*(1 + D*D), 2**m)
        if alpha <= Fraction(1, 128):
            beta = density*8*D + (2*m - 1)*density*(32 + Fraction(8, D)) + 4
            return max(4, ceil(16*beta))
        t += 1


@dataclass(frozen=True)
class Schedule:
    n: int
    divisor: int | None
    gaps: tuple[int, ...]
    # In decreasing order of guaranteed RMS error, each pair is (length, K*c).
    checkpoints: tuple[tuple[int, int], ...]

    def prefix_length(self, rms):
        if self.divisor != 1:
            raise ValueError("the RMS prefix guarantee requires a primitive tail")
        if not 1 <= rms <= self.n:
            raise ValueError("RMS tolerance must lie in [1,n]")
        for length, error_bound in self.checkpoints:
            if error_bound <= rms:
                return length
        return len(self.gaps)  # Exact final pass.


def sample_schedule(n, q, residues, cutoff=1, rng=None):
    """Only use gaps > cutoff in the periodic tail, then the mandatory 1.

    Pass an independent uniform integer sampler for the theorem's law.
    A seeded Random is available for reproducible examples.
    """
    if n < 2 or q < 1 or cutoff < 0:
        raise ValueError("require n >= 2, a positive period, and a nonnegative cutoff")
    residues = sorted(set(residues))
    if any(r < 0 or r >= q for r in residues):
        raise ValueError("residues must belong to [0,q)")
    if not residues:
        return Schedule(n, None, (1,), ())

    divisor = gcd(q, *residues)
    period = q // divisor
    allowed = [r // divisor for r in residues]
    size = (n + divisor - 1) // divisor
    floor_center = period * max(2, cutoff // divisor // period + 1)
    K = budget_constant(period, len(allowed)) if divisor == 1 else None

    centers = []
    c = floor_center
    while 4*c < size:
        centers.append(c)
        c *= 8

    if rng is None:
        rng = SystemRandom()
    gaps = []
    checkpoints = []
    for c in reversed(centers):
        gaps.append(divisor*(3*c + allowed[0] + period))
        gaps.extend(divisor*(3*c + r) for r in reversed(allowed))
        # The menu is a Cartesian product of complete periods and allowed residues.
        h = c + period*rng.randrange(c // period) + rng.choice(allowed)
        gaps.append(divisor*h)
        if K is not None:
            checkpoints.append((len(gaps), K*c))
    gaps.append(1)
    return Schedule(n, divisor, tuple(gaps), tuple(checkpoints))


def check():
    rng = Random(271828)
    catalogue_count = 0
    for period in range(1, 7):
        for k in range(1, period + 1):
            for residues in combinations(range(period), k):
                cutoff = period + 1
                schedule = sample_schedule(10000, period, residues, cutoff, rng)
                d = schedule.divisor
                assert d == gcd(period, *residues)
                prev = schedule.n
                for h in schedule.gaps[:-1]:
                    assert cutoff < h < prev and h % period in residues
                    prev = h
                assert schedule.gaps[-1] == 1 < prev
                width = k + 2
                assert (len(schedule.gaps) - 1) % width == 0
                for start in range(0, len(schedule.gaps) - 1, width):
                    block = schedule.gaps[start:start + width]
                    assert gcd(*block[:-1]) == d
                    c = (block[-2] // d - residues[0] // d) // 3
                    q = period // d
                    allowed = [r // d for r in residues]
                    menu = [h for h in range(c, 2*c) if h % q in allowed]
                    assert len(menu) == (c // q)*k and block[-1] // d in menu
                catalogue_count += 1

    hard = (30, 42, 70, 105)
    assert gcd(210, *hard) == 1
    for triple in combinations(hard, 3):
        assert gcd(210, *triple) > 1
    schedule = sample_schedule(2**65, 210, hard, rng=rng)
    assert len(schedule.checkpoints) > 2 and schedule.prefix_length(1) == len(schedule.gaps)
    for length, bound in schedule.checkpoints:
        if bound <= schedule.n:
            assert schedule.prefix_length(bound) == length
            assert schedule.prefix_length(bound - 1) > length
    assert schedule.prefix_length(schedule.n) < len(schedule.gaps)
    assert sample_schedule(1000, 7, ()).gaps == (1,)

    def inversions(word):
        return sum(a > b for i, a in enumerate(word) for b in word[i+1:])

    def insertion_pass(word, h):
        shifts = comparisons = 0
        for j in range(h, len(word)):
            pos, key = j, word[j]
            while pos >= h:
                comparisons += 1
                if word[pos-h] < key:
                    break
                word[pos] = word[pos-h]
                pos -= h
                shifts += 1
            word[pos] = key
        return shifts, comparisons

    executed = 0
    for n in range(2, 8):
        for permutation in permutations(range(n)):
            for B in (1, 3):
                # All nonfinal gaps > B in this test are even.
                z = list(permutation)
                for h in range(n-1, B, -1):
                    if h % 2 == 0:
                        insertion_pass(z, h)
                ideal = list(permutation)
                insertion_pass(ideal, 2)
                class_floor = inversions(ideal)
                previous = inversions(z)
                assert previous >= class_floor
                shifts = 0
                for h in range(min(B, n-1), 0, -1):
                    moves, comparisons = insertion_pass(z, h)
                    after = inversions(z)
                    assert moves <= previous - after <= (2*h-1)*moves
                    assert moves <= comparisons <= moves + n - h
                    previous = after
                    shifts += moves
                assert previous == 0 and (2*B-1)*shifts >= class_floor
                executed += 1

    # Lift one common quotient word onto ragged physical residue classes.
    n = 101
    lifted = sample_schedule(n, 6, [2, 4], rng=rng)
    assert lifted.divisor == 2 and len(lifted.gaps) > 1
    full = list(range(n))
    rng.shuffle(full)
    classes = [full[::2], full[1::2] + [n]]
    for gap in lifted.gaps[:-1]:
        insertion_pass(full, gap)
        for local in classes:
            insertion_pass(local, gap // 2)
        assert classes[0] == full[::2] and classes[1] == full[1::2] + [n]
    insertion_pass(full, 1)
    assert full == list(range(n))
    print(f"{catalogue_count} periodic catalogues, {executed} obstruction executions, "
          "and the 210, prefix-threshold and padded quotient checks passed.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="?")
    parser.add_argument("period", type=int, nargs="?")
    parser.add_argument("residues", type=int, nargs="*")
    parser.add_argument("--cutoff", type=int, default=1,
                        help="the periodic restriction is valid strictly above this gap")
    parser.add_argument("--rms", type=Fraction, help="requested RMS rank error on a primitive tail")
    parser.add_argument("--seed", type=int, help="seed a reproducible pseudorandom example")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.check:
        check()
        return
    if args.n is None or args.period is None:
        parser.error("supply n, period and any allowed residues, or --check")
    try:
        rng = Random(args.seed) if args.seed is not None else None
        law = sample_schedule(args.n, args.period, args.residues, args.cutoff, rng)
        result = {"divisor": law.divisor, "gaps": law.gaps}
        if args.rms is not None:
            result["prefix_length"] = law.prefix_length(args.rms)
    except ValueError as exc:
        parser.error(str(exc))
    print(json.dumps(result))


if __name__ == "__main__":
    main()
