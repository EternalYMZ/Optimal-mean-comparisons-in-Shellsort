#!/usr/bin/env python3
"""Sample the gap tables of P04's periodic-catalogue theorem (standard library).

Example: python periodic_catalogues.py 1000000 210 30 42 70 105 --cutoff 100
Example: python periodic_catalogues.py 1000000 6 0 --exceptions 9 8 5 --cutoff 9
Run python periodic_catalogues.py --check for the finite execution checks.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, permutations
import json
from math import ceil, gcd, isqrt
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
    suffix: tuple[int, ...] = (1,)

    def prefix_length(self, rms):
        if self.divisor != 1:
            raise ValueError("the RMS prefix guarantee requires a primitive tail")
        if not 1 <= rms <= self.n:
            raise ValueError("RMS tolerance must lie in [1,n]")
        for length, error_bound in self.checkpoints:
            if error_bound <= rms:
                return length
        return len(self.gaps)  # Exact final pass.


def ladder_terms(divisor, gaps):
    """Score before the common sqrt(pi)/8 factor: sum(coeff[a] / sqrt(a))."""
    terms = {}
    a = divisor
    for b in gaps:
        after = gcd(a, b)
        if after < a:
            terms[a] = Fraction(a - after, b)
            a = after
    return terms


def compare_scores(left, right):
    """Compare exact sums of rational multiples of inverse square roots."""
    groups = {}
    for a in sorted(left.keys() | right.keys()):
        coefficient = left.get(a, 0) - right.get(a, 0)
        if not coefficient:
            continue
        for base in groups:
            common = gcd(a, base)
            num, den = a // common, base // common
            x, y = isqrt(num), isqrt(den)
            if x*x == num and y*y == den:
                # 1/sqrt(a) = (y/x)/sqrt(base).
                groups[base] += coefficient * Fraction(y, x)
                break
        else:
            groups[a] = coefficient

    groups = {a: c for a, c in groups.items() if c}
    if not groups:
        return 0
    # Different rational square classes give Q-linearly independent radicals.
    # Thus this nonzero sum is separated from zero at some finite precision.
    bits = 32
    while True:
        scale_squared = 1 << (2*bits)
        lo = hi = Fraction(0)
        for a, c in groups.items():
            low = isqrt(scale_squared // a)
            high = low + (low*low*a != scale_squared)
            lo += min(c*low, c*high)
            hi += max(c*low, c*high)
        if lo > 0:
            return 1
        if hi < 0:
            return -1
        bits *= 2


def prefer_ladder(divisor, candidate, incumbent):
    if incumbent is None:
        return True
    order = compare_scores(ladder_terms(divisor, candidate), ladder_terms(divisor, incumbent))
    if order:
        return order < 0
    if len(candidate) != len(incumbent):
        return len(candidate) < len(incumbent)
    return candidate > incumbent


def best_ladder(divisor, gaps):
    """Minimum guaranteed ladder score. Ties prefer short, then larger gaps."""
    if divisor < 1:
        raise ValueError("require a positive divisor")
    allowed = sorted(set(gaps), reverse=True)
    if any(b < 2 for b in allowed):
        raise ValueError("nonfinal gaps must be at least two")
    if divisor == 1:
        return (1,)
    paths = {divisor: ()}
    for b in allowed:
        # Use each available gap once, in execution order. Skipping it retains the state.
        for a, prefix in list(paths.items()):
            after = gcd(a, b)
            if after < a:
                candidate = prefix + (b,)
                if prefer_ladder(divisor, candidate, paths.get(after)):
                    paths[after] = candidate
    winner = None
    for prefix in paths.values():
        candidate = prefix + (1,)
        if prefer_ladder(divisor, candidate, winner):
            winner = candidate
    return winner


def sample_schedule(n, q, residues, cutoff=1, rng=None, exceptions=()):
    """Use the periodic tail strictly above cutoff, plus explicitly permitted exceptions.

    Pass an independent uniform integer sampler for the theorem's law.
    A seeded Random is available for reproducible examples.
    """
    if n < 2 or q < 1 or cutoff < 0:
        raise ValueError("require n >= 2, a positive period, and a nonnegative cutoff")
    residues = sorted(set(residues))
    if any(r < 0 or r >= q for r in residues):
        raise ValueError("residues must belong to [0,q)")
    exceptions = sorted(set(exceptions), reverse=True)
    if any(b < 2 for b in exceptions):
        raise ValueError("exceptional nonfinal gaps must be at least two")
    legal_exceptions = [b for b in exceptions if b < n]
    if not residues:
        suffix = (legal_exceptions[0], 1) if legal_exceptions else (1,)
        return Schedule(n, None, suffix, (), suffix)

    divisor = gcd(q, *residues)
    period = q // divisor
    allowed = [r // divisor for r in residues]
    size = (n + divisor - 1) // divisor
    suffix = best_ladder(divisor, legal_exceptions)
    largest_exception = legal_exceptions[0] if legal_exceptions else 1
    floor_center = period * max(2, max(cutoff, largest_exception) // q + 1)
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
    gaps.extend(suffix)
    return Schedule(n, divisor, tuple(gaps), tuple(checkpoints), suffix)


def check_ladders():
    assert compare_scores({2: Fraction(1)}, {8: Fraction(2)}) == 0
    assert compare_scores({2: Fraction(1) + Fraction(1, 10**90)}, {8: Fraction(2)}) > 0
    assert prefer_ladder(4, (5, 1), (5, 3, 1))
    assert prefer_ladder(1, (5, 1), (3, 1))
    assert best_ladder(6, [9, 8, 5]) == (9, 8, 1)
    cases = 0
    for d in (2, 3, 4, 6, 10, 12):
        for count in range(7):
            for available in combinations(range(7, 1, -1), count):
                best = None
                for length in range(count + 1):
                    for subword in combinations(available, length):
                        candidate = subword + (1,)
                        if prefer_ladder(d, candidate, best):
                            best = candidate
                assert best_ladder(d, available) == best
                if d == 2:
                    odd = max((h for h in available if h % 2), default=1)
                    assert best == ((odd, 1) if odd > 1 else (1,))
                cases += 1
    return cases


def check():
    rng = Random(271828)
    ladder_cases = check_ladders()
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
    finite = (20, 15, 8, 4)
    for n in range(2, 24):
        chosen = [b for b in finite if b < n]
        assert sample_schedule(n, 1, (), exceptions=finite).gaps == tuple(chosen[:1]) + (1,)
    legal_words = 0
    for n in (2, 7, 10, 31, 200, 3000):
        for d in (1, 2, 3, 6, 12):
            extras = (13, 9, 8, 5, 4)
            word = sample_schedule(n, d, [0], cutoff=8, rng=rng, exceptions=extras)
            assert word.gaps[-1] == 1 and word.gaps[0] < n
            assert all(a > b for a, b in zip(word.gaps, word.gaps[1:]))
            assert all(h in extras or (h > 8 and h % d == 0) for h in word.gaps[:-1])
            tail = len(word.gaps) - len(word.suffix)
            largest = max((b for b in extras if b < n), default=1)
            assert all(h > max(8, largest) for h in word.gaps[:tail])
            legal_words += 1

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

    # For parity the entire suffix must pay I(S_2 x) / largest permitted odd gap.
    parity_runs = 0
    general_runs = 0
    for n in range(2, 8):
        for state in permutations(range(n)):
            ideal = list(state)
            insertion_pass(ideal, 2)
            price = inversions(ideal)
            for length in range(n - 1):
                for gaps in combinations(range(n-1, 1, -1), length):
                    word = gaps + (1,)
                    largest_odd = max(h for h in word if h % 2)
                    z = list(state)
                    suffix_shifts = 0
                    for h in word:
                        moves, _ = insertion_pass(z, h)
                        if h <= largest_odd:
                            suffix_shifts += moves
                    assert largest_odd*suffix_shifts >= price
                    parity_runs += 1
            if n > 4:
                # d=3: divisible prefix followed by bounded exceptions.
                z = list(state)
                for h in range(n - 1, 4, -1):
                    if h % 3 == 0:
                        insertion_pass(z, h)
                ideal = list(state)
                insertion_pass(ideal, 3)
                price = sum(abs(i-rank) for i, rank in enumerate(ideal))
                moves = sum(insertion_pass(z, h)[0] for h in (4, 3, 2, 1))
                assert 2*4*moves >= price
                general_runs += 1

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
    print(f"{ladder_cases} exhaustive ladder optima, {legal_words} exception schedules, "
          f"{parity_runs} parity and {general_runs} divisor-three lower bounds verified.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="?")
    parser.add_argument("period", type=int, nargs="?")
    parser.add_argument("residues", type=int, nargs="*")
    parser.add_argument("--cutoff", type=int, default=1,
                        help="the periodic restriction is valid strictly above this gap")
    parser.add_argument("--rms", type=Fraction, help="requested RMS rank error on a primitive tail")
    parser.add_argument("--exceptions", type=int, nargs="*", default=None,
                        help="additional permitted nonfinal gaps; below cutoff list every permitted gap")
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
        law = sample_schedule(args.n, args.period, args.residues, args.cutoff, rng,
                              exceptions=args.exceptions or ())
        result = {"divisor": law.divisor, "gaps": law.gaps}
        if args.exceptions is not None:
            result["suffix"] = law.suffix
            if law.divisor is not None and law.divisor > 1:
                terms = ladder_terms(law.divisor, law.suffix)
                result["ladder_upper_terms"] = {str(a): str(c) for a, c in terms.items()}
        if args.rms is not None:
            result["prefix_length"] = law.prefix_length(args.rms)
    except ValueError as exc:
        parser.error(str(exc))
    print(json.dumps(result))


if __name__ == "__main__":
    main()
