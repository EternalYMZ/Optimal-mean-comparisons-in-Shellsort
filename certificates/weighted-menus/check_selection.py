"""Replay the shared-sample proof's scalar bounds and small executed examples."""
from fractions import Fraction
from itertools import combinations, permutations
from math import factorial


def inversions(state):
    return sum(a > b for i, a in enumerate(state) for b in state[i + 1:])


def insertion_pass(state, gap):
    state = list(state)
    shifts = comparisons = 0
    for end in range(gap, len(state)):
        key = state[end]
        pos = end
        while pos >= gap:
            comparisons += 1
            if state[pos - gap] < key:
                break
            state[pos] = state[pos - gap]
            shifts += 1
            pos -= gap
        state[pos] = key
    return tuple(state), shifts, comparisons


def check():
    # Alternating expansion of log(1 + x) at x = 1/3.
    x = Fraction(1, 3)
    log_lo = x - x**2 / 2
    log_hi = log_lo + x**3 / 3
    assert 3 * log_lo - Fraction(2, 3) > Fraction(1, 8)
    assert 1 - 3 * log_hi > Fraction(1, 8)
    assert Fraction(9, 10)**10 < Fraction(1, 2)

    runs = 0
    for n in range(2, 7):
        target = tuple(range(n))
        tables = [tuple(reversed(gaps)) + (1,)
                  for k in range(n - 1) for gaps in combinations(range(2, n), k)]
        for start in permutations(target):
            initial = inversions(start)
            for table in tables:
                state = start
                remaining = initial
                cost = 0
                for gap in table:
                    state, shifts, comparisons = insertion_pass(state, gap)
                    after = inversions(state)
                    assert shifts <= remaining - after
                    assert shifts <= comparisons <= shifts + n - gap
                    remaining = after
                    cost += comparisons
                assert state == target and cost <= initial + n * len(table)
                runs += 1
    expected = sum(2**(n - 2) * factorial(n) for n in range(2, 7))
    assert runs == expected
    print(f"{runs} input-table pairs checked through n=6; both tail constants and cap verified.")


if __name__ == "__main__":
    check()
