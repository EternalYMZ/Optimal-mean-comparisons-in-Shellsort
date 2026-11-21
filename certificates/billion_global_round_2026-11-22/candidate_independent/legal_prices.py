"""Count locally legal insertion records using exact integer weights."""

from fractions import Fraction
from functools import cache
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "billion_joint_2026-11-22/family"))
from records import logs, smooth

N = 10**9
BUDGET = 50 * N
ANCHOR = 48_414_727_652
BASE = Fraction(1, 8)
SMOOTH = smooth(N, (11, 12))


def allowed_distances(n, earlier, h):
    """Use every established distance, including mixed sums of old gaps."""
    distances = {0}
    for g in sorted(earlier, reverse=True):
        distances = {a + i * g for a in distances for i in range((n - 1 - a)//g + 1)}
    return tuple(d // h for d in sorted(distances) if d and d % h == 0)


@cache
def ideals(length, distances):
    full = (1 << length) - 1
    predecessor_masks = [sum(1 << (q - d) for d in distances if d <= q)
                         for q in range(length)]
    levels = [{0: []}]
    for _ in range(length):
        upcoming = {}
        for chosen, transitions in levels[-1].items():
            remaining = full ^ chosen
            while remaining:
                bit = remaining & -remaining
                remaining -= bit
                q = bit.bit_length() - 1
                if chosen & predecessor_masks[q] != predecessor_masks[q]:
                    continue
                smaller = (chosen & (bit - 1)).bit_count()
                extra = min(q - smaller, max(0, q - 1))
                target = chosen | bit
                upcoming.setdefault(target, [])
                transitions.append((target, q, extra))
        levels.append(upcoming)
    assert levels[-1] == {full: []}
    return levels


def weighted(length, distances, t):
    """Compute the exact probability that a product-priced record is locally feasible."""
    a, b = t.numerator, t.denominator
    dense = [[a**e * b**(max(0, q - 1) - e) for e in range(max(0, q - 1) + 1)]
             for q in range(length)]
    total = 1
    for q in range(1, length):
        total *= sum(dense[q][min(j, q - 1)] for j in range(q + 1))
    values = {0: 1}
    for level in ideals(length, distances)[:-1]:
        next_values = {}
        for chosen, transitions in level.items():
            partial = values[chosen]
            for target, q, extra in transitions:
                current = next_values.get(target, 0)
                next_values[target] = current + partial * dense[q][extra]
        values = next_values
    [valid] = values.values()
    assert 0 < valid <= total
    return Fraction(valid, total)


def log_capacity(gaps, t, upper):
    total = Fraction(0)
    for index in gaps:
        h = SMOOTH[index]
        for q in range(1, (N - 1)//h + 1):
            z = q+1 if t==1 else (1 + (1 - 2*t)*t**(q-1))/(1-t)
            total += min(h, N-q*h)*logs(z)[upper]
    return total


@cache
def reduction(index, t, upper):
    h = SMOOTH[index]
    d = allowed_distances(N, SMOOTH[:index], h)
    length, long_count = divmod(N, h)
    result = 0
    for size, count in [(length, h - long_count), (length + 1, long_count)]:
        survival = weighted(size, d, t)
        precision = 1 << 80
        projection = -(-precision * survival.numerator // survival.denominator) if upper else (
            precision * survival.numerator // survival.denominator)
        lg = logs(Fraction(projection, precision))[upper]
        result += count*lg
        print(f"gap {h}; length {size}; tilt {t}; copies {count}; old distances {d}; "
              f"ideals {sum(map(len, ideals(size, d)))}; legal mass {float(survival):.12f}")
    return result


def ceil(value):
    return -(-value.numerator // value.denominator)


def main():
    # The baseline already prices the first ten stages. Local support corrections
    # below affect only disjoint new stage blocks, including stages 11-13.
    tested = (10, 11, 12)
    constant = logs(1/BASE)[1] * (BUDGET - ANCHOR)
    base_capacity = [reduction(i, BASE, True) for i in tested]
    print(f"baseline improvement >= {int(-sum(base_capacity) / logs(1/BASE)[1])} comparisons")
    for upto, (middle, values) in enumerate(((48, (48, 52, 54, 56, 58, 60, 61, 62, 63, 64)),
                                             (41, (41, 42, 43, 44, 45)),
                                             (36, (36, 37, 38, 39, 40))), start=1):
        selection = tested[:upto]
        remaining = sum(base_capacity[upto:])
        anchor = constant - log_capacity(selection, BASE, False)
        price = Fraction(middle, 64)
        original = (anchor + log_capacity(selection, price, True)) / logs(price/BASE)[0]
        targets = []
        for val in values:
            price = Fraction(val, 64)
            chosen = sum(reduction(i, price, True) for i in selection)
            original_num = anchor + log_capacity(selection, price, True)
            denominator = logs(price/BASE)[0]
            refined = Fraction(original_num + chosen + remaining, denominator)
            targets.append((ceil(refined), price))
            print(f"stage block 11-{10+upto}; at {price} refined target {ceil(refined)}")
        best, s = min(targets)
        print(f"BEST stage block 11-{10+upto}; old target {ceil(original)}; new target {best}; tilt {s}")


if __name__ == "__main__":
    main()
