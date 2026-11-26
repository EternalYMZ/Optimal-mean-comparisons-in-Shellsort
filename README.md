# Project S · P04 · Optimal mean comparisons in ordinary Shellsort

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

For n ≥ 2 distinct keys in uniform random order, a table fixed from n alone attains the minimum mean key comparison count over ordinary strictly decreasing gap tables ending in 1. This minimum is between log₂(n!) and (1 + 2^165)n log₂ n. The same family works for arbitrary ordered key sets. A separate upper-bound witness has at most floor(log₂ n) passes. The cost of generating a table is outside this comparison count.

## Check the Lean statements

For eventually periodic nonfinal gaps, the largest allowed odd gap determines the exact $n^{3/2}$ coefficient when the tail gcd is two. Nested divisor exceptions also have explicit optimal coefficients and forced gaps. For a finite catalogue the leading term is $n^2/(4B)$ with $B$ the largest available gap including one. The sampler constructs a legal table for every catalogue and chooses a minimum-cost suffix within the construction. Lean checks the [pointwise parity charge and finite exceptional-gap lower bound](Shellsort/ExceptionalGapLower.lean). [Classification, assumptions, sampler and replays](certificates/periodic-catalogues/README.md)

For nonuniform menus, the [bounded-atom transfer](Shellsort/WeightedMenu.lean) bounds weighted energy by the uniform estimate and proves the executed weighted bound on every input at seed centers up to 49,932. The [kernel replay](certificates/weighted-menus/p04_weighted_kernel.json) covers both roots. From this checkout run `lake build Shellsort.WeightedMenu`. The [selection check](certificates/weighted-menus/check_selection.py) verifies the tail constants used in shared-sample table selection and exhausts all legal tables and permutations through six keys.

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

Formal locations: [rank-input optimum](Shellsort/VerifiedOptimum.lean), [physical-key theorem](Shellsort/PhysicalKeyOptimum.lean), [short upper-bound witness](Shellsort/HarvestFullSchedule.lean).

Additional executable check: after the build, run `lake env lean PhysicalArrayCheck.lean`. See [PhysicalArrayCheck.lean](PhysicalArrayCheck.lean).

## Consecutive three-pass blocks, 25 November 2026

The revised analysis groups consecutive seeds into triples. At center `c`, the third gap is drawn from the integers between `ceil(c/2)` and `floor(107c/50)` that are coprime to the gcd of the two retained gaps. Lean proves that every seed menu has at least `3c/7` elements and that a uniform interval proposal succeeds with probability greater than one fifth. Every choice sequence gives a decreasing table with exactly the retained seed count, at most `floor(log₂ n)` passes, and sorts every rank input for `n ≥ 2`. [Menu density](Shellsort/ConsecutiveMenus.lean) · [Schedule and correctness](Shellsort/ConsecutiveTable.lean)

Lean also bounds the executed three-pass comparison count by the entrance and exit displacements. For any distribution of entrance states, a pointwise contraction with coefficients `1/200` and `2^24` propagates the shifted quadratic budget under an independent uniform menu choice. A separate finite averaging theorem selects a short deterministic table for a prescribed input law from any supplied pointwise expected-cost bound on a distribution of short legal tables. [Cost and propagation](Shellsort/ConsecutiveBlockBounds.lean) · [Prescribed input laws](Shellsort/PrescribedInputLaw.lean)

For every seed center `c ≤ 49,932`, every array length and every entrance permutation, the mean squared displacement after the actual three passes is at most `2^24 c F`, where `F` is the entrance footrule and the mean is over the third gap. The proof sums the primitive Fourier packets for all divisors of the chosen gaps. This establishes the random one-block scale transition throughout that range. The theorem `small_center_submenu` also proves that retaining any fraction η > 0 of a seed menu increases this pointwise bound by at most a factor of 1/η. [Finite-center contraction](Shellsort/ConsecutiveMenuEnergy.lean)

The revised manuscript derives `4,143,972,353 n log₂ n < 2^32 n log₂ n`, an expected bound for each fixed input under its random table, and a polynomial-time probabilistic selection guarantee of `2^34 n log₂ n` for the uniform mean. The sharper pointwise large-sieve estimate, full expected-cost assembly, and probabilistic selection proof remain analytical. The end-to-end Lean constant is `1 + 2^165`. Exact Python checks of the finite spectral and terminal-group arithmetic run from the repository root.

```sh
python certificates/consecutive-blocks/verify_p04_spectral.py
python certificates/consecutive-blocks/verify_p04_assembly.py
```

The [replay index](certificates/consecutive-blocks/p04_lean_replay.json) identifies two historical proof revisions, their roots and their export fingerprints. The ten consecutive-block roots replay at `776455d` (22,154 declarations). The finite-center submenu theorem replays at `d439356` (21,358 declarations). To check them from this checkout, create the two worktrees below and run the script from this README's directory. It uses Python 3.11 or newer, the pinned Lake toolchain and Nanoda. For each worktree it records the theorem statements and digest in `.lake/p04-replay/`.

```sh
git worktree add --detach ../p04-consecutive 776455d3d5e381fd92086cf5659f96674eaf5d4a
git worktree add --detach ../p04-submenu d439356fd87e130d86b879a68360d14acdbcbc30
(cd ../p04-consecutive && lake exe cache get && lake build)
(cd ../p04-submenu && lake exe cache get && lake build)
python certificates/consecutive-blocks/replay_p04.py --repo ../p04-consecutive
python certificates/consecutive-blocks/replay_p04.py --repo ../p04-submenu
```

## Proof guide

[Read the proof guide](brief.md). At one billion distinct keys, the [written entropy proof](certificates/seven-pass-proof.md) and its rational certificate give a mean of at least 50,017,307,496 key comparisons for every table with at most seven passes. The trial-coordinate costs printed by the checker describe its relaxed distributions.
