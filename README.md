# Project S · P04 · Optimal mean comparisons in ordinary Shellsort

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

For n ≥ 2 distinct keys in uniform random order, a table fixed from n alone attains the minimum mean key comparison count over ordinary strictly decreasing gap tables ending in 1. This minimum is between log₂(n!) and (1 + 2^165)n log₂ n. The same family works for arbitrary ordered key sets. A separate upper-bound witness has at most floor(log₂ n) passes. The cost of generating a table is outside this comparison count.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

Formal locations: [rank-input optimum](Shellsort/VerifiedOptimum.lean), [physical-key theorem](Shellsort/PhysicalKeyOptimum.lean), [short upper-bound witness](Shellsort/HarvestFullSchedule.lean).

Additional executable check: after the build, run `lake env lean PhysicalArrayCheck.lean`. See [PhysicalArrayCheck.lean](PhysicalArrayCheck.lean).

## Proof guide

[Read the proof idea in Chinese](brief.md). At one billion distinct keys, the rational finite certificate in [certificates](certificates) gives a mean of at least 50,017,307,496 key comparisons for every table with at most seven passes. The trial-coordinate costs printed by the checker describe its relaxed distributions.
