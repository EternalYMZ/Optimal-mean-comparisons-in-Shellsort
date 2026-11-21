# Finite comparison certificates

All bounds use a predetermined decreasing table ending in 1, uniform distinct ranks, and actual no-sentinel linear-insertion key comparisons at n = 1,000,000,000. These are analytical results supported by integer and rational computations.

* The [seven-pass proof](seven-pass-proof.md) derives the 50,017,307,496 lower bound, including the entropy accounting and directed rounding. Run `python certify.py` to reproduce the pass-count and largest-gap exclusions. A table below 50 billion in expectation must have 8 to 207,998 passes and a largest gap of at least 9,558,065. An eight-pass table also needs its first gap at least 13,063,872 and second gap at most 241,618,784. The script also prints costs of synthetic record laws, explicitly labeled trial.
* Run `python billion_global_round_2026-11-22/cutoff.py` for the counts of small gaps. At least 44 gaps no larger than ten million force at least 50,111,544,097 expected comparisons.
* Run `python billion_global_round_2026-11-22/state/interior.py` for a separate family exclusion. If every gap strictly between 98 and 750,000,000 is congruent to 0 or ±1 modulo one million, the average is at least 50,220,000,000.
* Run `python billion_global_round_2026-11-22/candidate_independent/legal_prices.py` for the 11,12 product table. Given its prefix bound of 48,414,727,652 on the full cost, an average of at least 3,458,498,827 extra comparisons across passes 11–13 suffices to exclude that table. Extra comparisons count only comparisons after the first comparison of each insertion. The script uses the prefix bound as an input. The adjacent check.py tests the local pricing routine against exact small cases.

The comparison-counter source and fixed-table measurements are in the [Project S playground](https://github.com/EternalYMZ/Project-S/tree/main/playground).

Run `python fixed_word_mean_2026-11-22/dyadic.py` for the separate powers-of-two table. It checks exact costs on all permutations for n = 2 through 9 and reproduces the billion-key enclosure in [dyadic_billion.txt](fixed_word_mean_2026-11-22/dyadic_billion.txt).
