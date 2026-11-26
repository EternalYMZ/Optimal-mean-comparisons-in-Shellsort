# Periodic gap catalogues

Miaozhen Yu. A fixed catalogue constrains the nonfinal gaps of a strictly decreasing Shellsort table; the final gap is always 1. Above a fixed cutoff, permission depends only on the residue modulo $q$. If the tail is nonempty let $d$ be the gcd of its residues and $q$.

| Allowed nonfinal gaps | Minimum uniform mean comparisons |
|---|---|
| Nonempty tail, $d=1$ | $\Theta(n\log n)$ |
| Nonempty tail, $d>1$ | $\Theta(n^{3/2})$ |
| Finite catalogue | $\Theta(n^2)$ |

Put $c_d=\sqrt\pi(d-1)/(8\sqrt d)$. For a pure-multiple catalogue with $d>1$ the leading coefficient is $c_d$. For $d=2$ and arbitrary exceptions, the coefficient is $c_2/h$ with $h$ the largest permitted odd gap including 1. Both have additive error $O_{\mathcal A}(n\log n)$. For a finite catalogue with maximum $B$ including 1, the mean optimum is $n^2/(4B)+O_B(n^{3/2})$. The parity optimum eventually uses $h$ and the finite optimum eventually starts with $B$. The reference inversion mean comes from the classical two-pass formula. [Janson and Knuth, Theorem 2, (9.1)–(9.3)](https://arxiv.org/pdf/cs/9608105)

A common schedule on the quotient classes prepares a fixed suffix. A gap $g$ changes the current divisor from $D$ to $e=\gcd(D,g)$ and contributes $\sqrt\pi(D-e)/(8g\sqrt D)$ to its leading coefficient. For each fixed suffix, averaging over the prefix draw and the independent uniform input gives this sum times $n^{3/2}$ with additive error $O_{\mathcal A}(n\log n)$. There also exists a deterministic prefix with this expansion. For exceptions forming a strict chain of divisors of $d$, its minimum is the global optimum and every chain member is eventually mandatory. This follows by charging the inversions left after sorting all classes modulo the smallest exceptional divisor, then applying the same argument within those classes. The quotient lower bound also proves equality when $d=2e$, all nonfinal gaps are multiples of $e$ and at least one is a nonmultiple of $d$. For arbitrary mixed catalogues the finite optimization yields a constructive upper bound. [Sampler, examples and finite comparisons](periodic_catalogues.md) · [Classical preservation of sorted gaps](https://sedgewick.io/wp-content/themes/sedgewick/papers/1985Improved.pdf) · [Footrule equality for permutations avoiding 321](https://arxiv.org/pdf/1202.4765)

For $d=1$ draw one complete table before the input arrives. For each RMS rank tolerance $1\le s\le n$, a length fixed by the catalogue, $n$ and $s$ guarantees $\mathbb E Q\le ns^2$ on each input with $O(n(1+\log(n/s)))$ expected comparisons. Different tolerances stop the same schedule. The footrule comparison lower bound is classical. [Giesen, Schuberth and Stojaković, Theorem 2.1](https://doi.org/10.3233/FI-2009-0005)

The [exceptional-gap kernel record](exceptional_gap_kernel.json) covers five roots for the pointwise suffix charge, the parity footrule identity, and a finite lower bound $n\sqrt{nd}/(2048H)$ on both executed means. Its hypothesis is $H\ge1$, $2\le d\le n$, with every gap above $H$ divisible by $d$. The [quotient kernel record](residue_quotient_kernel.json) covers $I_1(S_ez)+I_e(z)\le I_1(z)$ on every actual permutation. For each record use the replay driver below with the corresponding source and its ordered roots. The coefficient formula for all nested chains uses an analytical argument.

Run the following commands from the repository root.

~~~sh
python certificates/periodic-catalogues/periodic_catalogues.py 100000 210 30 42 70 105 --seed 1
python certificates/periodic-catalogues/periodic_catalogues.py --check
python certificates/periodic-catalogues/check_quotient_lower.py
lake build Shellsort
~~~

The [periodic replay](periodic_menus_kernel.json) checks the anchor gcd, the exact menu size and the shared-prime obstruction for every three allowed gaps in the mod-210 example. The [schedule replay](catalogue_schedules_kernel.json) checks finite scale paths from pointwise contraction and cost hypotheses, and an explicit family of decreasing gap words. The all-scale analytical estimate is required to deduce the full classification. To repeat a Nanoda export in a built checkout, use the existing driver and each manifest's ordered list of roots, for example:

~~~sh
lake env python certificates/weighted-menus/replay.py Shellsort/PeriodicMenus.lean Shellsort.PeriodicMenus.anchors_gcd Shellsort.PeriodicMenus.menu_card Shellsort.PeriodicMenus.four_residues Shellsort.PeriodicMenus.every_three_share_prime
lake env python certificates/weighted-menus/replay.py Shellsort/ExceptionalGapLower.lean Shellsort.ExceptionalGapLower.exceptional_suffix Shellsort.ExceptionalGapLower.uniform_exception Shellsort.ExceptionalGapLower.two_sorted_identity Shellsort.ExceptionalGapLower.parity_shift_price Shellsort.ExceptionalGapLower.legal_exception
lake env python certificates/weighted-menus/replay.py Shellsort/ResidueQuotientLower.lean Shellsort.ResidueQuotientLower.gap_sort_inversion_drop
~~~
