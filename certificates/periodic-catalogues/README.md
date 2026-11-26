# Periodic gap catalogues

Miaozhen Yu. A fixed catalogue constrains the nonfinal gaps of a strictly decreasing Shellsort table; the final gap is always 1. Above a fixed cutoff, permission depends only on the residue modulo $q$. If the tail is nonempty let $d$ be the gcd of its residues and $q$.

| Allowed nonfinal gaps | Minimum uniform mean comparisons |
|---|---|
| Nonempty tail, $d=1$ | $\Theta(n\log n)$ |
| Nonempty tail, $d>1$ | $\Theta(n^{3/2})$ |
| Finite catalogue | $\Theta(n^2)$ |

Constants may depend on the fixed catalogue. If all nonfinal gaps are multiples of $d>1$, the first term is $\sqrt{\pi}(d-1)n^{3/2}/(8\sqrt d)$ with an additive $O(n\log n)$ remainder. The classical formula counts inversions after complete within-class sorting. The construction simulates a primitive schedule on all quotient classes with one word, reaches that reference up to $O(n)$ expected residual inversions, and pays $O(n\log n)$ for the prefix. [Janson and Knuth, Theorem 2, (9.3)](https://arxiv.org/pdf/cs/9608105)

For $d=1$ draw one complete table before the input arrives. For each RMS rank tolerance $1\le s\le n$, a length fixed by the catalogue, $n$ and $s$ guarantees $\mathbb E Q\le ns^2$ on each input with $O(n(1+\log(n/s)))$ expected comparisons. Different tolerances stop the same schedule. The footrule comparison lower bound is classical. [Giesen, Schuberth and Stojaković, Theorem 2.1](https://doi.org/10.3233/FI-2009-0005)

Run in the repository root:

~~~sh
python certificates/periodic-catalogues/periodic_catalogues.py 100000 210 30 42 70 105 --seed 1
python certificates/periodic-catalogues/periodic_catalogues.py --check
lake build Shellsort.CatalogueSchedules Shellsort.PeriodicMenus
~~~

The [periodic replay](periodic_menus_kernel.json) checks the anchor gcd, the exact menu size and the shared-prime obstruction for every three allowed gaps in the mod-210 example. The [schedule replay](catalogue_schedules_kernel.json) checks finite scale paths from pointwise contraction and cost hypotheses, and an explicit family of decreasing gap words. The all-scale analytical estimate is required to deduce the full classification. To repeat a Nanoda export in a built checkout, use the existing driver and each manifest's ordered list of roots, for example:

~~~sh
lake env python certificates/weighted-menus/replay.py Shellsort/PeriodicMenus.lean Shellsort.PeriodicMenus.anchors_gcd Shellsort.PeriodicMenus.menu_card Shellsort.PeriodicMenus.four_residues Shellsort.PeriodicMenus.every_three_share_prime
~~~
