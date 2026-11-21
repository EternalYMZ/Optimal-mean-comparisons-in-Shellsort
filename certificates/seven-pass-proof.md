# Why seven passes cannot meet the billion-key comparison target

**Theorem.** Let n = 1,000,000,000. Choose any strictly decreasing positive gap table, with every gap below n and last gap 1, before reading a uniform permutation of n distinct keys. Ordinary linear insertion without a sentinel uses at least **50,017,307,496 key comparisons in expectation** if the table has at most seven passes. This proof uses exact rational arithmetic for the finite numerical bounds. Its arithmetic and entropy argument are documented here for independent review.

## What a comparison costs and what a record retains

In a chain, an insertion with j ≥ 1 predecessors and m successful right shifts has m + 1 key comparisons if m < j, and m comparisons if m = j. Reaching the chain head ends the scan by position alone. Its cost is therefore 1 + e_j(m), where e_j(m) = min(m, j − 1).

Record m for each insertion in its scheduled chain and position. To undo an insertion at position j, remove the key at position j − m, move the m intervening keys one place left, and return the removed key to position j. Undo each chain's insertions in reverse order, then undo the passes from the final sorted array back to the input. The full record thus determines the input and has Shannon entropy ln(n!) in natural-log units. This is the reversible insertion-record idea of [Jiang, Li and Vitányi](https://arxiv.org/abs/cs/9906008).

The first pass acts on chains with uniform relative orders. At insertion j, m is uniform on {0,…,j}, so the mean cost is j/2 + j/(j+1). On a chain of length ℓ the cost per key is
$$
a_\ell=(\ell-1)/4+1-H_\ell/\ell,
\qquad H_\ell=\sum_{j=1}^{\ell}1/j.
$$
The chains' relative orders are independent: every tuple of such orders occurs for the same number of input permutations. The inverse insertion argument also applies within one chain, so its first-pass record has entropy ln(ℓ!). Let $b_\ell=\ln(\ell!)/\ell$. A bar over a function of ℓ denotes its mean weighted by the fraction of keys in chains of that length. Then the first-pass mean cost and record entropy are $n\overline a$ and $n\overline b$, respectively.

## Gibbs bound for the remaining actual record

There are V = Σ(n − h) insertion coordinates in the suffix, where the sum runs over the suffix gaps. At a coordinate with j predecessors, use reference weights $t^{e_j(m)}$ for $0<t<1$. Their sum is
$$
G_j(t)=\sum_{m=0}^{j}t^{e_j(m)}
=\frac{1+(1-2t)t^{j-1}}{1-t}.
$$
The repeated weight at m = j − 1 and m = j accounts for the boundary case of reaching the chain head. The suffix record conditional on any realized first-pass record can be arbitrarily dependent. Apply nonnegativity of relative entropy to that conditional distribution and the product of the normalized reference weights. Its entropy is at most $\sum\ln G_j(t)+\ln(1/t)\,\mathbb E[\sum e_j\mid\text{first record}]$. All coordinates and predecessor counts depend only on n and the fixed table. Averaging the inequality gives
$$
\mathbb E C_{\rm suffix}\ge V+
\frac{\ln(n!)-n\overline b-\sum\ln G_j(t)}{\ln(1/t)} .
$$

For $t>1/2$, use $G_j(t)\le 1/(1-t)$. After this substitution the coefficient of V in the bound is $1+\ln(1-t)/\ln(1/t)<0$, so replacing V by $6n$ lowers the bound for all schedules with at most seven passes. The factorial bound $\ln(n!)\ge\int_1^n\ln x\,dx\ge n(\ln n-1)$ gives
$$
\frac{\mathbb E C}{n}\ge\overline a+6+
\frac{\ln n-1-\overline b+6\ln(1-t)}{\ln(1/t)}.
$$
The right side is a key-weighted average of the expressions for individual first-chain lengths.

## Reproduce the outward rounding

Set $t=431/500$. [certify.py](certify.py) evaluates a rational lower bound for each chain length from 1 through 201. It sums logarithm upper bounds for $b_\ell$, uses lower bounds for $\ln n$ and $\ln(1-t)$, and divides the resulting lower numerator by the endpoint that gives a lower quotient. For positive $x$, it writes $x=2^k u$ with $1\le u<2$. With $v=(u-1)/(u+1)$ it sums the first 32 terms of $\ln u=2\sum_{i\ge0}v^{2i+1}/(2i+1)$, bounds the remaining terms above by $2v^{65}/(65(1-v^2))$, and encloses $\ln 2$ by the same method at $u=2$. All operations are rational, including final directed rounding. The smallest lower bound occurs at ℓ = 24 and its product with n rounds down to 50,017,307,496.

First-pass chain lengths differ by at most one. If any length exceeds 201, every length is at least 201. The function $a_\ell$ increases with ℓ because $H_\ell/\ell$ decreases. The exact value of $na_{201}$ alone is larger than 50,017,307,496. This covers the other case. Run `python certify.py` and compare the result with [certificate.txt](certificate.txt). The tests on larger pass counts and the synthetic record laws printed by the same script are separate from this theorem.
