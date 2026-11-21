# How can a gap table chosen before reading the input attain the optimal average order?

Let $m_n$ be the minimum expected number of actual key comparisons over strictly decreasing positive gap tables below $n$ ending in 1. The input is a uniform permutation of distinct keys. Each chain uses linear insertion, including the comparison that stops a scan when one occurs. Each table is fixed before reading the input. For every $n\ge2$, the Lean theorem gives
$$\log_2(n!)\le m_n\le(1+2^{165})n\log_2 n.$$

**How much displacement can a pass afford?** For rank $x$ in slot $p(x)$ write $F=\sum_x|p(x)-x|$ and $Q=\sum_x(p(x)-x)^2$. A gap-$h$ pass uses at most $2F/h$ successful shifts and at most $n$ stopping comparisons. Each pass can only decrease $F$. If all gaps in a block are at least $H$ and its initial state satisfies $\sqrt{\mathbb E Q/n}\le LH$, Cauchy–Schwarz bounds the mean cost of each pass by $(1+2L)n$. Only the analyst uses final ranks.

**How can the scale decrease?** At scale $c$, apply two fixed gaps and choose a third from a finite set near $c$. Decompose threshold discrepancies by frequency and combine contributions with the same reduced frequency before estimating them. For each initial permutation the candidate average of the squared displacement after three passes is at most $2^{-47}Q+2^{98}cF$. Now average over the actual distribution at the start of the block. Interchanging the two finite averages gives one common gap attaining the bound in expectation. The choice can therefore be fixed before seeing the particular input. Iteration keeps mean squared displacement small at successive scales. A witnessing schedule uses at most $\lfloor\log_2 n\rfloor$ passes.

**Why is the order optimal?** The comparison transcripts for a fixed table form a binary prefix code. Distinct rank permutations require different transcripts: identical outcomes would move the same original labels to the same slots. The uniform mean transcript length is therefore at least $\log_2(n!)$. The finite family of legal tables attains its minimum. The upper bound supplies its order of growth. Efficiently generating an exact minimizer and convergence of $m_n/(n\log_2 n)$ are separate questions.

[HarvestScaleNumbers.lean](https://github.com/EternalYMZ/Optimal-mean-comparisons-in-Shellsort/blob/fe3fbebaa0bada514b2fe3e6c2cd61cd99a858f4/Shellsort/HarvestScaleNumbers.lean) · [VerifiedOptimum.lean](https://github.com/EternalYMZ/Optimal-mean-comparisons-in-Shellsort/blob/fe3fbebaa0bada514b2fe3e6c2cd61cd99a858f4/Shellsort/VerifiedOptimum.lean)

[Written proof of the seven-pass lower bound at one billion keys](certificates/seven-pass-proof.md)
