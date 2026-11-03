# Endpoint equality and the remaining graph obstruction

A snake has vertices $p_0,\ldots,p_m$ and length $m$ edges. The singleton counts
$\alpha_i$ retain their existing meaning.

## Local restriction

For a canonical six-direction window $012032$ starting at $r$, milestone121 proves

$$
\alpha_{r+2}\ge2,\qquad\alpha_{r+4}\ge2,\qquad
\alpha_{r+2}+\alpha_{r+4}\ge8.
$$

Complete checked snakes attain $(2,6)$, $(3,5)$ and $(4,4)$. The candidate
refinement is that equality forces both endpoints to have Hamming distance two
from both counted vertices.

The case $\alpha_{r+2}\le2$, $\alpha_{r+4}\le6$ is now proved for arbitrary snakes
in Lean, with no local-refutation premise remaining. Reversal gives its symmetric
case. The $(3,5)$ and $(4,4)$ cases have saved native refutations and checked
encodings; their Lean replays remain pending in the 381-module batch. The five-case
assembly has passed Lean with the local claims as explicit assumptions. The
universal equality theorem is still pending.

Each formula uses the full cube, the stated intervals and no added cycle cuts.
The extra clause requires an endpoint outside the common distance-two spheres
about normalized vertices $3$ and $6$. Their intersection is

$$
\{0,5,10,15,18,23,34,39,66,71,130,135,258,263\}.
$$

Its complement supplies 498 positive endpoint flags. The clause interpretation
and canonical-coordinate transfer passed Lean. An isolated checker raises the
literal parsing limit from 255 to 1023; its soundness lemmas also passed Lean.
The original checker is unchanged.

## A sharper occurrence bound

The distance-two spheres about distinct vertices of $Q_9$ intersect in at most
14 vertices. Translation reduces verification to 511 nonzero endpoint differences
and the 36 vertices at distance two from zero. The finite check and its transfer
to selected snake positions passed Lean.

Let $I$ be a finite set of fitting window starts, with both counted vertices of
each window in this intersection. The first positions $r+2$ are distinct. If $I$
is nonempty, the second position $\max I+4$ is greater than every first position
and contributes another distinct vertex. Hence

$$
|I|+1\le14,\qquad |I|\le13.
$$

The empty case is immediate. This argument passed Lean and improves the earlier
allowance of 14. No optimality claim is made for 13. Applying it to every equality
window still requires the two pending endpoint certificates.

For nonnegative occurrence credit $C$, the existing budget and a potential
estimate give

$$
(4200d+p)m\le1098960d+13Cd+8p+R.
$$

This arithmetic implication passed Lean; its occurrence, share-floor and
potential premises remain explicit.

## The numerical obstruction

The graph experiment used the earlier allowance of 14 and exact suffix pairs
$(3,5)$, $(4,4)$ and $(5,3)$. Clipped symbol $6$ represents $[6,21]$, so $(2,6)$
and $(6,2)$ cannot receive equality credit without more information. There are
9,577 eligible retained keys. Both profiles retain the inherited sum hypotheses.

At $C=4$, the conditional minimum mean remains 496. A replacement cycle receives
zero credit; the occurrence correction worsens the integer comparison from 234
to 235. Deleting every eligible suffix leaves both means and ranges unchanged:

| Profile | Minimum mean | Potential range | Original integer comparison |
| --- | ---: | ---: | ---: |
| Completed-share | $2915/6$ | $1730/3$ | 235 |
| Conditional-share | $496$ | $602$ | 234 |

The producer checked every retained-edge potential inequality. A separate audit
checked saved cycles, hashes and arithmetic, without independently rebuilding
the entire graph.

The surviving conditional cycle has edges 1275804, 3049577 and 988624, with words
$012304235$, $012341254$ and $012301430$. Each key has six counts equal to four,
history zero, weight 496 and zero additional credit. No actual snake realizing
this cycle is established.

Nonnegative credit preserves the old potential lower bound, while this cycle
still attains 496. The conditional minimum mean therefore stays 496 for every
$C\ge0$ in this credit family. The completed-profile attaining cycle also receives
zero credit. Even zero occurrence cost and zero potential range give

$$
\frac{1323416}{5623}>235,\qquad\frac{137866}{587}>234.
$$

Using 13 instead of 14, or reducing the range alone, therefore cannot improve
either integer bound while these cycles remain. Lean checks these numerical
inequalities and their nonnegative-cost versions. The connection from finite
graphs to arbitrary snakes retains its separate obligations.

## Next work and limits

Complete the endpoint batch and its equality and thirteen-occurrence conclusions.
The older batches 104 and 115 were found stopped with stale RUNNING files. Their
states and locks were preserved, process absence was verified, and unchanged
drivers were resumed from checked receipts.

For numerical pressure, inspect the existing six-consecutive-fours work against
the three surviving keys. The prepared next inputs contain all eight internal
count intervals: the first two are unrestricted and the six recorded counts are
exactly four. These cases have not been searched or excluded. Existing seven-count
certificates need a placement and coverage check before excluding these keys.

The maintained interval remains $191\le a(9)\le235$, with the documented limitation
on independently rebuilding the contributor upper-bound proof. Conditional 234
remains conditional. Neither optimality nor 196 is established. The open paper
remains revision 116; the next full revision is scheduled for 126. Its authors
and hyperlink settings are unchanged.
