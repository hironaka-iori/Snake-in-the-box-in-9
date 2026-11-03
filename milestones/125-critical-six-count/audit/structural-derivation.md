# Structural deduction for 0120324

This bounded review combines the saved pair inequalities and the applicable
five-centre theorem. It does not run a solver or compiler, reconstruct the full
historical exclusion catalogue, or establish the proposed floors 23 and 25.
The accompanying `lean/Structural125.lean` is source written for the root
agent's independent compilation. Its arithmetic theorems retain their explicit
premises. No new mathematical definition is used.

## Indexing and applicable statements

Let the seven transitions beginning at index $r$ have canonical word
$0120324$, with $r+7\le m$. The selected normalized segment is

$$
(0,1,3,7,6,14,10,26).
$$

In this note, displayed positions $1,\ldots,6$ mean the existing counts
$\alpha_{r+1},\ldots,\alpha_{r+6}$. The prefix has six-transition word
$012032$. The suffix has directions $(1,2,0,3,2,4)$, which canonicalize
to $012314$. Its five counts are positions $2,3,4,5,6$ of the full window;
its middle count is therefore position 4.

Reversing the full word canonicalizes to $0123143$, and exchanges count
positions $i$ and $7-i$. Both six-transition subwords individually are
self-reversing up to coordinate relabelling. Thus the prefix pair theorem
can exchange positions 2 and 4 within that prefix, while the suffix theorem
preserves its middle position. Reversal of the full window must also reverse
all six counts.

The following checked results apply:

1. `Snake9.ActualPair121.actual_pair_minima` and `actual_pair_sum` give
   $\alpha_{r+2},\alpha_{r+4}\ge2$ and
   $\alpha_{r+2}+\alpha_{r+4}\ge8$. Their only window assumptions are
   $r+6\le m$ and canonical prefix $012032$.
2. `Snake9.LocalWindow.JointIntervening4934.low_count_sum`, applied to
   the four transitions starting at $r$ and $r+2$, gives
   $\alpha_{r+1}+\alpha_{r+3}\ge5$ and
   $\alpha_{r+3}+\alpha_{r+5}\ge5$. The second word is $(2,0,3,2)$.
3. The maximal applicable pair-cap exclusions from
   `Snake9.LocalWindow.SurveyCatalogue` forbid
   $(\alpha_{r+1},\alpha_{r+3})\le(3,2)$,
   $(\alpha_{r+1},\alpha_{r+4})\le(2,3)$,
   $(\alpha_{r+2},\alpha_{r+4})\le(3,3)$,
   $(\alpha_{r+2},\alpha_{r+5})\le(3,2)$, and
   $(\alpha_{r+3},\alpha_{r+5})\le(2,3)$.
   The suffix also forbids $(\alpha_{r+3},\alpha_{r+5})\le(2,2)$;
   this is weaker than the last displayed prefix exclusion.
   The two exclusions used below are `s1_p14_c23` and `s1_p25_c32`.
4. `Snake9.ActualSum112.actual_outer_sum`, applied at $r+1$, gives

   $$
   \alpha_{r+4}\le2\quad\Longrightarrow\quad
   \alpha_{r+2}+\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\ge19.
   $$

5. General positivity and the exclusion of adjacent counts $(1,1)$,
   $(1,2)$ and $(1,3)$ imply that each internal count is positive, an
   internal neighbour of a count-one vertex has count at least four,
   and adjacent internal counts sum to at least four.

The additional universal triple exclusion used below is $(4,2,2)$.
Its existing actual-snake interface is
`Snake9.LocalWindow.no_certified_window_core`, with
`Snake9.LocalWindow.allRefuted` discharging its certificate premise.
The relevant instance starts at $r+3$ and has counts at $r+4,r+5,r+6$.
The fitting condition is precisely $r+7\le m$.

## What these results prove

Adding the disjoint pair bounds at positions $(1,3)$, $(2,4)$ and $(5,6)$
gives a total of at least $5+8+4=17$. This is the best consequence of
items 1–5 alone: the integer tuple $(2,4,3,4,2,2)$ satisfies every one
of those restrictions and has total 17. This tuple is excluded by the
additional universal triple $(4,2,2)$.

Incorporating that triple exclusion gives

$$
\sum_{j=1}^{6}\alpha_{r+j}\ge18.
$$

For a direct proof, assume the total is at most 17. Each of the three
disjoint pair bounds must be an equality. The last two counts are positive
and sum to four. The count-one neighbour restriction forces both to be two.
The return bound on positions $(3,5)$ now gives $\alpha_{r+3}\ge3$, and
the equality on $(1,3)$ gives $\alpha_{r+1}\le2$.
The pair-cap exclusion on $(1,4)$ forces $\alpha_{r+4}\ge4$.
The exclusion on $(2,5)$ forces $\alpha_{r+2}\ge4$.
Their sum is eight, so both are four. The last three counts are therefore
$(4,2,2)$, a contradiction.

The abstract tuple

$$
(\alpha_{r+1},\ldots,\alpha_{r+6})=(2,4,3,4,2,3)
$$

attains 18 and satisfies all the listed pair and five-centre restrictions.
It also avoids the established general triples $(2,2,2)$, $(2,2,3)$,
$(2,2,4)$, $(2,3,2)$, $(3,2,3)$, $(4,1,c)$ for $4\le c\le6$ and their
reversals, and the four-count patterns $(2,4,2,3)$ and $(3,2,4,2)$.
Consequently the best floor from this explicitly reviewed family is 18.
It supplies an arithmetic counterexample to inferring 23 or 25 from that
family. It is not a constructed snake, local geometric assignment, or
counterexample to either proposed geometric floor. No claim of completeness
over every historical local exclusion is made.

There is a stronger useful conditional deduction. If $\alpha_{r+4}=2$,
the pair-cap exclusion on $(1,4)$ forces $\alpha_{r+1}\ge3$. The suffix
outer-sum theorem then gives

$$
\sum_{j=1}^{6}\alpha_{r+j}\ge3+2+19=24.
$$

Thus a counterexample to floor 23 must have $\alpha_{r+4}\ge3$.
For floor 25, the case $\alpha_{r+4}=2$ is reduced to the boundary
$\alpha_{r+1}=3$ and suffix outer sum exactly 19. The abstract tuple
$(3,6,3,2,4,6)$ shows that this total-24 boundary is consistent with all
the restrictions listed above. Excluding it requires further geometry.

For example, a new bound on the four remaining counts of at least 15
would combine with $\alpha_{r+2}+\alpha_{r+4}\ge8$ to give floor 23;
a bound of at least 17 would give floor 25. Neither new bound is asserted.
The present checked pair inequality alone supplies no such premise.

## Retaining empty squares in the deficit argument

Retain the existing $T$, $s_0$ and the sum $D$ of the natural-number
shortfalls below 25 in the first 39 disjoint six-count blocks. For
$m\ge235$, those blocks occupy internal positions 1 through 234.
The remaining $m-235$ internal counts are at least one, and the two
endpoint counts contribute at least eight. Hence

$$
T+D\ge39\cdot25+(m-235)+8=m+748.
$$

This sum form avoids any ambiguity from truncated subtraction. Combining
it with the retained square budget gives

$$
T+35(m+1)+2s_0\le9214
\quad\Longrightarrow\quad
D\ge36m-8431+2s_0.
$$

In particular $m\ge235$ implies $D\ge29+2s_0$. Therefore the explicit
condition $D\le28+2s_0$ suffices to prove $m\le234$. Empty squares allow
a larger deficit budget; no lower bound on their number is inferred here.

If every six consecutive internal counts have sum at least 25, 38 disjoint
blocks give, for $m\ge234$,

$$
T\ge38\cdot25+(m-229)+8=m+729.
$$

Thus $36m+764+2s_0\le9214$, which at $m\ge234$ implies $s_0\le13$.
The additional premise $s_0\ge14$ whenever $m\ge234$ would therefore
yield $m\le233$ under floor 25. Both the universal floor and that
empty-square lower bound remain explicit unproved geometric premises.

The existing Lean interface uses `SquareIncidence.totalEmptyAnchored`,
which counts each ordinary empty square at its four corners. The direct
identity and inequality are

$$
2\,\mathrm{totalEmptyAnchored}+4T+144(m+1)
=36864+4\,\mathrm{totalWedge},\qquad
\mathrm{totalWedge}\le m-1.
$$

For a nontrivial snake these imply
$4T+140(m+1)+2\,\mathrm{totalEmptyAnchored}\le36856$.
`Structural125.lean` uses this existing count directly, so its actual-snake
theorems require no new definition or separate ordinary-square conversion:

- $m\ge235$ implies $2D\ge58+\mathrm{totalEmptyAnchored}$.
- The explicit premise $2D\le56+\mathrm{totalEmptyAnchored}$ when
  $m\ge235$ gives $m\le234$.
- Universal floor 25 and $m\ge234$ imply
  $\mathrm{totalEmptyAnchored}\le52$.
- Universal floor 25 plus the explicit lower bound
  $\mathrm{totalEmptyAnchored}\ge56$ when $m\ge234$ gives $m\le233$.

## Source and receipt checks

Read-only checks matched the current source and log bytes to the saved
successful `ActualPair121` and `ActualSum112` receipts. Their printed
actual-snake theorem dependencies list only `propext`, `Classical.choice`
and `Quot.sound`. The source hashes are respectively
`17732a533cc39f73a1d140a69e5b666260a0fdc3ae5731611ff15b5f45090280`
and `9e5f7db4a74440971e5bd3d9ada06c1973c021614df22e94d09aa803d83f759d`.

The milestone49 verification receipt has status `PASS`, reports 159 Lean
audits and 50 checked negative survey rows, and has SHA-256
`fb119273313a0af5780c7fba30e9af12891a711c287311da9666bf6ea1e36f72`.
The current `SurveyCatalogue.lean` and `SumWindow4934.lean` bytes match its
source hashes `7e44e21b229cf6e9df26515cca67142b1ecfcbb00e88a924d38f1b0bed86c771`
and `6bdf9559127b46548a64082db318669d5f971db79c8dcea811e1c9983df11feb`.

The older triple interface was read in `work/final_lean/LocalWindowBridge.lean`
and its certificate composition in `LocalWindowRefuted.lean`; their current
hashes are `f4079fec8009e019d048db4b5a6764291165308352e9281d6921ffa022c65def`
and `8ec98dbea3cf7cdccf633b2550920c78d2ff6f8ca6a076d5137d1217fca315d4`.
This bounded review does not independently rebuild that older dependency chain.

The read `SquareIncidence.lean` in the saved strengthened build has SHA-256
`3813aa1d9b451cf93c643ab8c954d599be1c646d5c633133bbef9dc9de261518`.
The reused interfaces are `global_identity`, `selected_total`,
`wedge_total_upper` and `GlobalCharge98.core_count_total`.

The initial bounded review wrote this note and `lean/Structural125.lean`. No novelty,
new unconditional global bound, floor 23, floor 25, or complete-snake
counterexample is claimed by this review.

## Supplement: actual intervals under a contrary total at most 22

After the root agent reported a successful compile of `Structural125.lean`
with twelve axiom reports, that source was frozen. A separately authorized
source, `lean/ActualBounds125.lean`, supplies the actual-snake reduction for
the next probe. It imports the previously checked `ActualPair121`,
`ActualSum112`, and `CycleExclusion4906` modules. No new solver result
enters its proof.

For an arbitrary snake and canonical seven-transition word $0120324$,
the source first obtains the correct prefix and suffix by applying the
existing canonicalization and direction-slice lemmas. It then transports
`CycleWindow4906.refuted` through `canonical_interval_exclusion`, obtaining
the actual impossibility of
$\alpha_{r+1}\le2$ and $\alpha_{r+4}\le3$ simultaneously.

Under the contrary hypothesis
$\sum_{j=1}^{6}\alpha_{r+j}\le22$, the prefix theorem already gives
$\alpha_{r+2},\alpha_{r+4}\ge2$. If $\alpha_{r+4}\le2$, it must equal
two, the transported pair exclusion gives $\alpha_{r+1}\ge3$, and the
suffix theorem gives outer sum at least 19. This forces total at least 24,
contradicting the assumed cap. Hence $\alpha_{r+4}\ge3$.

Together with general positivity and the upper bound 21 at internal
vertices, the exact six intervals are

$$
([1,21],[2,21],[1,21],[3,21],[1,21],[1,21]).
$$

`actual_six_bounds` states these intervals with no extra local-refutation,
coordinate-label, endpoint, or catalogue premise. It assumes exactly the
fitting condition $r+7\le m$, the canonical word, and the total cap 22.
It is source written for separate compilation; a successful root receipt
is required before describing this new bridge as Lean checked. The child
agent did not run a compiler or solver and did not change the frozen
`Structural125.lean` source.
