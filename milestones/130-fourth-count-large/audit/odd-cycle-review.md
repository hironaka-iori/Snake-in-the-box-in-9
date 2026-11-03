# Conditional parity comparison of the saved cycles

The proposed parity restrictions remove the saved four-edge witness for
odd-length snakes. For even-length snakes, one initial phase is excluded
and the other survives the parity test. The surviving phase contributes two
distinct equality starts per period, so the at-most-thirteen budget would
exclude seven complete fitting repetitions. The eighteen-edge witness is
unchanged by all these tests.

This is a comparison of the two supplied saved cycles only. The new parity
statements and the occurrence budget are assumptions of the computation.
No full graph was constructed, no solver or Lean compiler was run, and no
new minimum mean or snake upper bound is claimed.

## Inputs and placement checks

The primary input is milestone 121's `data/pair-graph/results.json`. The
specified milestone 124 `cycle-targets.json` identifies itself as a copy of
the original milestone 121 cycle contexts. Its source hash, profile names,
edge order, direction words, chronological counts and saved bonuses all match.
These files contain an eighteen-edge cycle of mean \(2915/6\) and a four-edge
cycle of mean \(496\). They do not contain the later eleven-edge witness.
The source results describe finite profiles with unproved sum rules. This
audit preserves that qualification and does not discharge those other premises.

For each saved edge, the audit examines both placements. At placement zero
it uses direction entries 2 through 7 and count entries 0 through 4; at
placement one it uses direction entries 3 through 8 and count entries 1
through 5. These are zero-based positions. In each orientation it renames
directions by their order of first occurrence and tests the word 012032.
When reversing a word, it reverses the five counts as well. The pair always
uses entries one and three of the oriented five-count list.

Both orientations match whenever this canonical word matches: its reversal
canonicalizes to the same word. They give the same pair sum, deletion decision
and proposed credit, so each placement is counted once.

The audit also checks cyclic source/target adjacency in the saved vertex
identifiers, count overlap, direction overlap after canonicalization, every
six-count code, and each displayed mean against the saved weight sum. These
checks concern the saved cycle data; they do not revalidate edge membership
by rebuilding the full graph.

## Odd-length comparison

The proposed condition for odd-length snakes is

\[
\alpha_{r+2}+\alpha_{r+4}\ge9.
\]

A count symbol below six is exact, whereas symbol six represents an actual
count from six through twenty-one. The audit therefore deletes a placement
only when both pair symbols are below six and their sum is below nine. A
clipped pair such as \((6,2)\) cannot be deleted by that test.

At suffix placement one, the proposed additional credit is twenty-four times
the positive part of nine minus the clipped pair sum. It is combined with
the existing bonus by taking the maximum. The two bonuses are never added
together. An edge removed by either placement receives no retained weight
or updated cycle mean.

The clipping check enumerates all thirty-six symbol pairs and all 441
corresponding actual pairs in \([1,21]^2\). For each symbol pair, the deletion
test agrees with the absence of any represented actual pair satisfying
floor nine. For all 413 actual pairs satisfying that floor, the proposed
credit is at most twenty-four times the actual excess above the clipped
pair sum. This verifies the finite clipping arithmetic; it does not prove
the odd-length geometric premise.

For the profile labelled `completed`, none of its thirty-six placements
matches 012032. No edge is removed and no weight changes. The saved weight
sum remains 8745 over eighteen edges, so its mean remains \(2915/6\).

For the profile labelled `conditional_floor18`, the changes are:

| Saved edge | Placement | Five counts | Exact pair | Old weight | Proposed suffix credit | Odd-length outcome |
|---|---:|---|---|---:|---:|---|
| 2222588 | 1 | \((5,3,3,5,5)\) | \((3,5)\) | 616 | 24 | Removed |
| 148850 | 0 | \((5,3,3,5,5)\) | \((3,5)\) | 376 | 0 | Removed |
| 2219941 | 1 | \((3,5,5,3,3)\) | \((5,3)\) | 376 | 24 | Removed |
| 146842 | 0 | \((3,5,5,3,3)\) | \((5,3)\) | 616 | 0 | Removed |

Every listed pair is exact and sums to eight. Thus the four-cycle of weight
sum 1984 and mean 496 is broken by the assumed odd-length floor nine. There
are no surviving edges with changed weights in either saved cycle. The two
proposed credits of twenty-four belong to deleted edges and cannot be used
to report an updated cycle mean.

## Even-length comparison

For even-length snakes the assumed restriction is that an exact-pair-eight
012032 window starts at an even index. For initial phase \(p\), edge visit
\(k\) and placement \(s\), the window's start parity is computed as

\[
(p+k+s+2)\bmod2.
\]

Reversal preserves this start parity when the total snake length is even.
The audit rejects an exact pair-eight match precisely when the displayed
parity is odd. It tests both initial phases. To return to the starting
parity, an odd-length cycle would require two traversals; an even-length
cycle requires one. Both supplied cycles have even length, so one traversal
is sufficient in each phase here. No eleven-edge cycle is tested.

For the four-cycle, the matching placements have start offsets 3, 3, 5 and 5
relative to its initial phase, in the displayed edge order. Phase zero makes
all four starts odd and removes all four edges. Phase one makes all four
starts even and leaves the four-cycle with its saved weights and mean 496.

| Saved profile | Initial phase | Removed edges | Surviving saved mean |
|---|---:|---|---|
| `completed` | 0 | None | \(2915/6\) |
| `completed` | 1 | None | \(2915/6\) |
| `conditional_floor18` | 0 | 2222588, 148850, 2219941, 146842 | No surviving period |
| `conditional_floor18` | 1 | None | \(496\) |

The even-length comparison changes no retained weight. It applies the start
parity test separately from the odd-length floor-nine credit calculation.

## Counting equality starts without duplication

The suffix match at edge 2222588 and the prefix match at the next edge 148850
represent the same original window start. The same duplication occurs for
edges 2219941 and 146842. Counting both placements would therefore double
the number of equality windows.

The occurrence-budget calculation counts only matching suffix placement one
with an exact pair sum eight. The surviving phase-one four-cycle has two
such starts per four-edge period, at offsets 3 and 5. Consecutive periods
give distinct starts. If all these designated windows are realized as fitting
windows of an actual snake, seven complete periods give fourteen equality
starts and exceed the bound thirteen. Under that hypothesis, at most six
complete periods are possible. A partial period requires its own count.

The eighteen-edge witness has zero such starts in either phase, so this
occurrence budget places no restriction on its repetitions. These conclusions
do not bound the length of an arbitrary walk, which may use other cycles or
leave and re-enter a cycle. They also require the correspondence between
the counted graph placements and distinct fitting actual windows.

## Saved evidence and scope

`audit/check_odd_cycles.py` performs the comparison without importing the
graph producer. `data/odd-cycle-review.json` records every edge, both oriented
tests, odd-length deletion and credit decisions, both even-length phases,
and the distinct suffix-start counts. Its input hashes are rechecked after
the computation. The earlier odd-only result and its exact script are
preserved separately in the audit folder.

The unchanged eighteen-edge witness remains an obstruction to improving its
saved mean using these additional restrictions alone. Removing the four-edge
witness does not determine a new minimum mean. Other cycles may remain, and
the supplied inputs do not assess the later eleven-edge cycle. No new global
upper bound follows from this saved-cycle comparison.
