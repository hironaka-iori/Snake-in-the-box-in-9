# Why the 191-edge snakes work: palette structure of the bank

Checkpoint: 21 October 2026. **No snake longer than 191 edges was found.**
This milestone analyses the structure shared by the 131 bank snakes
(`work/bank9.json`), formulates construction hypotheses from it and tests
them in small, structured families. All exclusions below are solver or
enumeration results inside stated families, without proof certificates.

Notation. A snake with 192 vertices has 191 edges. Q9 = Q5 x Q4: the five
most used coordinates are *heavy* (bits of x in Q5), the four least used are
*light* (bits of a *cell* c in Q4). The *quotient walk* is the sequence of
cells visited; a *piece* is a maximal run of the snake inside one cell, an
induced path of Q5.

## 1. Invariants of the bank

All counts are recomputed by `scripts/invariants.py` (`data/invariants.json`).

**Two families.** 127 entries (A) have 5 heavy coordinates with 26-44 uses
and 4 light coordinates with 19-24 uses in total (typically 1, 4, 6, 8; or
2, 4, 7, 9). The 4 entries 127-130 (B) have 6 heavy coordinates and 3 light
coordinates used 2, 3, 7 times (12 light transitions); they are the only
entries with undominated vertices (2-3 each). Everything below concerns
family A unless stated otherwise.

**Cell profile.** The quotient walk has 19-24 light transitions (20-25
visits) and visits all 16 cells. In every entry:

- 12 *strong* cells hold 12-14 vertices, almost always as a single piece
  (624 pieces of 13, 436 of 12, 415 of 14 vertices over the 127 entries);
- 4 *weak* cells hold 8-11 vertices, as a piece of 6-8 vertices plus one or
  two single-vertex pass-throughs (cell profiles such as
  14,14,14,13,13,13,13,13,13,12,12,12,9,9,9,9);
- the 4 weak cells always form **two antipodal edges of Q4**: their pairwise
  distances are {1,1,3,3,4,4} in all 127 entries.

A Q5 snake has at most 14 vertices, so strong cells are essentially full.

**Palette.** For each heavy vertex x let T(x) be the set of cells in which
(x, c) lies on the snake. Splitting Q5 by whether T(x) contains only even
cells (A), only odd cells (B) or both (M) gives, in all 127 entries,

- |A| = |B| = 11 (24 entries have one spine of 10), |M| = 10;
- A and B are **induced 11-vertex paths of Q5** (the spines), with
  transition sequences 2,1,0,2,3,4,0,2,1,0 and 2,4,3,2,0,1,3,2,4,3;
- **one single pair (A, B) up to Q5 symmetry** for all 127 entries
  (`data/spine_classes.json`); exactly one automorphism of Q5 swaps A and B,
  and only the identity fixes both;
- every light transition happens at a vertex of M;
- each strong cell contains 9-11 vertices of its own spine and 2-4 of M.
  Over the whole snake 142-146 of the 176 spine slots and 46-57 of the 160
  M slots are used; the weak cells are where the spine slots are lost.

Because A and B are disjoint and adjacent cells have opposite parity, spine
vertices never conflict across cells. **The cells interact only through the
10 vertices of M.** This is a relaxation of the 14-cycle palette of milestone
16: smaller spines (11 instead of 14) and a large shared set M (10 instead of 4).

The maximum induced linear forest inside A u M has 14 vertices
(`freewalk.c` computes it), so the palette alone allows 16 x 14 = 224.

**Near symmetry.** With g = (swap of A and B on Q5, a suitable map of Q4),
|S cap g(S)| is 182-190 for every sampled entry with |A| = |B| = 11
(`scripts/sym.py`, every 6th entry). The bank snakes are close to invariant
under an involution, which is consistent with the symmetric-snake search
of the other agent. That search is not duplicated here.

**Q8 halves.** The least used light coordinate splits a family-A snake into
two Q8 halves of 96+96 vertices (90 entries; the coordinate is used 2 or 4
times) or 97+95 (37 entries; used once in 25 of them, three times in 12).
With one crossing, each half is a single Q8 snake with 96 or 94 edges, inside
the same palette. **No family-A half has more than 97 vertices**, and 97 is
exactly the palette maximum in Q8 (H4 below). Family B splits as 94+94+4 along
its lightest coordinate.

The record Q8 snake (Carlson-Hougen, 98 edges) is *not* of this kind. As
Q5 x Q3 its profile is 14,14,13,13,12,12,12,9, with 17 visits and pieces of at
most 8 vertices, and its parity palette consists of linear forests with 9 and
8 vertices and |M| = 14 (`data/pal_q8witness.json`). The Q9 records are
therefore not glued from optimal Q8 pieces. Their halves are 2-3 vertices
short of the Q8 optimum.

**Other observations.** 12-vertex pieces are mostly subpaths of 14-coils of
Q5 (426 of 436), but 13- and 14-vertex pieces mostly are not. Both spines lie
in 14-coils. The endpoint distance is 3, 5 or 7. Repeated heavy coordinates
are 3 to 14 positions apart, and only 12 normalised 6-windows of the
transition sequence occur. The bank shows no recursive pattern of the
Abbott-Katchalski or Kautz type. Its 50 distinct quotient walks (up to Q4
symmetry and reversal) revisit the weak cells instead of following a Gray
code of Q4, and the pieces are not copies of one Q5 snake.

## 2. Hypotheses and tests

| Id | Hypothesis | Family tested | Result |
|---|---|---|---|
| H1 | Fixing only the quotient walk frees enough to grow | Quotient-walk SAT (`qmodel.py`); heavy coordinates free | Entry-0 walk, fixed piece sizes: SAT in 1.1 s (control). Free sizes, target 192 or 193: UNKNOWN after 100-200 s. Q8 sanity: the 98-edge witness walk is recovered in 3.2 s; "one piece longer" is UNKNOWN after 150 s, although it is impossible since a(8)=98 |
| H2 | The bank walks with the bank palette are not maximal: some piece can grow | Palette + bank walk, piece sizes >= bank sizes, at least one piece larger (`rigidity_grow.py`) | **49/49 distinct walks UNSAT** (0.1-0.6 s); controls without growth SAT with 192 |
| H2' | Rebalancing pieces by up to 2 vertices gains 1 | Palette + bank walk, sizes >= bank - slack, total >= 193 (`rigidity_slack.py`) | slack 1: entries 0, 73 UNSAT; **slack 2: 49/49 UNSAT** (<= 3.4 s); slack 3 and 5: UNKNOWN (entry 0, 35 s) |
| H3 | Removing the weak cells (Hamiltonian quotient walk, one piece per cell) | All 131 Hamiltonian paths of Q4 up to symmetry, bank palette, total >= 193 (`hamiltonian_walks.py`, `hamfree.c`) | Interior pieces >= 12: no Hamiltonian-quotient snake exists at all (exhaustive, 0.5 M nodes). Interior pieces >= 11: 131/131 UNSAT. Interior pieces >= 10: 131/131 UNSAT (<= 12 s) |
| H3-Q8 | Same principle in Q8 = Q5 x Q3 | Hamiltonian quotient, bank palette, exhaustive (`hamfree.c`) | maximum 94 vertices (COMPLETE, 7.5 M nodes), against 99 for a(8) |
| H4 | The palette itself is good in every dimension (palette tower Q5 x Qk) | Global SAT with only the palette restriction (`tower.py`) | Q6: max 26 vertices (opt. 27); Q7: max 49 (opt. 51); Q8: max 97 (98 UNSAT in 477 s; opt. 99); Q9: >= 192 (192 UNKNOWN in 150 s) |
| H5 | Doubling: two palette Q8 halves joined across one crossing | Palette + light coordinate used exactly once (`doubling.py`) | Not decided: control 192 UNKNOWN (300 s), 193 with both halves >= 96 UNKNOWN (600 s) |
| H6 | Family B (Q6 x Q3) is rigid in the same way | Own palette and walk, sizes >= bank - slack, total >= 193 (`familyB_slack.py`) | Entries 127, 129: controls SAT (192, about 2 s); slack 0, 1, 2 UNSAT; entry 127 slack 4 UNSAT (6.9 s), slack 8 UNKNOWN |
| H7 | Other spine pairs (A, sigma(A)), A an induced path, sigma an involution of Q5, are better | 20 random pairs with A of 11, 12 or 13 vertices, scored by the palette maxima in Q6 and Q7 (`palsearch.py`) | Q6 maxima 24-26, Q7 maxima at most 48. The bank pair (26, 49) beats all 20. The forest palette of the Q8 record reaches **27 in Q6, >= 51 in Q7 and 99 in Q8**: it is optimal at every level |
| H8 | The palette of the Q8 record carries over to Q9 | Global SAT in that palette, Q5 x Q4, 376 free vertices | Target 160 already UNKNOWN (150 s): this needs a structured search, not plain SAT |

All SAT answers were re-checked as snakes by an independent pairwise test.
The searches used one core at `nice -n 19`; every run is listed in `data/`.

### What the tests show

1. **Rigidity.** In the bank palette and along a bank walk, the snakes are
   locally maximal in a strong sense. No piece can grow, and no set of
   changes of up to 2 vertices per piece reaches 193. These
   neighbourhoods are global in the heavy coordinates: all 20-25 pieces are
   re-chosen at once. They differ from the LNS windows of milestone 20.
2. **The weak cells are necessary in this palette.** With one piece per
   cell, every Hamiltonian quotient walk fails already when every interior
   piece must have 10 or more vertices (16 pieces averaging 12.06 are needed
   for 193). Pass-through cells are the price of turning between the strong
   cells while keeping adjacent M-contents disjoint.
3. **The palette loses 1, 2 and 2 vertices in Q6, Q7 and Q8.** Each half
   of a single-crossing palette snake is a palette Q8 snake. The other half
   uses the swapped palette, and the swap is a symmetry. Such a snake
   therefore has at most 97 + 97 = 194 vertices, that is 193 edges. The
   bank reaches 97 + 95. Snakes with 2 or more crossings are not covered by
   this bound.
4. **Sanity checks.** The quotient model recovers the a(8) witness from its
   walk, but cannot prove the (true) impossibility of growing it. The bank
   palette does not reproduce a(6), a(7) or a(8): its tower maxima are 25,
   48 and 96 edges, against 26, 50 and 98. The forest palette of the Q8
   record reproduces all three: it reaches 26, >= 50 and 98 edges.
5. **Palette ranking.** Among symmetric spine-path palettes the bank pair is
   the best one sampled, but every spine-path palette tried loses at least
   2 vertices in Q7. The structurally different forest palette does not.

## 3. What this suggests about a(9)

- The 191-edge snakes form a single structural class: one spine pair in
  Q5 x Q4, 12 strong cells and 4 weak cells on two antipodal Q4 edges, and
  near-invariance under the swap of the spines. Within this class they are
  rigid. This explains why the LNS of milestones 18-20 keeps recovering bank
  entries: every local move stays in the same palette.
- The bank palette caps the halves at 97 vertices. A single-crossing snake
  in it has at most 193 edges, and it needs both halves at or near the
  palette maximum. The bank palette therefore has at most 1-2 vertices of
  room. a(9) = 196 or more would require a different palette, or
  2 or more crossings with halves that are unions of paths.
- **Most promising direction: change the palette, not the snake.** Rank
  palettes (A, B, M) of Q5 by their tower maxima in Q6, Q7 and Q8. These
  take seconds to minutes. Then search Q9 only inside palettes that are
  optimal in lower dimensions. The forest palette of the Q8 record
  (`data/pal_q8witness.json`: A and B are linear forests with 9 and 8
  vertices, |M| = 14) is the first such palette found: it is optimal in Q6,
  Q7 and Q8, whereas the bank palette is not. A larger M allows more light
  transitions per cell, which weakens the obstruction behind the weak cells.
  Plain global SAT cannot search Q9 in this palette (H8). The next step is
  the walk-and-size model of H2/H3 with walks of the Q8-record type: about
  17 visits per Q8 half, pieces of at most 8 vertices, and one weak cell per
  half. In the bank palette that model settles instances in seconds.

## Files

- `scripts/invariants.py`: all bank invariants, writes `data/invariants.json`.
- `scripts/sym.py`, `scripts/coils.py`, `scripts/museage.py`: the
  near-symmetry, coil-containment and slot-usage counts quoted above.
- `scripts/qmodel.py`: exact CNF for a fixed quotient walk (pieces, entry
  and exit vertices, cross-cell disjointness, lazy cycle cuts), with
  optional palette, size bounds and a "some piece grows" clause.
- `scripts/rigidity_grow.py`, `scripts/rigidity_slack.py`,
  `scripts/familyB_slack.py`, `scripts/q8_witness_walk.py`: H1, H2, H2', H6.
- `scripts/hamiltonian_walks.py` (SAT), `scripts/hamfree.c` (exhaustive
  branch and bound over palette pieces), `scripts/hamq.py`
  (Hamiltonian paths of Q_k up to symmetry): H3.
- `scripts/freewalk.c`: branch and bound with revisits. Its bound is too weak:
  a Q8 run was truncated after 2.5e9 nodes. Not used for any claim.
- `scripts/tower.py`, `scripts/doubling.py`, `scripts/palsearch.py`: H4,
  H5, H7 and H8, built on the milestone 20 `Model2`.
- `data/*.jsonl`: one line per instance.

Build the C programs with `gcc -O2 -o hamfree hamfree.c` in `scripts/`.
Example runs from the repository root:

```sh
python3 milestones/21-snake-structure/scripts/invariants.py milestones/21-snake-structure/data/invariants.json
cd milestones/21-snake-structure/scripts
nice -n 19 python3 rigidity_slack.py 0,73 45 2 193 1 out.jsonl
nice -n 19 python3 hamiltonian_walks.py 10 193 15 out.jsonl
nice -n 19 python3 tower.py 3 98 600 1 out.jsonl
python3 runham.py 5 3 1 1 0 0
```
