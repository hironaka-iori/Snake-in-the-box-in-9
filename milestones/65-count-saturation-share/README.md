# Milestone 65: count saturation and empty-square shares

Nine stronger empty-square share bounds and a direct geometric exclusion have passed Lean. All **17 modules and 104 theorem-dependency audits** passed. An independent verifier checks **479 branch certificates and 217 propagation steps**, their geometric premises, and both finite graph certificates.

The geometric exclusion removes a transition present in every cycle of the saved 118-state critical family. The remaining 217 transitions form an acyclic graph with maximum walk length **19**. This concerns that restricted family. It does not show that all snake windows belong to the family or establish a new global bound. The contributor-checked interval remains **191 <= a(9) <= 235**.

## Count saturation

At an internal snake vertex, let K be the 21 opposite corners in coordinate pairs that avoid its incoming and outgoing directions. Its singleton count is the number of absent vertices in K. Suppose this count is at most h, and D is a set of vertices already proved absent. If declaring q absent would give more than h absent corners, then q must be selected:

\[
|K\cap(D\cup\{q\})|>h\quad\Longrightarrow\quad q\text{ is selected}.
\]

New selected vertices force further absences through the induced-path degree bound. These deductions can alternate. A branch ends in either a contradiction or a certified set of absent vertices from which an empty-square share lower bound follows. The neighbour choices from milestone 64 cover every actual snake, so the minimum surviving branch bound applies to the original window.

The general proof supports lower and upper count deductions; the nine completed instances use **upper count bounds only**. Unused count assumptions have been removed. In particular, a truncated count of six is interpreted as the interval [6,21], and supplies only the universal upper bound 21 here.

The nine share improvements are transitions 7, 10, 11, 44, 45, 57, 58, 91 and 115. They use 443 branch certificates. The separate exclusion of transition 24 uses 36 branches; its simpler direct proof below avoids those branches entirely.

## A direct terminal count restriction

For six distinct coordinates a,b,c,d,e,f, consider a snake segment whose eleven directions are

\[
(a,b,c,d,a,e,d,c,f,e,d).
\]

The singleton count at its tenth internal vertex is at least three, without conditions on the other counts.

To prove this, translate the first vertex to zero and relabel the six coordinates as 0 through 5. The selected vertices are then

\[
0,1,3,7,15,14,30,22,18,50,34,42.
\]

Vertex 1 already has selected neighbours 0 and 3, so its neighbour 33 is absent. Vertex 7 already has selected neighbours 3 and 15, so its neighbours 6 and 39 are absent. These three vertices are opposite corners of squares through vertex 34, in coordinate pairs (0,1), (2,5), and (0,2), respectively. These pairs avoid the incoming and outgoing directions 4 and 3. Each square therefore contributes to the singleton count at 34, proving the lower bound three. The arbitrary-coordinate and arbitrary-position interpretation has passed Lean.

Transition 24 of the saved family requires a terminal count of two, so it is impossible. Removing this single transition makes the family acyclic. A checked integer rank increases by at least one along every remaining transition, ranges from zero to 19, and has an attaining walk of 19 transitions. Thus every consecutive run entirely contained in this retained family has length at most 19.

## Separate effects of the two improvements

Retaining all 218 transitions and applying only the nine share gains gives exact normalized minimum cycle mean

\[
\frac{9961}{2400}=\frac{1991}{480}+\frac{1}{400}.
\]

An exact integer potential and an attaining cycle certify this value. Removing transition 24 instead destroys all cycles of the restricted family. No minimum-cycle-mean claim is assigned to the resulting acyclic graph.

The raw search proposes 110 exclusions in total. Only transition 24 is certified and used in the checked exclusion graph. The remaining 109 proposals are research data, not proved exclusions. The restricted acyclicity result does not determine how frequently a full snake can leave and re-enter this family. That missing global accounting prevents an improved upper-bound claim.

## Reproduction and evidence

- `scripts/search.py` records candidate count deductions on the complete saved family.
- `scripts/compact.py` reduces the selected traces to their necessary facts.
- `scripts/prepare_lean.py` generates the nine share instances; `--exclusion` generates the selected contradiction.
- `scripts/prepare_graphs.py` generates the two finite graph certificates.
- `scripts/replay.py --resume` replays current sources and reuses only matching completed modules.
- `scripts/verify.py` independently reconstructs the 21-corner sets, joint neighbour choices, reduced deductions, share values, and exact graph certificates. It also audits current source hashes, replay completion and printed theorem dependencies.
- `data/verification.json` and `data/lean-audit.json` record the successful independent and Lean checks. Imported earlier modules are reused, and the global contributor proof is not rebuilt by this round.
- `logs/build-record.json` records all 17 completed modules. Earlier failed diagnostic logs are retained as development history and are superseded by the successful current module logs.

## Next step and manuscript schedule

Integrate the direct terminal-count restriction into the complete direction/count model using sufficient direction history, then recompute the complete graph potential and account for boundary losses. The eleven-direction condition must be preserved exactly; equality of overlapping shorter canonical labels must be checked before using a smaller history representation. Combining the new shares with inherited shares uses their maximum at the same charged centres, never their sum.

This completes research round **9 of 10** after manuscript revision 56. The next full paper rewrite is scheduled for milestone 66. The repository paper and existing editor mirror are unchanged this round; the previously recorded compilation limitation is unchanged.
