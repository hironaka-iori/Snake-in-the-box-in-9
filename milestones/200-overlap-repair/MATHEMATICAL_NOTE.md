# Round 200: overlap counting and the limit of direct trimming

## Main result and scope

A complete native census establishes an exact restriction for the specified published 50-edge Q7 parent: two independently trimmed copies, placed using any relative cube isometry, have at most 92 vertices in total when their projections are disjoint. Placing them in opposite Q8 faces therefore gives at most a 92-vertex separated two-path forest within this construction family. The maximum is attained. The result does not classify other Q7 parent shapes or bound arbitrary Q9 snakes.

This is stronger than the previous equal-trim involution census: arbitrary isometries, different trimming intervals and unequal component sizes are all included. It confirms that the saved 96-vertex forest requires changing a parent shape. No new Q9 witness or global numerical bound was obtained.

## Why overlap limits trimming and repair

Write S and f(S) for the two full parent sets, each of size 51, and let C be their intersection size. For the final two paths to have disjoint projections, every shared vertex must be removed from at least one parent. A deletion removes at most one such coincidence. Thus, if D counts omissions from the two parent copies,

$$C\le D.$$

This remains true when additions are allowed. If A counts additions and the final total is 100 vertices, set partition gives

$$100=102-D+A,\qquad D=A+2.$$

The proof counts each original and final set over a common finite vertex universe. At each shared original vertex, disjoint final selections force at least one omission indicator. Summing proves the overlap inequality. Partitioning both old and new selections into retained, removed and added vertices proves the size identity. These are checked in CollisionRepair200, together with the trimming cutoff and two interval inequalities. All six theorem dependency reports pass with no admitted statement.

For trimming alone, a total of at least 92 vertices requires D at most 10, and therefore C at most 10. This is the completeness argument for the finite cutoff used below; it is not an empirical heuristic.

## Complete trimming census

The program considers all 5040 coordinate permutations and 128 translations, or 645120 relative isometries. Exact XOR difference counts find 1363 maps with at most ten intersection vertices. All other maps require more than ten deletions and cannot compete with a 92-vertex witness.

For each of the 1363 retained maps, enumerate the 66 nonnegative left/right trims of the first parent whose sum is at most ten. If its retained interval is I, the forbidden positions in the second parent are exactly the positions whose images lie in I. The longest admissible second interval is the largest gap between consecutive forbidden positions, including the two end gaps. Every competitive pair has one of these first intervals and a second interval contained in such a gap.

The resulting 89958 first-interval cases attain a maximum of 92 vertices. One witness retains positions 5 through 50, inclusive, in both parents for the map exchanging coordinates (1,4),(3,6) and translating by 126. Each component has 46 vertices and 45 edges. The native program checks every vertex pair of the saved witness for inducedness, distinctness and cross-face separation.

The complete numerical census has input and script hashes, an intersection histogram, explicit retained intervals and saved paths. It has no Lean replay of all numerical entries. The cutoff logic is checked separately in Lean. The exact 92 restriction is therefore a native finite result for this parent-and-trimming family.

## Direct bounds at the two best full-parent placements

The two minimum-overlap isometries have two coincident vertices each. In parent-position notation their collision pairs are

$$ (38,43),(43,38), \qquad (4,38),(38,4). $$

For retained intervals [a,b) and [c,d), with endpoints between 0 and 51, neither collision pair may lie in both retained intervals. Those two exclusions imply

$$ (b-a)+(d-c)\le89 $$

for the first map, and at most 92 for the second. Lean checks both interval implications. The identification of these positions with the concrete maps remains supplied by the native placement data. This distinction prevents the interval lemmas from being mistaken for a full proof-assistant replay of the placement census.

## Coupled repairs with arbitrary final shapes

The repair model permits two independently variable induced Q7 paths, each with 49 to 51 vertices and total 100, with all endpoints free. Their projected sets must be disjoint. The paths need not remain images of each other. A directed circuit through one dummy vertex enforces connectedness of each path; the selection constraints include every cube edge between selected vertices, so disconnected cycles cannot satisfy the path query.

At the two minimum-overlap placements, the queries with at most four total parent omissions return INFEASIBLE in 3.125 and 2.594 seconds. Consequently, within either of these two starting placements, a 100-vertex repair needs at least five omissions and at least three additions. These exclusions are native solver results without Lean contradiction certificates.

The same placements with at most six total omissions remain UNKNOWN after 60.032 and 60.000 seconds. These time limits provide no six-omission exclusion.

To extend the four-omission question to every relative cube isometry, the checked overlap inequality permits restriction to maps with C at most four. The complete native catalogue contains sixteen maps: fourteen involutions and one pair of mutually inverse noninvolutions. Swapping the parents and applying the inverse map identifies that last pair, leaving fifteen repair cases. Omission ordering is imposed only for involutions, where applying the involution and swapping the two final paths exchanges their omission counts.

The two minimum-overlap cases are excluded. The remaining thirteen representatives were deferred before model solving because the available-memory requirement was not met. The first launch refusal and subsequent bounded waiting records are retained. No other applications were stopped. No complete four-omission exclusion for all sixteen maps is claimed. The catalogue, model generator and resume script are saved for continuation.

## Whole-manuscript source review

The review covers every line of the 8964-line main source and the 961-line frontier explanation as they stood before this round's edits. Three bounded reviews cover nonoverlapping main-source ranges; the construction review also covers the entire explanation. Consequential findings were checked against the cited local records.

The revision corrects a historical sentence that described unsuccessful 66-edge and 92-edge merger searches as completed constructions. It explicitly introduces the different quotient used for triangle-based endpoint classes, qualifies finite-walk averages by boundary terms, distinguishes an older floor-eighteen target from the current floor-fifteen profile, defines the loss and window total at first use, explains why one unordered involution contact means two intersection vertices, and makes representative transport unambiguous. The abstract and current frontier are updated. Authors and local hyperlink settings are preserved.

This is a complete source review, with selective checking of underlying records. It is not an independent rebuild of the archived 235 proof or a replay of every finite certificate. The archived 235 qualification and conditional status of 233 and 234 remain unchanged.

## Handoff and pause

The user requested a pause after this round. Complete publication and then set the goal to paused. No worker should remain running. Resume research only on a new user request.

The first next step is the thirteen unrun four-omission repair representatives, using scripts/resume_catalogue.py after the memory requirement is met. If all are excluded, the result would establish a five-omission minimum for every relative placement of these parent copies; it would still concern this repair family. If a witness is found, check its complete paired-path geometry and then attempt the opposite-face completion. A 100-vertex face needs 93 compatible opposite-face vertices for 192 edges, 95 for 194 or 97 for 196.

If four-omission witnesses do not exist, larger coupled repairs can be considered with the overlap catalogue extended to the corresponding omission budget. The two existing six-omission timeouts should not be rerun unchanged without stronger constraints or a different search strategy. The original optimum question and the 196 conjecture remain open.
