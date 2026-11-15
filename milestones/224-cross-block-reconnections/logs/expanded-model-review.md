# Round 224 expanded two-block model review

Review date: 15 November 2026. Finding: the inspected width-44 model includes the specified family of simultaneous equal-length replacements and uses no mutual-contact condition or round-193 closure premise. No invalid pruning or unintended individual crossing restriction was found.

## Inspected material and identity

Read every line of `prepare_expanded.py` (43 lines), `prepare_expanded_solver.py` (17 lines), and the generated `joint_regions44.py` (75 lines), including its complete semantic difference from the previously reviewed width-33 solver. Parsed all 301 context records and 602 parts in `regions44.json`; independently reconstructed their geometry. The JSON has 181609 text lines; this was a complete structured-data audit rather than a manual line-by-line prose reading.

| Artifact | SHA256 |
|---|---|
| `scripts/prepare_expanded.py` | `19519891b9985a7d907adf307c92b69d1e6760627924beabaa16a953a5b2301a` |
| `scripts/prepare_expanded_solver.py` | `8cba52c8432be6e010ca07b0c5fe63aa94cbc5b713c817379236c06adfba97bc` |
| `scripts/joint_regions44.py` | `de09b42cc6dc39c735039606dbce41676b8e86df7e681489f31b910bf0423401` |
| `data/regions44.json` | `c2c5b1465726c4e8c2ab142a1524e171cfeb992cb66d906475e9d1e2e766ec0b` |

The region source pin remains the reviewed round-223 seed result, SHA256 `3df4967aaf726c4db222d577f13507b227425c82a57607a46354905cd2f91932`. Its preparation-script pin agrees. Only this review log was written. No solver, compiler or software tests were run. The read-only exact reconstruction was the permitted mathematical audit. Native results from the live expanded search were not audited or treated as an exclusion certificate here.

## Complete maximal-window coverage

The windows are exactly

\[
[a,a+44],\quad 0\le a\le6,
\qquad [c,c+44],\quad100\le c\le142.
\]

Their number is $7\cdot43=301$. Every first window contains blocker index 7 strictly inside; every second window contains blocker index 143 strictly inside. The first ends no later than 50 and the second starts no earlier than 100, so their interiors and anchors are disjoint.

For any original interval $[r,s]$ of at most 44 edges with $r<7<s$, choosing $a=\max(0,s-44)$ gives a containing first window in the displayed range. For $r<143<s$, choose $c=s-44$; then $100\le c\le142$. Padding with unchanged original positions converts each shorter equal-length replacement into a 44-edge replacement without changing the resulting path. Thus the maximal contexts cover all simultaneous short replacements in the specified family, although contexts can overlap in the paths they represent.

Independent enumeration found 280 possible short intervals containing 7 and 946 containing 143. Every interval is contained in a recorded maximal window. The JSON context order and interval pairs agree exactly with the expected 301 pairs.

The coverage retains the fixed seed alignment, both block anchors and all outside positions, appends vertex 24 after retained endpoint 88, preserves each block's original length, and requires four total bit-8 crossings. Unequal-length replacements, longer blocks, a different endpoint or seed, and other total crossing counts remain outside this model.

## Domains, peeling and parity

The forbidden-set construction correctly removes retained vertices, retained nonanchor neighbours, vertex 24 and all of its neighbours, then restores the part's own anchors. No lower-face restriction is applied to either domain. This is necessary because the first maximal window can include the original crossing at edge index 46, and replacement crossings can also be redistributed between the blocks.

Every nonanchor on a valid replacement has two selected neighbours. Deleting nonanchors of current domain degree below two, then keeping only the component of the first anchor, preserves every valid replacement. Anchors are exempt from degree-two peeling. A 44-edge path has 45 vertices. Its two anchors have the same parity, so it requires 23 vertices of their parity and 22 of the other parity. The stored `required_even` value is therefore 23 for an even first anchor and 22 for an odd first anchor. Disconnection, fewer than 45 vertices, or insufficient parity capacity are valid exclusions.

The independent reconstruction used Hamming-distance adjacency, direct forbidden-contact conditions, synchronous degree deletion, a separate connectivity traversal and a replay of every saved peeling step. It found:

- Agreement on all 301 retained sets and all 602 initial/final domains.
- Agreement on all anchors, intervals, 45-vertex targets, required parity counts, rejection lists and context statuses.
- All 5713 saved peeling steps valid, with matching terminal cores.
- 107 statically excluded contexts and 194 pending contexts.
- At part level, 117 disconnection reasons and 114 each of size and colour reasons. Reasons overlap.
- Maximum final domain sizes 123 and 125 for the two respective parts.

No context contains a `contact_candidates` or individual `crossings` field. The even-count requirements occur as follows: first part, 172 contexts requiring 23 and 129 requiring 22; second part, 154 requiring 23 and 147 requiring 22. No discrepancy was found.

## Combined crossing constraint

The fixed crossing count uses exactly the original edges outside the replaced edge-index ranges $[a,b)$ and $[c,d)$. This includes the retained boundary edges correctly. Appending 24 to 88 changes bit 6, so contributes no bit-8 crossing. Consequently the replacement paths must have a combined crossing count

\[
4-\text{fixed crossing count}.
\]

Every stored count agrees with an independent reconstruction. The original numbers of crossings inside the two windows, and their required combined replacement count, have the following distribution:

| Original first-window count | Original second-window count | Required combined count | Contexts |
|---:|---:|---:|---:|
| 0 | 1 | 1 | 69 |
| 0 | 2 | 2 | 60 |
| 1 | 1 | 2 | 92 |
| 1 | 2 | 3 | 80 |

The generated solver correctly collects conjunction variables for every available vertical edge in both parts and imposes one equality on their sum. It imposes no individual crossing equalities. In particular, the first replacement may enter the upper face even when its original window has no crossing, provided the combined count and endpoint geometry permit it. Retaining the width-33 individual counts here would have been unjustified; that restriction is absent.

## Generated solver and verification boundary

The preparation script's intended changes all appear in the generated source: the input is `regions44.json`, target size and even count are read from each part, the contact-selection inequality is removed, and the two individual crossing equalities are replaced by the combined equality. The source description correctly states that no short-move closure premise is used.

The remaining constraints and assembly are unchanged in their mathematical role. Selected anchors have degree one, selected nonanchors degree two, and all cross-part equalities and adjacencies are forbidden. The windows remain separated by at least 50 original edges, so no intended consecutive pair crosses between their vertex sets. Each feasible degree graph consists of the anchor-to-anchor path and possibly cycle components. Recorded cycle cuts validly exclude each selected cycle. When no cycles remain, all 45 selected vertices belong to the replacement path.

The assembly retains the original outside positions, inserts both 44-edge routes and appends 24. It still has 193 vertices. The source checks distinctness, every unordered adjacency pair and exactly four bit-8 crossings before accepting a witness. The initial serialized model and all recorded cycle cuts are jointly required for replay.

The inherited `COMPLETE_COVERAGE` status means all contexts received entries, including potentially unresolved ones. Any final exclusion must separately confirm that every entry is either a valid static exclusion or native `INFEASIBLE`; unknown and timed-out entries remain unresolved. No expanded-search outcome is established by this model review.

The proposed separate width-33 run without contact restrictions had not been supplied as a reviewed artifact in this assignment. Removing that dependency from its result requires inspection of the actual contact-free source and evidence, including any static rejection logic. This report establishes that independence for the inspected width-44 model only.
