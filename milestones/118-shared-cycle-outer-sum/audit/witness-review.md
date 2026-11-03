# Independent review of the five initial local witnesses

The five saved vertex sets pass an independent direct check of the radius-four local geometry. Four have outer-four sum at most $12$ and actual middle count at least $9$. Consequently, both the unconditional proposed outer bound $13$ and the version restricted to middle count at least $6$ are false in this relaxed local model. This review establishes no counterexample among complete snakes.

All five probes use direction word $012301$, whose window vertices are $[0,1,3,7,15,14,12]$. The five entries below are actual absent-corner counts, in window order. The outer sum omits the third entry.

| Saved probe under `data/probes/` | Actual counts | Outer sum | Selected vertices | Component sizes | Saved cuts checked |
| --- | --- | ---: | ---: | --- | ---: |
| `012301-completed-cycle.json` | $(4,2,10,2,3)$ | 11 | 117 | 23,23,23,21,9,9,9 | 35 |
| `012301-conditional-cycle.json` | $(4,2,10,4,2)$ | 12 | 113 | 46,29,29,9 | 7 |
| `012301-middle6-outer12.json` | $(4,4,9,2,2)$ | 12 | 116 | 43,30,21,15,7 | 34 |
| `012301-outer12.json` | $(2,2,10,4,4)$ | 12 | 113 | 71,29,13 | 18 |
| `012301-outer13.json` | $(5,3,10,2,3)$ | 13 | 120 | 64,37,6,4,1,1,1,1,1,1,1,1,1 | 17 |

The first witness realizes exactly the outer tuple of the completed-profile target in milestone117, and the second realizes the conditional-profile target. Clipping each actual count at $6$ gives $(4,2,6,2,3)$ and $(4,2,6,4,2)$, respectively. In both cases the actual middle count is $10$, within the graph symbol's interval $[6,21]$. The saved occurrences are edges1719644/463728 at offsets1/0 for the first tuple, and edges1275421/992595 at offsets0/1 for the second. All four listed orientations are forward. The direction word is also equivalent to its reversal after coordinate relabelling; reversing it requires reversing the count tuple, and preserves the outer sum.

The verification reconstructed cube adjacency by single-bit flips, the radius-four ball around the five internal centres, and all $21$ allowed opposite corners at each centre. It checked distinct selected vertices in the ball, inclusion of the induced seven-vertex window, degree at most two, positive degree for every selected interior vertex, and at most two interior endpoints. Each witness has exactly two interior endpoints. Each component has one fewer edge than vertices, so every selected graph is a forest. Every one of the111 recorded cycle cuts is a connected induced cycle inside the ball and is not fully selected. Counts were recomputed from corner membership and checked against the saved bounds and sum cap. Current source hashes and the probe script hash match the pins in all five records. The independently recomputed results also agree with the existing witness and probe audits.

These checks concern the stated local geometric conditions; they do not reconstruct a complete assignment to all auxiliary counter variables. No solver, Lean compiler, full-graph scan or global path construction was used. The selected forests are disconnected and the boundary allows components to terminate without contributing to the interior endpoint budget. Whether any of these forests extends to a complete snake remains unresolved. Their five-count compatibility does not establish simultaneous realization of an entire saved graph cycle, its histories or adjacent windows. The observations therefore rule out obtaining the proposed bound from the present local constraints alone; an actual-snake proof could still use additional global conditions.

The earlier bounded search examined96 designated probe records from milestones109–117, including19 saved local witnesses. None had designated shape $012301$ up to coordinate relabelling and reversal. That search did not enumerate interior subwindows of all saved vertex sets. The present direct witnesses supersede the need for that additional search. Later milestone118 total-sum probes are outside this five-witness review.

The proposed inequality should not be used to delete either complete middle-symbol bucket. Both buckets contain the verified local examples at middle count $10$. Any further count-sum argument must retain the distinction between exact middle counts and the interval represented by symbol $6$.

The detailed immutable record is `data/independent-witness-review.json`, SHA256 `aca745023f289d1f96581bce33c30836bc7bc2239cc952567db0b6344f4ba297`. It contains each probe hash, source pins, exact and reversed counts, component sizes and graph-target matches. The reviewed existing records have hashes:

- `data/witness-audit.json`: `4daaafba615db6c7cf8576cafdf798ee30b63718d3947b6c74e88b7505e211b0`.
- `data/probe-audit.json`: `933cbbf3e6ce1e07e79983fb376e3a3662b1910a4d91eb6bad15a9ca0241cc60`.
- Milestone117 `data/graph-audit.json`: `13039f91dc62cc7f7b476364883a0f9126978da0daa563e1ebc74aedddf19fed`.

Only the two owned review files were written. Existing evidence and the active proof batches were left unchanged.
