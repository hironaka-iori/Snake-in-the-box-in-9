# Round 225 source and model review

Review date: 15 November 2026. Finding: no correctness issue was found in the reviewed width-dependent model, inherited containment exclusions, or witness reconstruction. All statements below concern the fixed seed, retained positions and anchors, endpoint-24 extension, and exactly four bit-8 crossings. They imply no global snake bound.

## Scope inspected

Read all 54 lines of `scripts/prepare_width.py`, all 80 lines of `scripts/joint_regions.py`, all 58 lines of `scripts/run_regions.py`, and all 142 lines of the ready `lean/Simultaneous225.lean`. Consulted the frozen round-224 contact-free width-44 inputs and combined statuses, whose hashes match the preceding independent reviews. Independently enumerated the containment relations and maximal-window coverage for all widths 34–43. Reconstructed every noninherited region in the width-34 through width-38 input files present at the audit snapshot, including all 5995 saved peeling steps. This was a read-only exact mathematical audit, not execution of the model preparation or search programs.

Only this review log was written. No optimizer, compiler or software tests were run. Live native outcomes and newly created input files after that snapshot are outside this bounded report. Source inspection of the Lean file does not establish a compiler result or numerical certificate.

## Maximal windows and inherited exclusions

For width $w$, the program enumerates exactly

\[
[a,a+w],\quad0\le a\le6,
\qquad[c,c+w],\quad144-w\le c\le142.
\]

There are $7(w-1)$ contexts. Both blockers, at indices 7 and 143, lie strictly inside their corresponding intervals. For every $34\le w\le43$, the windows remain disjoint: the first ends by 49 and the second begins no earlier than 101. Every shorter block containing the corresponding blocker can be enlarged to one of these windows, preserving unchanged original positions. For the first block $[r,s]$, choose $a=\max(0,s-w)$; for the second choose $c=s-w$. Independent enumeration confirmed coverage for every allowed shorter interval at all ten widths.

Containment uses the closed interval inequalities for each corresponding pair. If a candidate exists in a smaller context, its 191-edge path before appending 24 is unchanged outside the smaller open interiors and hence outside the containing width-44 interiors. The additional padding vertices stay in their original positions. The containing anchors remain original vertices, both padded replacement lengths are 44, and the resulting complete path and its four crossings are unchanged. Thus the candidate would satisfy the contact-free width-44 necessary model. A valid exclusion of that parent excludes the smaller context.

The source uses only parent statuses `STATIC_EXCLUDED` and `INFEASIBLE`. It never inherits an exclusion from `UNKNOWN` or `TIME_LIMIT`. Parent and current seed arrays agree. The containing width-44 family has no mutual-contact condition, individual crossing allocation or lower-face restriction that could invalidate this transfer. Static exclusions retain their geometric status and native infeasibility retains its native status. Containment does not turn either into a Lean numerical certificate.

The complete independent containment counts are:

| Width | Contexts | Inherited exclusions | Remaining before new static reductions |
|---:|---:|---:|---:|
| 34 | 231 | 197 | 34 |
| 35 | 238 | 199 | 39 |
| 36 | 245 | 201 | 44 |
| 37 | 252 | 203 | 49 |
| 38 | 259 | 205 | 54 |
| 39 | 266 | 207 | 59 |
| 40 | 273 | 209 | 64 |
| 41 | 280 | 210 | 70 |
| 42 | 287 | 211 | 76 |
| 43 | 294 | 211 | 83 |

For every stored inherited row in the audited inputs, the chosen parent, its status, and the complete `all_parent_ids` list agree with independent reconstruction.

## Domains and colour counts

For a noninherited context, the forbidden-set construction removes retained vertices, neighbours of retained nonanchors, vertex 24 and its neighbours, then restores the part's own anchors. Both replacement domains may use either cube face. This is the necessary retained-position and endpoint-separation condition. The original seed has only the two nonattachment contacts with 24 at indices 7 and 143; those positions are removed from the retained set.

Every nonanchor on a valid replacement has two neighbours on that replacement. Repeated deletion of domain vertices of degree below two, while exempting anchors, is sound. Every valid replacement lies in its first anchor's component, so the subsequent connectivity reduction is also sound. Disconnection of the other anchor, fewer than $w+1$ vertices, or inadequate parity counts are valid static exclusions.

The required number of even vertices is

\[
\begin{cases}
\lfloor(w+2)/2\rfloor,&\text{first anchor even},\\
\lfloor(w+1)/2\rfloor,&\text{first anchor odd}.
\end{cases}
\]

For odd $w$, both colours occur $(w+1)/2$ times. For even $w$, the first anchor's colour occurs $w/2+1$ times and the other colour $w/2$ times. The source formula is therefore correct for both cases. The second anchor has the required parity because it is $w$ original path edges away.

Independent reconstruction used Hamming-distance adjacency, direct contact conditions, synchronous degree deletion and a separate component traversal. It reproduced all saved initial/final domains, anchors, retained sets, colour requirements, crossing totals and reason lists in these input snapshots:

| Width | Inherited | Newly static | Pending |
|---:|---:|---:|---:|
| 34 | 197 | 12 | 22 |
| 35 | 199 | 15 | 24 |
| 36 | 201 | 13 | 31 |
| 37 | 203 | 8 | 41 |
| 38 | 205 | 0 | 54 |

All 5995 recorded peeling steps had the required current degree, and their terminal cores agreed. No discrepancy or invalid rejection was found. Pending input counts describe model preparation, not terminal solver outcomes.

## Crossing allocation

The fixed crossing count includes exactly the original edges outside the two replaced edge-index ranges. Since appending 24 to 88 changes bit 6, the combined replacement crossing count must be four minus that fixed count. The program imposes precisely that sum.

For each part, the number of bit-8 crossings has the parity of whether its two anchors lie in different faces. Writing this number as `parity + 2*half` is therefore necessary. The upper bound `replacement_crossings // 2` on `half` cannot exclude a feasible allocation: each individual nonnegative crossing count is at most the combined total. The combined equality supplies any tighter bound needed when that part's parity is one.

All candidate contexts at widths 34–43 have a nonnegative total, at least the sum of the two required parities, and the correct combined parity. These constraints do not retain the obsolete fixed zero/one allocation. In particular, at width 34 the second window $[130,164]$ contains two original crossings; both even allocations $(0,2)$ and $(2,0)$ remain permitted by the equations. At larger widths the first window may itself include crossing edge 46. No lower-face restriction is imposed.

The parity restriction is also consistent with the preliminary degree model containing disconnected cycles: each cube cycle crosses the face cut an even number of times. Its use does not require assuming connectivity before the cycle cuts.

## Compatibility, cycles and witness reconstruction

Each part selects $w+1$ vertices, includes both anchors, gives selected anchors degree one and selected nonanchors degree two, and enforces the correct colour counts. Every cross-part equality and adjacency is forbidden. This is necessary because the two intervals are separated in index and have no intended edge between their replacement vertex sets. Contacts with unchanged positions are already excluded by the domains.

The selected degree graph consists of an anchor-to-anchor path and possibly disjoint cycles. The two degree-one vertices must belong to the same component. The trace beginning at the first anchor therefore reaches the second anchor; remaining components have degree two. Every recorded cycle cut requires omission of at least one vertex of that cycle and is valid for an induced replacement. With no remaining cycles, the route uses all $w+1$ selected vertices.

The assembly includes each route's anchors once, retains the original positions outside the open interiors, and appends 24. Equal replacement lengths preserve the 192 original path positions, giving 193 vertices after extension. Before saving a witness, the source checks distinctness, every unordered adjacency pair and exactly four bit-8 crossings. No witness was executed or independently verified in this source-only review.

The serialized initial model and any subsequent recorded cycle cuts together determine a query. `COMPLETE_COVERAGE` means all requested contexts received entries; it does not imply exclusion if any entry is `UNKNOWN` or `TIME_LIMIT`. Inherited entries must remain tied to their pinned excluded parent. The wrapper's `ACCEPTED_NATIVE_RESULT` means normal resource-supervised completion, not a mathematical infeasibility claim.

## Wrapper and Lean-source observations

`run_regions.py` passes the requested width and arguments to the reviewed solver, pins the source and corresponding region file, records resource conditions and output hashes, checks that its pins did not change, and distinguishes interrupted execution from a normal exit. It does not silently convert an interrupted or unknown result into an exclusion. One solver search worker is configured in the model source. This review did not exercise the process or resource handling.

The ready `Simultaneous225.lean` supplies two appropriate generic statements. `replaceTwoBlocks` constructs a whole indexed induced path from local injectivity/inducedness, agreement outside the interiors, retained-position separation and mutual separation; it does not assume whole-candidate injectivity or inducedness as a premise. `agreement_of_enlarged_intervals` establishes the basic containment implication for agreement. Their mathematical scope supports the written assembly and padding arguments. Concrete domain arrays, context enumeration, parent exclusions and native contradiction results remain separate obligations. No compiler success is asserted by this report.

## Artifact hashes

| Artifact | SHA256 |
|---|---|
| `scripts/prepare_width.py` | `618a3aab17802890e0b2df0db0eded20ff3d97ddfedf38cd5c3f11ae6425213b` |
| `scripts/joint_regions.py` | `bf4220652446cca29f1b3967a9267d66902b1f29d220298666913c193ea5f7ab` |
| `scripts/run_regions.py` | `0ff0441a7c90399ff7db9002043bb45bbd754627b623fb2e4c0de00989ae50e0` |
| Initial `lean/Simultaneous225.lean` snapshot | `b002d76d8b2c98824adf70c4c266b9dbc7e5a30a5678e0d8c3233165b0a2661d` |
| Round-224 `data/regions44.json` | `c2c5b1465726c4e8c2ab142a1524e171cfeb992cb66d906475e9d1e2e766ec0b` |
| Round-224 `data/combined44.json` | `c4428697e1561f1c5f4e37928827322d59feed70b5df3bbf09dea0808dbbfb4d` |
| `data/regions34.json` | `1bd89121f2ba89dde6ce74a3174bbaeda327684c4db02b915335902ca10fb017` |
| `data/regions35.json` | `8a99767126820c0af789f61623620956517b164d9f0f26dfc5e543dfb7bba0aa` |
| `data/regions36.json` | `d2020caab348d3420153d1caa64f233d58ab4c576e886195f8a0505106c35fd5` |
| `data/regions37.json` | `0ad1c5dd5bdbbeae85a3b6bc9b391ff44bdf654dbff00db7fdda0ecbf3704758` |
| `data/regions38.json` | `ddb2b38a4119f2dbeb9706f8344cc5485ce17e862d94f39605f0fa00b499eb23` |

## Lean-source update before final freeze

The parent revised the optional Lean source during this review. The final 150-line `Simultaneous225.lean` was reread completely, together with all 37 lines of the newly imported `ReplacementIndices225.lean`. The constructor and containment statements are unchanged. Arithmetic steps are now supplied by six explicit elementary index lemmas, replacing direct arithmetic automation inside the constructor. Their statements express the required separated-index, exterior-index and interval-inclusion facts. No mathematical scope change or new issue was found. This remains source review only, with no compiler outcome asserted.

Final `Simultaneous225.lean` SHA256: `2cee2bb8fe0918cc19d1c036ac45ac9021058043123a011f71a5a14e1430dbca`.

`ReplacementIndices225.lean` SHA256: `69a50aa3aa3900d31f95ff68a9256405f9d908705b67241959b59cd07bc599fd`.
