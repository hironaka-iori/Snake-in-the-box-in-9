# Round 221: independent long-model rational certificate audit

The saved certificates pass exact arithmetic inspection. At both fixed roots, the continuous model admits a point satisfying all saved rows and the complete families of occupancy-cycle, subset-forest and disagreement-cycle parity inequalities. The saved mixtures have objective exactly 94 and inherit all three families. This result concerns fractional feasibility in the fixed-parent model; it does not construct a Boolean partner.

## Points and provenance

| Root | Exact objective | Saved rows | Fractional coordinates | Largest denominator bit length |
|---:|---:|---:|---:|---:|
| 0 | \(2507137819890885477/26128236866583647\) | 3,145 | 424 | 59 |
| 78 | \(388107824092577/4052758842992\) | 3,110 | 425 | 43 |

Both objectives exceed 94. All 574 variable bounds and every equality and inequality were evaluated with rational arithmetic. The points lie below the independently reviewed upper certificates \(95955197/10^6\) and \(95763979/10^6\). Their gaps are positive, so this review makes no claim of exact LP optimality.

The long-model hashes and preserved square-model prefixes agree with the separately frozen `data/long-audit.json` review. That review supplies added-row validity and upper-certificate inspection. This audit checks the new point, flow and potential data directly and matches their model, source and predecessor hashes. The square baseline and earlier rational addendum remain unchanged.

## Complete occupancy-cycle family

For each root, all 337 saved edge-deleted potentials have the correct source value, target reachability, and exact closing bound. The audit verifies all 113,232 remaining-edge difference inequalities. With \(c_u=1-x_u\), telescoping along a cycle with edge \(st\) removed gives

\[
p(t)\le 2\sum_{u\in C}c_u-c_s-c_t.
\]

The saved closing bound \(p(t)+c_s+c_t\ge2\) therefore proves \(\sum_{u\in C}x_u\le |C|-1\) for every simple cycle. This uses feasible potentials; shortest-path optimality is unnecessary. The minimum occupancy cost is exactly 1, attained by saved squares with vertex sets \(\{20,22,84,86\}\) and \(\{8,9,10,11\}\), respectively.

## Complete subset-forest family

The flow capacities were reconstructed from the exact point. Each undirected edge contributes two directed arcs of capacity \(D y_{uv}\). Each vertex also has a sink arc: capacity \(D\) at the fixed root, \(D e_u\) at each possible opposite endpoint, and zero at other vertices. Here \(D\) is the least common multiple of the point's denominators.

| Root | Scale \(D\) | Nonzero flow entries | Total arc capacity bit length |
|---:|---:|---:|---:|
| 0 | 313538842399003764 | 13,694 | 66 |
| 78 | 8105517685984 | 12,222 | 51 |

For each root, every one of the 158 source flows passes all 832 capacity bounds, conservation at every intermediate vertex, the source/sink balance, and supply at least \(2D x_v\). This is 131,456 capacity checks per root. All 158 exact degree equations were also checked. The minimum supply surplus is zero.

For any subset \(U\) containing source \(v\), conservation bounds its outgoing cut capacity below by \(2x_v\). Let \(B(U)\) denote the edge capacity crossing its boundary and \(E(U)\) the endpoint mass inside it. The checked degree identities imply

\[
2\sum_{u\in U}x_u-E(U)
=2\sum_{\substack{ab\text{ an edge}\\a,b\in U}}y_{ab}+B(U),
\qquad B(U)+E(U)\ge2x_v.
\]

Consequently,

\[
\sum_{\substack{ab\text{ an edge}\\a,b\in U}}y_{ab}
\le \sum_{u\in U}x_u-x_v.
\]

Thus every subset inequality follows, including those absent from the finite row list. No maximum-flow optimality assertion is needed. The independent audit uses unbounded Python integers throughout. At root 0, the total arc capacity is 60,171,307,677,381,251,448; it cannot be represented by a signed 64-bit integer.

## Complete disagreement-cycle parity family

For each edge, the audit reconstructs

\[
\delta_{uv}=x_u+x_v-2y_{uv}
\]

and checks \(0\le\delta_{uv}\le1\). The two-copy graph has 316 states. For each edge, its layer-preserving arcs cost \(D\delta_{uv}\), and its switching arcs cost \(D(1-\delta_{uv})\). Both directions are included, giving 2,696 directed arcs.

For every one of the 158 original vertices, the corresponding saved potential is zero at its layer-0 state and at least \(D\) at its layer-1 state. Every directed arc satisfies the exact potential-difference bound. This is 425,968 inequalities per root.

For a cycle with an odd marked edge subset \(F\), follow switching arcs precisely on \(F\). The lifted walk begins and ends at different copies of the same vertex. Telescoping therefore gives

\[
\sum_{e\in F}(1-\delta_e)+\sum_{e\notin F}\delta_e\ge1,
\]

equivalently every required odd-subset parity inequality. This argument covers all such cycles, with no shortest-path optimality assumption. The lower cost 1 is attained by the explicitly checked ordered squares \([0,2,6,4]\) and \([2,6,14,10]\), marking edge indices \(0,1,3\) in each.

## Exact objective 94 and limits

The saved one-edge paths \([0,2]\) and \([78,14]\) are encoded exactly. All their saved model rows and bounds pass. Mixing each with its audited point using \(\lambda=92/(Q-2)\) gives the saved target vector, coordinate by coordinate, and objective exactly 94. The weights are

\[
\lambda_0=\frac{2403797791725695524}{2454881346157718183},\qquad
\lambda_{78}=\frac{372853813555264}{380002306406593}.
\]

All target rows and bounds were checked again. Every complete family is linear in the model coordinates and holds for the actual one-edge path, so all three persist under the mixture. The targets retain 434 and 438 fractional coordinates.

The rational and flow execution records are terminal, exit 0, with no resource stop. Their elapsed times are 2.860 and 1.234 seconds, with maximum sampled private memory 50,573,312 and 37,220,352 bytes. Stream, summary, source and input hashes match. The cut and target certificates are checked directly and pinned; this review does not invent execution receipts for them.

No optimizer, compiler, search, repeated basis reconstruction or software tests were run. The generic Lean proofs and the earlier actual-path model arguments are separate from this exact native-array audit. An end-to-end Lean assembly for these concrete rational vectors, flows and potentials is not asserted. All source and certificate hashes are recorded in `data/long-primal-audit.json`; these audit files are frozen after completion.
