# Independent review of the universal five-count experiments

The two frozen experiments passed the bounded audit in `scripts/independent_universal_cycles.py`. The saved output is `data/universal-cycle-audit.json`. Previous audit files were preserved. No solver, Lean compiler, graph optimization, all-edge rule test or all-edge potential test was rerun. The script completed in approximately three seconds; a Git commit-graph warning did not prevent retrieval and hash verification of the required algorithm source.

## Frozen results

| Experiment | Rule count | Profile | Cycle length | Mean | Saved potential range | Comparison | Integer part |
|---|---:|---|---:|---:|---:|---:|---:|
| Universal sum at least 21, retaining the middle-cap rule | 11 | Completed local floors | 26 | $6309/13$ | $7656/13$ | $4781536/20303$ | 235 |
| Same | 11 | Conditional floor18 | 5 | $496$ | $602$ | $551765/2348$ | 234 |
| Universal sum at least 22 | 10 | Completed local floors | 26 | $6309/13$ | $7656/13$ | $4781536/20303$ | 235 |
| Same | 10 | Conditional floor18 | 6 | $496$ | $602$ | $551765/2348$ | 234 |

The completed cycles each have total weight 12,618. The conditional cycles have total weights 2,480 and 2,976 respectively. “Completed” describes the pre-existing local-floor profile; both experiments still assume unproved sum inequalities and do not establish an actual-snake upper bound.

Every saved edge was checked against the original full direction/history/count key and raw endpoint indices. Membership in the retained diagram, cycle chaining, survival of the saved deletions, reconstructed original credit and profile floor, and the final edge weight were checked independently. Direction-table, diagram, block and root data were matched to their Lean source literals. All applicable rule deficits are zero at both placements on every cycle edge. The recorded bonuses therefore vanish independently of their saved values.

Each compressed potential was decompressed and checked against its recorded uncompressed hash. All have 1,601,856 signed 64-bit entries, minimum zero and the stated maximum after scaling. Every saved cycle edge has zero potential slack. The comparison was recomputed exactly as

$$
\frac{1098960d+8p+R}{4200d+p}.
$$

The producer's whole-graph potential assertions, restricted-weight hashes and evaluator source were inspected and pinned. This review does not independently reproduce those all-edge checks. It independently verifies the attaining cycles and potential bytes/ranges, and relies on the producer for the matching lower certificates over all edges.

## Alignment, deletion counts and coefficients

The two six-transition windows begin at positions 2 and 3 of the nine-transition extension. Their count windows begin at positions 0 and 1 of the six-count code. Both placements can delete an edge; only the latter contributes excess credit. All rules used here have reversal-symmetric bounds and selected positions. Symbol 6 denotes $[6,21]$, and applicability requires each complete represented interval to satisfy the condition. A sum deficit permits deletion only when every selected symbol is below 6. Other deficits contribute through the maximum of competing credits.

The universal-total21 experiment removes 170,409 of 4,947,008 original edges, leaving 4,776,599. The universal-total22 experiment removes 225,900, leaving 4,721,108. The deletion sets satisfy

$$
D_{\text{middle cap}}\subseteq D_{\text{universal }21}
\subseteq D_{\text{universal }22}.
$$

They remove respectively 59,112 and 114,603 more edges than the earlier middle-cap experiment. These set inclusions and counts were checked; deletion predicates were not reevaluated over the entire graph.

All saved cycle deficits vanish, so changing nonnegative coefficients within either frozen family leaves those cycle weights unchanged. The cycles give coefficient-independent mean ceilings $6309/13$ and $496$. The saved all-edge computations attain them with coefficients 24. Further coefficient search within those families cannot raise the means. The report does not assert that either saved potential range is the smallest possible range.

## Native evidence boundaries

| Probe restriction on $012345$ | Status | Native seconds | Added cycle cuts |
|---|---|---:|---:|
| Total at most 20 | `UNSAT_UNCERTIFIED` | 2.656 | 0 |
| Total at most 21 | `UNSAT_UNCERTIFIED` | 8.547 | 0 |
| Total at most 22, short attempt | `UNKNOWN` | 20.015 | 0 |
| Total at most 22, longer attempt | `UNSAT_UNCERTIFIED` | 28.391 | 5 |
| Total at most 23 | `SAT_LOCAL_WITNESS` | 3.078 | 8 |

The stronger total-at-least-23 candidate comes from the longer native run. It is not a checked local theorem. The short run remains `UNKNOWN`; its record is preserved. The saved local witness at total 23 has counts $[6,3,6,2,6]$. The separately supplied witness audit reports six components. This review pins that record without repeating its adjacency verification. Such a local witness does not construct a complete snake, but it prevents treating a stronger universal local total bound as established by this model.

The previously proposed endpoint-cap/middle-cap/total-at-most20 probe also returned native UNSAT, with zero added cuts. Its conclusion is subsumed by the unconditional total-at-most20 probe. No further probe is requested by this review.

## Candidate23 transfer without another full scan

The universal-total22 completed cycle has 26 edges, hence 52 tested placements. Its conditional cycle has 6 edges, hence 12 placements. **None of these 64 placements has canonical direction shape $012345$.** Accordingly, the minimum five-count sum over matching windows is undefined: the set is empty. No positive candidate23 demand and no candidate23 deletion occurs on either cycle.

The direction shapes at the two placements of the completed cycle are $012032$, $012034$, $012310$ and $012314$. For its conditional cycle they are $012034$, $012301$, $012304$ and $012310$. Thus this conclusion does not depend on interpreting symbol 6 as an exact count.

Suppose the universal-total22 graph is changed only by raising that rule's lower bound from 22 to 23, with the same bounds, placements, nonnegative coefficients and maximum-credit convention. The new edge set is a subset of the old one, and the weight of each surviving edge cannot decrease. Therefore the old inequality

$$
p+\pi(v)\le d\,w(u,v)+\pi(u)
$$

continues to hold with the new weights. The two cycles above survive with identical weights, since neither contains a matching window. Their cycle means remain $6309/13$ and $496$ and attain the lower bounds supplied by the old potentials. Under the existing all-edge certificate, this proves equality of the means after this single modification without building a new graph.

The old potential functions and their ranges remain valid, so the same integer comparisons remain available. This argument neither computes the new removal count nor proves that a newly optimized potential has the same range. It is an arithmetic transfer from the saved finite certificates, with no new Lean proof or graph23 result file claimed. Even reducing the ranges to zero cannot exclude 235 or 234 at these mean ceilings: the corresponding comparison numerators exceed those integer multiples of the denominators by 23,337 and 4,064 respectively. A full rescan is therefore unnecessary to determine whether this isolated strengthening improves those integer conclusions.

## Pins

The JSON contains all underlying source pins, decoded cycles, rule tests at both placements, potential-file pins, and the explicit empty candidate23 match sets. Paths below are relative to `milestones/115-total-count-certificate`.

| File | SHA256 |
|---|---|
| `scripts/independent_universal_cycles.py` | `7fa8f57bce1164202381082f17bbd62e91c4d40dd274a14382068432fc37923b` |
| `data/universal-cycle-audit.json` | `9ad482cd3f8b24d924400fc6d3f731fe62d968205cf1189c6bc6134779d98ec2` |
| `data/universal345-total21/results.json` | `3a985899027384f2d13b1eb204d51567bcf3ddcf2cc65538e43f4b3fb499ef78` |
| `data/universal345-total22/results.json` | `4840bf5acb53fc82eda4ffdf31de46aa71969f15a8a75cf80c73e862b93ac6cc` |
| `data/probes/012345-total22-long.json` | `1a846c48ef92253f9996d6b8ba18f21ac4739a3bd97ef4111d2e4deac89fd574` |
| `data/probes/012345-total23.json` | `55f996dfe4b326899856fc5e4722cf63f054fecf685cc6bd37debffed305f6c6` |
| `data/witness-audit.json` | `406325336c13a5f7e15e781605a5ec1e901ac4e98aee97e92ddb48de494a6aa4` |
