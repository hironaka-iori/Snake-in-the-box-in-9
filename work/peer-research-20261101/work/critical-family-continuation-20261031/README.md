# Q9 critical-family continuation and three certified count exclusions

Frozen source checkpoint:31October2026. Local research continuation; no upload. The project reports191<=a(9)<=235, but that global proof is inherited and was not rebuilt here. This round establishes no smaller global numerical bound and performs no fresh Lean kernel replay.

## Results that can actually be used

### Three ordinary geometric count-window exclusions

The digits in a direction word name distinct coordinates. Let x0,...,x9 be consecutive snake vertices and alpha_i the singleton-square count at xi in the COMPLETE snake. Each listed conjunction is impossible; all other internal counts are unrestricted by that row.

| Directions | Impossible simultaneous conditions | Core variables/clauses | RUP steps/hints |
|---|---|---:|---:|
|012310420|alpha3=3, alpha4<=5, alpha5<=3, alpha7<=5|776/1052|353/30020|
|012310450|alpha3<=5, alpha4<=3, alpha5<=4, alpha6<=4, alpha7=3|1109/1617|1264/109753|
|012342153|alpha4=3, alpha6<=3, alpha7<=5, alpha8<=5|857/1137|284/26439|

These are ordinary computer-assisted local proofs, with explicit necessary-CNF semantics and independently parsed RUP certificates. They are not claimed as freshly Lean-checked theorems or as novel priority results. COUNT_WINDOW_PROOF.md gives the full proof for row1, and the same interpretation applies to rows2/3 with their individually audited count bounds. Each count_window_certificates/edgeNNN directory contains the complete standalone DIMACS core, LRAT proof, variable remapping, original clause indices and SHA256 manifest.

The fresh independent reader reconstructs every retained input row from the pinned original encoder, checks that ALL alpha-clause hypotheses are within exactly the displayed bounds, checks actual cube-cycle clauses, replays every hint, rejects a deliberately invalid hint and requires the final empty clause. It does not invoke CDCL or reuse the producer's proof-check result.

Translation and coordinate permutation transport the normalized exclusions to arbitrary matching windows. Endpoint clauses are used only at vertices with complete neighborhoods; no unknown boundary neighbor is set to zero. The global path supplies at most two genuine degree-one endpoint witnesses. Canonical sequential-counter threshold assignments supply auxiliary values. Thus a genuine snake satisfying a row would satisfy all its input core clauses, contradicting the checked propositional refutation.

### Critical-direction language strengthened

The authorized repository file critical-edges.json was downloaded as data:18,865 records, SHA2562a19ca61f96985b5063d8ef20534a9c5e6fe7ac9c0d21e4de451a1d4bddebc5f. The independently hashed frozen potential proves w+pi(u)-pi(v)=480 on EVERY recorded edge. Completeness of the original extraction over absent graph edges was not reverified.

The six frozen source cases are7202,7211,7215,7217,7218,7219. The current eight-case model additionally includes7203/7216. Matching all offsets/orientations removes128 old records (116/34 hits,22 overlap), leaving18,737. Bucket6 always means the entire interval[6,21]; no partial-bucket hypothesis is silently admitted. The current/frozen summaries share the same candidate-base array hashes, but this round does not load all4,957,613 current graph edges.

All three small frozen cyclic components were independently excluded as indefinite coordinate histories: the two4-cycles and one2-cycle exhaust all Q9 coordinate branches at9 model edges, or17 literal transitions. New abstract labels are allowed to reuse historically used coordinates absent from the current overlap; they are not automatically treated as fresh. The full-nine-coordinate independent oracle confirms the results.

The first222 exclusions matched exact edge IDs and therefore unnecessarily depended on count states. They project to111 distinct direction histories. Removing patterns containing shorter forbidden substrings preserves exactly the same accepted language and leaves63 patterns. Complete short-window closure then examines1181 length-three projected histories and15184 length-five histories without a bad triple;44 triples and358 five-histories are geometrically impossible. Combined with the already checked continuation patterns, the final minimal direction basis contains431 patterns.

Independent full-nine-coordinate, no-symmetry/no-dedup checks refute all431 patterns using432972 coordinate trials. The sparse reachable direction-AC product has96350 vertices and317570 edges. A separate checker verifies every allowed outgoing, all41433 forbidden outgoing, every failure/bad suffix, projection, endpoint, weight and reachable state. Two original large components remain; all other original cyclic components have no cyclic lift. Data/review:review_short_closure.py/json/md.

### Exact remaining obstruction

Every edge of the saved431-rule lifted SUBGRAPH has zero slack at mean480 under the frozen potential pulled back by projection. A reachable17-edge closed walk of weight8160 proves that this explicit subgraph still has minimum mean exactly480. This is a real exact finite-graph certificate, not a complete-snake construction.

Applying the three new count rules removes another24 source records from this explicit frozen subset, leaving18713. The new lifted subset has96211 vertices/316974 edges, two cyclic components, and still a mean480 closed walk. The total number removed from the complete current5-million-edge graph is not measured. The full graph-to-arbitrary-snake formal interpretation remains outstanding upstream.

## Additional method: recover clipped-six excess

The existing proved six-step-return theorem from milestone50 says alpha1+alpha4+alpha5>=13 for distinct-coordinate word012340. If a recorded triple totals below13 and contains a>=6 bucket, it has EXACTLY ONE such bucket. That coordinate must supply the deficit above6. Multiple requirements on one coordinate combine by maximum, not sum.

This gives positive pointwise excess on1096 frozen records. Uniform position averaging is one safe way to use pointwise gains, subject to its own global endpoint budget. After all three new exclusions and431 direction rules, a zero-gain closed walk whose counts are all below6 still attains480. Consequently upgrading only these clipped-six demands cannot remove the obstruction. This reuses an existing project theorem; it is not asserted to be a new combinatorial theorem.

## Important correction: auxiliary share searches discovered ordinary exclusions

A zero-share specialization uses the identity that for a selected charged center c and q adjacent to c,1<=d_S(q)<=9, so floor(12 E_S(q)/d_S(q)) is zero iff E_S(q)=0. Zero share can therefore be modeled by positive nonempty-face clauses, with a checked complete face domain.

Weighted-empty-face searches at caps15/31/63 initially appeared to prove five-center share lower bounds16/32/64. Backward proof-dependency analysis found that the relevant refutations did NOT use the cap, face-definition clauses or any other added objective input. Their contradiction is already a consequence of base geometry and count constraints. Those share conclusions under the original exact antecedents are vacuous, not independent nonvacuous share improvements.

The three ordinary exclusions above are the stronger and correct interpretation. Auxiliary summaries are annotated with that correction. A cold ten-second base search is UNKNOWN; the separately discovered compact pure-base RUP proofs nevertheless verify. Adding extension definitions/auxiliary search structure changed search behavior without becoming a necessary premise of the final proof. No timeout is promoted to UNSAT.

Other zero-share/upper-bound-only core-pack experiments remain separately labelled local conditional investigations and are NOT admitted as nonvacuous mean-raising rules. No raw solver return is promoted to a universal theorem without its interpretation and independently checked proof.

## Exact global arithmetic target

Assuming the project's edge-count inequality, with mean mu=p/d and actual integer-scaled potential range R,

    m <= (1098960*d + 8*p + R)/(p+4200*d),

excluding235 edges requires STRICTLY

    227*p > 111960*d + R.

At d1,R578, mu must exceed112538/227 (about495.762115). Integer mean496 suffices only with actual R<=631. Mean480 cannot cross this threshold even at R0 under that fixed boundary formula. The continued exact480 obstruction therefore prevents claiming234 from this round. Merely counting removed transitions or forbidden patterns is not a substitute for a new exact mean/range certificate.

## Reproduce

Run from this directory, Python3.12+, without -O:

    python verify_frozen_data.py
    python filter_current_cases.py
    python review_short_closure.py
    python export_count_exclusions.py
    python verify_count_exclusions.py
    python apply_count_rules.py

The first three recheck the frozen data/filter/431-pattern lift. The exporter reconstructs compact original-count cores from the saved auxiliary-run proofs; the independent reader rereads DIMACS/LRAT and source rows. The final command computes the three-rule effect on the explicit source subset only.

Producer programs include probe_critical_cycles.py, compact_history_lift.py, direction_history_lift.py, advance_direction_patterns.py, short_direction_closure.py and evaluate_short_closure.py. They preserve the reviewed63/431 snapshots separately from exploratory pending patterns. Re-running experiments may overwrite their result files; preserve them first. UNKNOWN/STATE_LIMIT/DEPTH_LIMIT are not refutations.

RUP/CDCL runtime sources, BinaryCNF sources, the exact original wincert.py fixture, frozen graph records, potential and source summaries are included in the ZIP at their expected relative paths. NumPy/native SAT solvers are NOT required for the delivered verifier pipeline. Figures/PDF authoring additionally needs Pillow/ReportLab and the documented Windows fonts.

No private authorization token, installed toolchain, compiled cache or third-party paper PDF is included. The report and all code are local; nothing in this research round is pushed.

## Next precise target

The remaining all-exact-count480 cycle defeats clipped-six-only refinements. It requires additional low-count compatibility or a genuinely positive empty-square charge on surviving exact-count windows, together with complete coverage of EVERY remaining minimum-mean component. The three new count exclusions are a verified increment in that direction, not completion of the global proof. Before any new numerical upper bound, rerun/verify the complete graph potential, retain the actual boundary range, and discharge the full arbitrary-snake and formal-replay obligations.

Source references: the connected repository's milestones50,59,70 and72, and the exact frozen hashes in the manifests. Earlier literature notes and published191-edge construction checks remain separate completed work; this continuation does not reset them to an older254/255 baseline or introduce Ramsey as the main method.
