# Round 178: floor14 needs exactly two units of loss in the retained comparison

The round is complete. The user requested about15–20 minutes of work followed by a pause. No new unconditional bound or longer construction is claimed. The maintained interval remains191–235 edges, with the archived contributor235 proof's complete independent rebuild pending.

## New finite-graph result

| Pending floors (012034,012301,012340,012345) | Scaled mean | Scaled range | Scale | Conditional inequality |
| --- | ---: | ---: | ---: | --- |
| 14,16,16,16 | 4448 | 5346 | 9 | 42248m +45L <=9928330 |
| 14,14,14,14 | 4448 | 5380 | 9 | 42248m +45L <=9928364 |

All4,661,572 edge inequalities pass exact integer scans for both final potentials. The inherited retained graph, completed floors, count restrictions, and count-conditioned012032 increment are unchanged. The second inequality excludes235 whenever L >=2, with exact margin6/42248. Thus uniform14 plus positive loss of at least two suffices for conditional234, improving the previous reused-potential threshold23. The fixed-other-floor16 threshold improves from17 to2.

## Why the loss threshold is optimal in this comparison

Both profiles have a9-edge cycle of weight4448. A9-edge walk of weight3854 forces scaled range5346 at that mean for the first profile. An8-edge walk of weight3356 forces scaled range5380 for the uniform profile. Separate scalar reconstruction reproduces every witness edge from original source rows and confirms retention and adjacency.

At L=1, minimizing over nonnegative rational means and ranges gives respectively235+5/42248 and235+39/42248. Both exceed235. The exhibited potentials attain these comparisons. Hence2 is the least sufficient nonnegative integer loss threshold with these weights, boundary24, zero occurrence credit and only a scalar loss lower bound. Additional geometry, endpoint restrictions, occurrence credit, a stronger boundary, or graph changes could alter this conclusion.

## Remaining geometric case

Under uniform14 and the retained graph premises, m >=235 forces m=235 and L in{0,1}. Existing geometry then forces domination. The L=0 case has zero remainder everywhere. The L=1 case has exactly one positive-remainder vertex. The elementary bound e <=choose(9-d,2), together with residue12e mod d=1, forces that vertex to have d=5 and e=3. The finite arithmetic classification passes Lean. Its geometric pair-counting hypothesis is stated explicitly; the new actual-snake wrapper checks the critical length, loss, domination and support conclusions under explicit window and potential premises. The degree/empty-count classification uses the stated elementary geometric bound.

A proposed next target exploits the fact that a window's rational share minus integer share is at most L. This follows by multiplying each corner remainder by the proportion of its selected neighbours included in the window, a factor in[0,1]. A rational-share lower bound16 would imply integer share15 in the remaining L <=1 case. That local rational bound has not been established. It may be more tractable than the original unrestricted share18 certificate.

## Evidence and execution

Five accepted Lean modules contain twelve theorem dependency reports: four comparison/critical-case statements, four optimality/obstruction statements, one finite corner classification, two actual-snake implications, and one exact integer feasibility witness. Only standard accepted axioms occur. Two larger arithmetic elaborations exceeded the256MiB compiler cap; their logs and exact source snapshots are preserved. Splitting the proof and supplying explicit positive linear combinations gave accepted proofs without raising that limit. An equality-parameter draft was not needed or checked.

The new producer reconstructs weights in bounded batches from disk-backed source columns and matches three archived weight hashes before optimizing. It preserves the768MiB free-memory reserve. Unlike the older1GiB-private producer, it has a512MiB private cap and a startup requirement equal to that cap plus the reserve. Measured peak private memory for the producer and guardian together was90,333,184 bytes. Existing Mathlib and core Lean limits were unchanged.

The initial uniform14 mean4447 potential passed but was suboptimal. A cycle-extraction attempt at mean4448 failed to find a negative cycle because that mean was feasible; the failed run is preserved and is not used as impossibility evidence. A subsequent complete computation at mean4448 passed with range5380. The common critical cycle then proved the mean optimal. Native source columns remain local and are excluded from publication; regenerate the original columns from the archived source-graph.npz if needed.

Still unresolved: the four local floors; inherited retained count premises, including hypothetical0123104 six-count floor25 under its specified first-count condition; reference exclusions; complete graph-to-snake proof; complete Lean finite-graph certificate. The1358 reference entries and791 context obligations retain their prior scope. The share18 replay remains33,111/145,215 deductions, without final contradiction.

The main manuscript and short explanation are updated in place. Authors and hyperlink settings are preserved. The next manuscript-wide review remains186. Do not begin round179 until the user resumes the paused goal.

The aggregate constraints admit m=235,L=1,G=22895,W=111595, with equality in the global budget and packing constraint and satisfaction of both potential inequalities. Lean checks this integer witness. It is no snake construction; it confirms that rounding the aggregate scalar constraints cannot finish the proof.
