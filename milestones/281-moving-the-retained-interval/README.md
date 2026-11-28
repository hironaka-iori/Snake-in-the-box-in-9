# Round 281. Moving the retained interval along a 191-edge snake

A 192-edge snake can share **at most 99 consecutive edges** with archive path `191-0`, up to a translation, coordinate permutation and reversal. All 92 starting positions for a 100-edge interval were covered. Both new tails may use all nine coordinates. The number 99 is an upper bound on possible overlap. We have no 192-edge witness.

Moving the fixed interval matters. The result rules out either end, the centre and every off-centre placement of 100 consecutive edges. For each excluded interval the original 191-edge donor also shows that its maximum extension in the whole cube is exactly 191.

## Computation and transfer

We attempted 44 distinct intervals and proved exclusions for 18. The 26 other target searches ended open within their allowances. Six checked prefix shapes from Round 280 were available as additional certificates. For each search, the two independent end-growth programs first tried to produce a path or finish the search. Where they did not both give an exclusion, the occupancy calculation considered both endpoint parities and saved checkable proofs. Only completed exclusions entered the coverage calculation.

On transferring the intervals by literal cube isometries, the consecutive-overlap bounds improved for six archived 191-edge paths and twelve archived 190-edge paths. Their respective new bounds are 99 through 103 and 98 through 103. The archive-wide bounds across all 131 and 1,042 paths remain 153 and 159 respectively. The calculation combines these new certificates with the earlier per-path interval covers. [All placements and per-donor bounds](coverage.json)

For any starting index, an interval can extend at most to the vertex immediately before the first endpoint that completes a known forbidden subinterval. Taking the largest such edge count over starting indices gives the recorded overlap bound. Matching a transition sequence requires one consistent permutation of cube coordinates over the whole interval. Each match used in the calculation was also checked on the actual vertices. [Search decisions](windows.json) · [Coverage calculation](coverage.py) · [Proofs](proofs) · [Computational receipts](runs)
