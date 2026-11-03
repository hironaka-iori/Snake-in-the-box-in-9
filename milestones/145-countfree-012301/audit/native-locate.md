# Existing certificate for the count-free 012301 share-16 claim

The exact native input and archived evidence have been located and reconstructed. This audit did not replay a proof. The saved evidence is DRAT; no matching LRAT file was found in the inspected milestones 72 and 73 provenance or the milestone filename search. Case 7303 has no folder and remains recorded as `NATIVE_CERTIFICATE_ONLY`.

The authoritative record is `milestones/72-four-count-proof-closure/critical-current/data/pysat3-cap15-certificate.json`, selected by that directory's `data/portfolio.json`. The matching original files remain under `build/`, with compressed copies under `certificates/`. The historical native audit and archive receipt agree with the files currently present. Milestone 73's `scripts/bootstrap_case.py` selects this exact metadata for index 3/case 7303; it does not supply an existing case 7303 proof.

## Exact claim and assumptions

The direction sequence is `[0,1,2,3,0,1]`, giving window vertices `[0,1,3,7,15,14,12]`. All five count bounds are `[0,21]`. The share cap is 15, the resolution is 12, and the local radius is 4. The encoder permits at most two endpoints. It has no extra positive count bound, parity assumption, or endpoint-placement assumption.

There are sixteen additional eight-cycle exclusion clauses, appended before the cold proof-producing solve. These are material premises of the saved Boolean input. They are valid for an induced path because its induced subgraph cannot contain a cycle. This review independently checked that every listed vertex set lies in the encoded ball, has eight distinct vertices, is connected, and has degree two at every vertex. The generic four- and six-cycle exclusions already present in the base encoding also remain.

The normalized reverse of `012301` is again `012301`: reversing `[a,b,c,d,a,b]` gives `[b,a,d,c,b,a]`, and exchanging the names of the first two and last two coordinates restores the same pattern. Thus the representative is compatible with both orientations. This is a mathematical observation about the target interface; no checked actual-snake theorem or reversal wrapper for this certificate has been produced by this audit. Any future wrapper must quantify over four distinct directions below 9, require a complete six-transition window, and interpret the sum over its five internal centres.

## Independent checks completed

The checker reconstructed all 92,656 original clauses and their ordered literals using the current hash-pinned encoder. The header has 11,378 variables. It separately compared the 54,746-clause base with the untagged local encoding. The ball contains 421 vertices. Reconstructed meanings cover every variable exactly once. Each of the 71 totalizers and every share implication was reconstructed separately from the register meanings: 35 centre incidences, 28 square variables per incidence, 16 share-unit variables per incidence, 560 cap literals, and the cap unit at threshold 16.

The saved core has 12,977 clauses and 5,323 active variables. Each core clause has a unique matching original clause identity; the complete identity list is saved in `data/native-review.json`. The core is a submultiset of the original input, and its family counts match the historical metadata:

| Family | Core clauses |
|---|---:|
| Base local constraints |6017|
| Empty-square implications |787|
| Upward totalizer clauses |4680|
| Downward totalizer clauses |1055|
| Share implications |437|
| Share cap |1|

Six of the sixteen additional eight-cycle clauses occur in this core: original clause IDs 92641, 92642, 92643, 92645, 92648, 92652. The historical `old/cut` tag covers all cycle exclusions, including the ordinary four- and six-cycle clauses; its count 259 must not be reported as the number of additional eight-cycles.

All original and compressed files were hashed independently, and compressed content was streamed and compared against the original hashes and archive sizes. No original file was changed. The reconstruction completed in 2.469 seconds. No solver, converter, proof replay, Lean compiler, or graph computation was invoked.

## Preserved proof evidence

| File stem `pysat3-cap15` | Original bytes | Gzip bytes | Original SHA-256 |
|---|---:|---:|---|
| `.cnf` |1987669|318101|`653031c6d87edfd86d2f08a2ba47d28270b7571a26c70993dadd846729eaf307`|
| `.core.cnf` |257925|61806|`f4ee34e49f55473ac4cf55a5e38de77b3408473b253360d0bb4bbcca2697c1d7`|
| `.drat` |106351672|25849927|`34aac438fc02bf2fea262f0899c267c68dd0a11ef205676328ffd19a3c6f3789`|

The metadata SHA-256 is `1bb804fb72d10063e0b0741b33747fe29a95c4b3d8d18986d1263476eb99a03a`. The complete source and archive hash map is saved in the review receipt.

The historical verifier log contains `s VERIFIED`, reports 285,541 core lemmas from 554,437 proof lemmas, 31,017,505 resolution steps, zero RAT lemmas, and 24.485 seconds. Its bytes and the recorded checker executable hash agree with the old native audit. The raw DRAT ends with the empty clause. These observations verify provenance and the historical report; they do not constitute a fresh proof replay.

The 31,017,505 resolution steps exceed the current 20 million hint replay allowance as an indication of likely workload. They are not a measured LRAT hint count. There is no LRAT stream to count or replay under the present authorization. Conversion, proof trimming, and a revised replay budget require a separate bounded task. The existing proof is already available, so a new solver query is unnecessary merely to recover this certificate.

## Remaining obligations

1. Convert the preserved DRAT proof against the exact original CNF to an explicit proof stream, retaining the original clause identities, and measure its actual hints and size.
2. Independently check the complete retained stream before exporting it. If it exceeds the budget, preserve the original and use a separately recorded sound reduction or a new explicit budget.
3. Check the semantic clauses, all used cycle exclusions, and the contradiction in Lean; then assemble the actual-snake coordinate and orientation wrappers with standard axioms.

The status is `PASS_INPUT_CORE_AND_ARCHIVE_RECONSTRUCTION_NO_NEW_PROOF_REPLAY`. Neither a new local theorem nor a new global upper bound follows from this audit alone.
