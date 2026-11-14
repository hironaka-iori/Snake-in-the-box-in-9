# Joint support for three consecutive groups

The frozen case22 snapshot contains stricter joint pair information, but this analysis finds no additional domain-value deletion. A unary-only implementation is not justified by these five regions. Retaining the new pair restrictions could affect later branches; its search benefit and cost remain unmeasured.

## Scope and input pins

The source is the immutable round215 state after 740 committed jobs, with five frontier regions: 20, 712, 711, 710 and 738. No changing state, compiler, software test, solver or branching search was used. The deterministic analysis completed in approximately one second.

SHA-256:

- `215-word-partner-capacity/data/case-22/state.json`: `1e53d7824e4350092104072ba5c1506236f8af19969f09346ab3c3f517e7eacb`
- Same directory, `model.json`: `1a4d81c600d104347a501cfc9bf82db91a3aa04a6ebfd3ea20fcb1ca283aa95b`
- Same directory, `support-constraints.json`: `0362c97affd2b4b19405f2a05747327a703b55459b6f1cb3d7bc455c72bce040`
- `216-joint-word-support/scripts/analyze_joint_support.py`: `18a953d0c887a1a368e3c755ac5ff0031b686d5a51efcfc10ce5ccdb5abf7647`
- `216-joint-word-support/data/joint-support-analysis.json`: `99c8d224fe2328f5bf0261fe6ad541992cfe882ba542caa5fcff9a2bf7e5d929`

The baseline repeatedly applies every original binary relation and Hall filtering for the four chosen/outside families. It omits partner-capacity/support rules, lexicographic symmetry rules and higher-order nogoods. All five regions reach a baseline fixed point. This is a saved-domain comparison, not a full reproduction or certification of the native propagator.

## Necessary relations and redundant checks

For every consecutive group pair, every pair allowed by the saved relation has Hamming distance one. Thus values at groups \(g\) and \(g+2\) necessarily have Hamming distance zero or two. This distance condition is intersected with the existing outer relation; an absent relation is initially unrestricted. No existing restriction is weakened.

For a triple, joint support requires one assignment satisfying its two consecutive relations and its outer relation simultaneously. Checking that a middle value independently has some left neighbour and some right neighbour adds nothing after binary propagation. When the outer relation is unrestricted, those neighbours already combine into a permitted triple. A distance-zero-or-two outer condition alone also holds automatically for that combination.

Additional information comes from particular outer restrictions or from retaining restrictions on specific value pairs that have no common third value in its current domain. This is a necessary condition for the same complete assignment, independently of how a prospective propagator discovers it.

## Frozen-state results

After baseline closure, installing all static distance-zero-or-two outer relations and repeating binary/Hall closure deletes zero domain values in every region. Exact projection of the supported triples then gives:

| Region | Unsupported pair occurrences after the static restriction | Immediate joint domain deletions | Deletions after installing all projected pair restrictions once and repeating binary/Hall closure |
|---|---:|---:|---:|
| 20 | 140 | 0 | 0 |
| 712 | 135 | 0 | 0 |
| 711 | 227 | 0 | 0 |
| 710 | 250 | 0 | 0 |
| 738 | 188 | 0 | 0 |

The total is 940 unsupported pair occurrences: 896 outer-pair occurrences and 44 consecutive-pair occurrences. Counts distinguish region and triple; a consecutive pair can occur in two triples, so these are not counts of distinct global forbidden pairs. No region is contradicted by the analyzed rules. The final comparison installs one complete triangle-projection pass; repeated triangle projections to a fixed point were not attempted.

For an explicit witness, take region20 and groups \((6,7,8)\). The outer pair of words \((5,6)\) is allowed by the original outer relation and has Hamming distance two. Its only six-bit common neighbours are 4 and 7, both absent from the middle domain. Nevertheless, word5 has middle-domain neighbours 21 and 37, while word6 has neighbours 22 and 38. Thus the outer pair has no joint support even though both words retain independent binary support. The saved middle domain is

\[
\{19,21,22,25,26,28,35,37,38,41,42,44,55,59,61,62\}.
\]

The JSON records current domain masks, supported-triple counts, unsupported-pair counts and example pairs for every affected triple. Its final domain arrays show that all individual words still survive after the projected pair restrictions and ordinary closure.

## Assessment

The witness establishes pair information that the existing unary domain state does not express. It does not establish an immediate domain-pruning advantage: all 940 pair occurrences disappear without removing an individual value. These exclusions are already logical consequences of the original relations and domain restrictions; the distinction is their explicit availability to a propagator.

A pair-retaining prototype could therefore be meaningfully different from an independent-neighbour check or a unary-only triangle pass. This snapshot alone does not justify expecting faster search, fewer branches, or a new exclusion. Omitted partner and lexicographic rules could also imply some of the same restrictions. No Lean bridge, native integration, complete traversal or new snake bound is claimed.
