# Which rule helps on the five round-215 parent regions?

This experiment concerns Case 22 of the 98-edge eight-cube parent search in [round 215](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/670d633bca81e3efff8d8ba5db0a1ba7079af137/milestones/215-word-partner-capacity/MATHEMATICAL_NOTE.md). The frozen state hash is `1e53d7824e4350092104072ba5c1506236f8af19969f09346ab3c3f517e7eacb`. All five region domains first pass the complete frozen word/partner propagation. The observer retains the input parser and propagation source verbatim and replaces the search driver with read-only reports on copies of the domains.

For three consecutive words a,b,c of a cube walk, either a=c or a and c differ in two coordinates. In the latter case there are just two possible values of b, one for each order of the flips. The outer pair and both consecutive pairs must also satisfy the saved binary relations. Remove an outer pair if neither possible middle word is allowed.

| Region | Outer pairs at distance two losing both possible middles | Single words removed by all consecutive triples together | Single words removed by arbitrary triple consistency | Single words contradicted by the original rules when fixed individually |
|---:|---:|---:|---:|---:|
| 20 | 139 | 0 | 0 | 13 |
| 712 | 130 | 0 | 0 | 8 |
| 711 | 206 | 0 | 1 | 15 |
| 710 | 246 | 0 | 2 | 9 |
| 738 | 175 | 0 | 0 | 12 |

The 896 two-bit pairs in column two count occurrences separately by region and chronological position. There are also many outer pairs at distance greater than two; chronological geometry rejects all of those. To test all consecutive triples simultaneously, take adjacent ordered pairs as states. Join (a,b) to (b,c) whenever the full triple is supported. Forward and backward reachability in this layered graph identifies exactly which single words occur on a chain satisfying every consecutive triple. Every word in the five reduced regions occurs on such a chain.

For arbitrary triples, intersect each permitted binary relation with what is possible through each intermediate variable, repeating until stable. This preserves a fitting assignment because its actual intermediate word witnesses support. Only three single-word candidates disappear: group 22, word 5 in region 711, and group 22, words 20 and 36 in region 710. As a separate check, fixing each word and applying the original rule set directly yields contradiction in every case.

**The next comparison should test single-word probing first.** Fix each surviving word of each nonsingleton variable, run the original propagation once to closure, and restore the input. An immediate contradiction excludes that value in that region. The 57 reported region/group/word candidates include all three arbitrary-triple deductions. Compare propagation cost and search nodes at an equal node budget on copies of the same five roots. These are root-level decisions, not complete region exclusions or measured end-to-end speedups.

[Reproducer](parent_triples.py), [binary-relation closure](pair_consistency.cpp), and [per-region results and candidate lists](parent-triples-215.json). With a C++20 build of `pair_consistency.cpp`, run `python parent_triples.py --cc /path/to/clang --pairs /path/to/pair-consistency.exe --probe-all` in the branch checkout.

### Matched run

The identical round-215 search engine was run on copies of all five input regions, once with their original domains and once with the 57 contradicted choices deleted at the root. Each run received the same 250,000-node budget. Region 738 exhausted in both versions, taking 61,626 and 58,021 nodes respectively. The other four hit the limit in both versions. Search-only elapsed totals were 121.531 and 121.703 seconds, respectively, before charging for the probes. This comparison gives no reason to install probing as the default. [Paired results](parent-probe-comparison.json) and [reproducer](probe_comparison.py).

The independent [round-216 main checkpoint](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/cfa2e8ed386259be99cd2564361591cd92a3b7bc/handoff/CURRENT_STATUS.md) has since integrated joint pair support and saved nine current regions. Continue those current regions using its 30-second job recommendation. The five round-215 roots above constitute the frozen comparison set.
