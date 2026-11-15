# Round 228 bounded final document review

Conclusion: passed after one clarification in the short explanation. No outstanding issue was found in the reviewed revision. The last complete historical manuscript review was round 220; the next remains round 230.

## Final source hashes

| Source | SHA256 |
|---|---|
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex` | `43d61f680d480369d9fad76fe2b5b6642b5e720479ff3c94f98777a61c49b227` |
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex` | `1f13b26b016ea551642dfc1febb0bc03ded6dbffb3593d1ab5e4edeb4680f507` |
| `E:/Snake-in-a-box/milestones/228-wider-replacement-constructions/MATHEMATICAL_NOTE.md` | `badcdc7e3fc7d16d5588190c7b9c202d0eacb9ec394cd5259cf6d833fd002e7c` |

The corresponding two files under `E:/Snake-in-a-box/paper/` have exactly the same hashes as the editor originals. The main has 11,936 lines, the short explanation 588, and the note 95. The note is unchanged from its previously reviewed source.

## Reviewed scope and preservation

Read the complete revision script as source, without running it, and the complete diffs of both editor manuscripts against the round-228 `data/*.before.txt` snapshots. Read the entire short explanation, lines 1–588, including the final corrected passage. In the main, read the complete abstract and preamble, lines 1–100; the complete new `sec:width45` subsection beginning at line 8166, including `prop:twofixedupper228` and its proof; the changed verification paragraph at lines 8443–8445 with its diff context; and the new bibliography entry at lines 11929–11934. Read the mathematical note in full. The remaining historical main text was outside this bounded review.

Exact source comparisons confirm that both three-author declarations and the existing hypersetup block are preserved. The short explanation still has no separate hypersetup block. No previous label or bibliography key was removed. The main adds `sec:width45` and `prop:twofixedupper228`; both documents add `research228`.

The review used file reads, source comparisons and inspection of saved data and hashes. No project script, search worker, solver, compiler or software test was executed by this reviewer. The parent reports successful built-in recompilation of the corrected frontier followed by the unchanged main. Compilation and PDF visual inspection were not independently repeated here.

## Coverage and mathematical scope

The documents and note agree with `coverage45.json` and `search-summary.json`. The final table has 308 unique IDs, exactly 0 through 307, with the following disjoint counts:

| Recorded class | Contexts |
|---|---:|
| Static exclusions | 107 |
| Completed infeasibility rows retained from the interrupted initial batch | 34 |
| Boundary templates with no surviving branch | 69 |
| Contexts covered by reduced pair infeasibility | 85 |
| Direct pair infeasibility for unsupported allocations | 13 |
| Total | 308 |

The 154 reduced contexts comprise 69 plus 85. The coverage file contains 331 representative results, and every dependency hash in its pin map matches its current file. Its hash matches the summary's recorded coverage hash.

The reported allocation counts 16, 24, 78 and 36 sum to 154. The 2,141 original configurations produce 4,282 boundary branches; 3,527 fixed-boundary contradictions and 83 disconnections leave 672 configurations, which form 392 exact groups and 331 representatives. The first reduced batch excludes 321 tasks and leaves ten unknown; the longer batch excludes precisely those ten. The 13 direct contexts remain separate from the supported single-lower-segment reduction. These distinctions agree with the saved terminal evidence inspected during preparation of the note. Timeouts and the initial batch's incomplete rows are not used as exclusions.

The upper/lower decomposition and edge-count formula are correct under the stated prescribed joining endpoints and single nonempty lower segment. Upper-piece inducedness and separation, lower-piece inducedness and separation, and exact permitted projection contacts account for all pairs. Compatibility with retained outside vertices remains an explicit separate domain condition.

The width-45 boundary restriction explicitly depends on complete native width-44 exclusion. Selecting an old inner neighbour of an anchor forces its adjacent path position, permitting an unchanged-edge trim. If both blocks can be trimmed, the same complete candidate lies in the excluded width-44 family. The manuscripts do not treat this as an unconditional transfer of a smaller-width exclusion to larger domains.

The conclusion consistently concerns normalized bank 123, appended endpoint 24, retained anchors and outside positions, two length-preserving blocks of at most 45 edges and four coordinate-8 crossings. Padding supplies coverage of shorter blocks within this family. Neither a new 192-edge witness nor a global upper bound is claimed. The maintained interval remains 191 to 233, and the independent rebuild of the contributor's upper-bound assembly remains pending.

The note and main also retain the projection-mask limitation: the literal configurations have no unintended nonattachment projection contact, while general reuse must exempt only actual vertical joining ports. This limitation is not converted into a checked generic reconstruction claim.

## Lean evidence boundary

The current `AllocationFacts228.lean` hash matches the accepted receipt: `222619ea91ecedcc83b0a510eab2e8200233500e601680714c91b8909f7e1a8a`. The receipt is PASS with exit code zero and no stop reason. Its three reports match the actual saved compiler log:

- `row_count`: the literal table has 154 rows, with no axioms reported.
- `all_allocations`: the finite allocation predicates hold, with no axioms reported.
- `forced_allocation`: the listed allocation follows from the stated budget, parity and zero-count permissions; the reported axioms are `propext` and `Quot.sound`.

The papers accurately describe allocation arithmetic as kernel checked. Extraction of the flags, domain preservation, upper enumeration, complete coverage assembly and numerical contradictions retain their native status. The general path constructors remain earlier results with their stated premises. No complete Lean certificate for the width-45 exclusion is claimed. This bounded review did not rebuild those earlier proofs or replay any solver contradiction.

## Resolved clarification

The short explanation initially said that the reduction fixes the short upper-face pieces, then asserted that the listed conditions exclude every repetition and chord. Upper-piece inducedness needed to be explicit alongside the stated lower-piece inducedness and separation. Final line 458 now reads: “The reduction fixes the short induced upper-face pieces before searching for”. The correction is present in the editor original, exact mirror and revision generator. The main proposition already contained this hypothesis. The final frontier hash above supersedes the initial reviewed hash `9679829ed5ff9cf0b8723891840dfdcece89236a36bf666042e87f4e9b174271`.

## Supporting evidence hashes

- `data/coverage45.json`: `7587d552787e38de6ec877c6517b87b9a6d301bb5e500a64c42465d24a5d5eef`.
- `data/search-summary.json`: `72fed0d273bac390611afc28ec92f7f63730bcb083e3e9f094fe0c28fb88f950`.
- `data/AllocationFacts228-audit.json`: `c9d424a51282cafbd63cbc3f7358f7cd77fbd211ff805ff1eb0049b797762446`.
- Accepted compiler log: `f02c4499a8b3272d42edcd207d5cd7212c1390501ec749697d7008c9773b3c83`.
