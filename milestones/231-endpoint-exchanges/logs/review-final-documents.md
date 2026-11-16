# Round 231 final document review

**No outstanding blocking issue found after the two wording corrections below.** The final documents consistently separate the majority-class exclusion, its checked indexed-path components, its directly verified finite certificates, and its remaining native solver evidence. The maintained global interval remains 191 <= a(9) <= 233.

## Coverage and findings

Reviewed the main manuscript's abstract and initial result/status discussion, reading guide, complete `sec:colour231` proposition and proof, its computational and scope paragraphs, the new verification paragraph, and the new bibliography entry. Reviewed the short explanation's opening interval and evidence statement, complete “Reorder one colour class freely” section, “Remaining questions”, and bibliography entry. Read all of `MATHEMATICAL_NOTE.md`. This is a bounded review of the current additions and relevant context, not a fresh review of all 12,226 manuscript lines.

The contraction proposition is sound. It uses exactly two neighbours in the fixed class for each interior label. The proof correctly derives distinct labels from their unique unordered neighbour pairs, rules out same-parity adjacency and extra cross-parity chords, and treats the singleton case. Collapsing parallel labels preserves existence. The dummy-vertex circuit explanation is consistent with the previously audited models.

All counts agree with the independent construction audit: 131 seeds, 145 distinct 96-sets, 23,200 descriptions, 23,127 distinct 97-sets, 73 exact duplicates, 17,271 isolated cases, 5,807 excess-leaf cases, and 49 circuit queries. Exact set grouping is distinguished from classification under cube symmetries.

The documents consistently state that the covered candidate has 192 edges and a 97-vertex majority class containing one entire saved 96-vertex class. They allow a new path order, endpoints, crossing counts, and opposite class. They explicitly leave the fixed 96-vertex minority-class case open. The note's stronger statement about changing both classes is explicitly conditional on completing that next case.

The distinction between 45 elementary separator explanations and four remaining native exclusions is accurate. The finite extraction and solver contradictions are not presented as consequences of the checked constructor. The short explanation's 23,078 initial exclusions equal 17,271 + 5,807.

The four reported Lean results match the actual source interfaces and saved audit: interleaving construction; exact even/odd positional adjacency; extracted injectivity/disjointness; and same-parity-position nonadjacency. The manuscript and note preserve the separate obligations for cube-colour identification, literal graph generation, label selection, and finite exclusions. This review read the four compiler reports and verified the saved source, object, and log hashes against `data/ColourContraction231-audit.json`; it did not invoke Lean or independently rebuild the imported dependency closure.

The contributor paragraph correctly retains plain/H8, share, contextual-refutation, and floor premises for the inspected 231-target interface. Its arithmetic, 4763m <= 1104764, agrees with the contributor review. It does not replace the maintained 233 upper bound or describe an unconditional 231 assembly as completed. The independent-full-rebuild qualification on the existing completed contributor 233 theorem remains present in both manuscripts.

## Corrections identified and verified

1. The first reading-guide version extended the replacement-family scope sentence through `sec:colour231`, incorrectly suggesting that the new colour-class search fixed endpoints and replacement intervals. The final guide now ends that range at `sec:facevisits230` and gives the colour-class survey its own sentence with endpoints, order, crossings, and the opposite class free.
2. The first separator paragraph used an either/or explanation that could suggest endpoint deletion supplied some of the 11 additional certificates. The final main text states their actual common-component obstruction. The note explicitly records that all 11 use that obstruction and none uses endpoint deletion. The general endpoint-deletion inequality remains valid background.

Both repairs were reread in the frozen final sources. No further revision is requested by this review.

## Preserved settings and exact final files

The complete author commands and complete `hypersetup` command, including nested values, were compared against the round-231 pre-edit snapshots. They are unchanged. The main document retains `Iori Hironaka`, `Tommy Ma`, and `Steven Zhan` in that order, and its existing PDF author/settings block is preserved. The short document's author command is unchanged; it has no separate `hypersetup` command, as before.

Each authoritative original is byte-identical to its corresponding `E:/Snake-in-a-box/paper/` mirror.

| Final file | Bytes | SHA-256 |
|---|---:|---|
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex` | 765927 | `326a4fd1393da549cce9bd5981aaae3f5127e1ef86076372bb626e49205061d2` |
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex` | 36408 | `90fcdfaa6e784ce7f4ccf55eb6db1c3d87d70fb1adf8384e59b6491a664ddc6a` |
| `E:/Snake-in-a-box/milestones/231-endpoint-exchanges/MATHEMATICAL_NOTE.md` | 6181 | `46b278d06e9733b53c6e39e809ed1c6ee5de4ec3fec8bede73892c1b1a10d737` |

The main and short sources contain 12,226 and 686 lines, respectively. The saved Lean audit receipt has SHA-256 `564fea79de9a6df23f33951cf598a48e89105cdccdef24794590d2275dd4ac51`; its checked source has SHA-256 `d0c22bf9db3554edfae7f856e28e0de3e7718bafb2ea64e35266f4d290438aa3`.

No compiler, solver, software test, or manuscript edit was performed by this reviewer. LaTeX compilation and rendered-page inspection are separate from this source review. Only this report was written.
