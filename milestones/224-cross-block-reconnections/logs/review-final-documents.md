# Round 224 bounded final document review

Review date: 15 November 2026. Final finding: no unresolved substantive issue in the reviewed final sources. Two local scope/wording corrections identified during review were applied by the parent agent and checked below. The earlier model reviews are preserved.

## Exact reading scope and limits

Read both complete diffs from `data/snake9_research.tex.before.txt` and `data/snake9_frontier_explanation.tex.before.txt` to the current manuscript mirrors. Read every frontier line, 1–501; main lines 1–99 and 7819–8075, including the complete abstract, new subsection `sec:twoblock224` at lines 7820–7895, and the complete verification section at lines 7897–8071. The main source contains 11535 lines. The final wording corrections retain these line counts and were reread in place.

Read all 64 lines of `MATHEMATICAL_NOTE.md`, including the appended width-34 crossing-allocation note and contributor observation. Read the complete search summary and inspected all 301 combined-result records as structured data, comparing each with its original or flow-run source. Read all 71 lines of `TwoBlocks224.lean` and all 101 lines of `TwoBlockEscape224.lean`, and inspected both accepted audit receipts with their saved source, compiler-log and object identities. The earlier failed escape-proof log was also inspected; the two incomplete simplifications and preserved failed source are distinct from the accepted proof.

This is the requested bounded revision review, not a new full-paper review. The complete review remains scheduled for round 230. No manuscript, model or proof source was edited by this reviewer. No solver, compiler or software tests were run. No PDF rendering or publication result is certified by this log. Hash comparisons and structured-data comparisons do not constitute a fresh Lean compilation or native solver replay.

## Final hashes and source preservation

Editor originals are under `D:/Codex/2026-10-13/new-chat/outputs/`. Their corresponding mirrors under `E:/Snake-in-a-box/paper/` are byte-identical.

| Document | Final SHA256 |
|---|---|
| `snake9_research.tex`, editor and mirror | `45aab4f0f416f4ca32fbd58f210aa21f1282bdb39d7ed1698f5aad433fc490e8` |
| `snake9_frontier_explanation.tex`, editor and mirror | `c378fefa4c13730c27d1001422e15dd8a21949bf96e7c02380c639966eeb1dca` |
| `MATHEMATICAL_NOTE.md` | `d98caa6a143830c97f46be65fa9f659b82c00ba794ca8a6783bd8b526191aae0` |

The main before-source hash is `47a5328d5120bb718b94034653f56fa704fba6796f43bd55a796630bb0132e10`; the frontier before-source hash is `1c60c266904a1d06c9a83eda374679cf1a2020e33dd3a29d18f3bbc1511ba2db`.

Both author declarations are unchanged and retain Iori Hironaka, Tommy Ma and Steven Zhan in order. The complete main `hypersetup` block is unchanged, including all three authors in the PDF metadata. The frontier has no `hypersetup` block in either version, and its hyperlink package configuration is unchanged.

All 353 earlier main labels remain in their previous order. Only `sec:twoblock224` and `prop:interaction224` are added, yielding 355 without duplicates. All 121 earlier main bibliography keys remain in order, with only `research224` added. The frontier retains its six earlier bibliography keys and adds the same reference; it has no labels in either version.

## Mathematical claims and evidence

1. The main interaction proposition correctly assumes an initial member of a blocked family, closure under each permitted length-preserving block replacement, two ordered disjoint open interiors, and an induced final path with an extension. Its contact conclusions are necessary conditions. The proof correctly constructs an induced intermediate path when one new interior has no equality or adjacency with the other old interior, then invokes closure twice. Shared anchors are allowed. Positional old interiors, including vertices that move between blocks, are the relevant sets. No claim of sufficiency, historical novelty or unconditional native bank closure is made.

2. The accepted Lean sources match that scope. `TwoBlocks224.firstIntermediate` constructs an actual indexed intermediate path under separation and agreement. `TwoBlockEscape224.escape_requires_cross_contacts` derives both contact conclusions with closure and blocked-extension hypotheses explicit. Each accepted receipt reports `PASS`, exit code zero, and only `propext`, `Classical.choice` and `Quot.sound`. Source, compiler-log and object hashes agree with the receipts. The accepted checks took approximately 3.203 and 1.062 seconds. The failed first escape-proof attempt contains two unsolved simplification goals and is preserved separately. The accepted axiom list contains no admitted-statement axiom. These generic results do not certify the native closure census or solver contradictions.

3. The numerical width-33 exclusion is correctly separated from the conditional interaction theorem. Its final contact-free run removes the contact inequality and every contact-based static reason. It covers all 224 maximal contexts, with 171 geometric exclusions and 53 native infeasibility results. The earlier independent model review established the maximal-window coverage of all shorter equal-length replacements in the stated family. The result remains restricted to the selected seed alignment, fixed anchors and outside positions, endpoint-24 extension, and exactly four bit-8 crossings. The contact-free result does not depend on the round-193 closure premise and has no complete Lean solver certificate.

4. The width-44 statements agree with the terminal records: 301 contexts comprise 107 static exclusions, 102 native infeasibility results and 92 unknown cases. The combined crossing equality is the correct restriction; individual counts are not fixed. The biconnected pass removes no vertex and rejects no case. The flow constraints preserve actual 44-edge paths via successive forward flows of 44 down to 1. All sixteen selected retries terminated with `UNKNOWN`; they are a subset of the existing 92 unknown IDs, so the combined unresolved count stays 92 rather than increasing by sixteen.

5. Every search-summary result/execution hash and count agrees with the saved records. The four runs have recorded totals of 4.453, 4.234, 77.828 and 98.438 seconds. All execution receipts report accepted native results and exit code zero. Every combined width-44 record equals the appropriate original or flow record, plus its `latest_query` field; all 301 IDs occur once. The 92 unresolved IDs match the summary exactly. Every recorded cycle-cut list is empty, and no run records a witness. `COMPLETE_COVERAGE` is explicitly distinguished from complete exclusion.

6. The appended width-34 warning is correct. The interval $[130,164]$ contains both original crossing edges 130 and 163. Its first maximal window contains no original crossing, leaving two crossings outside the pair. The two replacements therefore have two crossings available in total. Allocations $(0,2)$ and $(2,0)$ are consistent with the anchor-face parities; retaining the earlier $(0,1)$ restriction would be invalid. The note presents this as a continuation requirement, without claiming a completed width-34 search.

7. The maintained interval remains $191\le a(9)\le233$. The inherited one-crossing ceiling remains limited to the saved parent's cube-isometry class and carries no attainment claim. No new snake, global upper bound or optimality conclusion follows from the current native exclusions. The note's new contributor revision is reported as work in progress, without asserting a completed 231 bound or an independent rebuild. This reviewer did not independently fetch or rebuild that branch.

8. The local archive contains exactly 316 serialized models. Every archived member's bytes match the corresponding raw model, every manifest length/hash agrees, and the archive hash agrees with its manifest. This supports the local preservation statement; remote publication was outside this review.

## Issue disposition

The initial frontier paragraph omitted disjointness and said an entire new interior equals or is adjacent to a vertex. It now specifies two blocks with disjoint interiors and a vertex contained in each new interior. The main paragraph now explicitly begins its zero/one crossing deduction with “For a four-crossing result”. Both corrections match the intended hypotheses and leave all numerical results unchanged.

`data/scope-clarification.json` records the initial reviewed source hashes `cf9beb5da80b0c2fe54ccdbdd418776aec8cb26a024c8836449a5fd1ddd2353f` and `c9fed0a445926e9bfd2bae94bf47f9d3fcd5766800e1a16c398e7132bce8c0c8`, followed by the final hashes above. Both corrections were reread in the editor-identical mirrors. No further correction is required by this bounded review.

## Principal evidence hashes

| Artifact | SHA256 |
|---|---|
| `data/search-summary.json` | `ed4b86207fbc6ef339bd798a4b5c7172d9c0d6611d0fd367dfa30c7e41b27280` |
| `data/combined44.json` | `c4428697e1561f1c5f4e37928827322d59feed70b5df3bbf09dea0808dbbfb4d` |
| `data/TwoBlocks224-audit.json` | `1b7a23680905edeaff44326e5779c43fe350b3e33fc3dafcd47222bba01e5a32` |
| `data/TwoBlockEscape224-audit.json` | `e7820f93aa7c4d0419591cfb5755a4f556e74318e9399ce1165c4a3b8438b899` |
| `lean/TwoBlocks224.lean` | `39094d199c912be8beda24e58253e105ff0ccb518bb11b0aa916e45cdd2ce290` |
| `lean/TwoBlockEscape224.lean` | `86a141cb7addeff699fbf64c7e50284c91087b332ec28678e2553d332daa32c8` |
