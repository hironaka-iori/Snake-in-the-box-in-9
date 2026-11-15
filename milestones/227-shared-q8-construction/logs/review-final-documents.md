# Round 227 bounded final document review

Conclusion: passed after the short explanation's starting-face qualification was corrected. No outstanding issue was found in the reviewed changes. This is the round-227 revision review; the next full historical manuscript review remains round 230.

## Final sources

| Document | SHA256 |
|---|---|
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex` | `ff3222d6f7755fc6b87fd59e3d1fd7c483c184badeecbe4da17533d2f3f10b7d` |
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex` | `7b34feb178e6819482112694a1baefec57517e05323d6d001e8a9540124d6bb4` |
| `E:/Snake-in-a-box/milestones/227-shared-q8-construction/MATHEMATICAL_NOTE.md` | `455da89a381a8db7765e98fd87aad007b7122c4c8fbb41b34bc9e6ea2470c031` |

Both editor originals are byte-identical to their corresponding `E:/Snake-in-a-box/paper/` mirrors. The three-author declarations and existing hyperref metadata are unchanged from the round-227 before snapshots. All earlier theorem/reference labels and bibliography entries are preserved. The main source adds `sec:lowerpair227`, `prop:fixedupper227` and bibliography entry `research227`; the short explanation adds the same bibliography entry.

## Exact review scope

Read the complete diffs of both current manuscripts against `data/snake9_research.tex.before.txt` and `data/snake9_frontier_explanation.tex.before.txt`. Read the entire short explanation, including its final corrected passage, covering current lines 1–579. In the 11,831-line main manuscript, read lines 1–105 and 8060–8355, including the abstract, complete new subsection, proposition/proof and verification section; the complete diff additionally supplied the historical-status edits near line 8041 and the new bibliography entry. Read all 55 lines of MATHEMATICAL_NOTE.md. The rest of the historical main text was outside this bounded review.

Read the four actual statements and proofs in `lean/TemplateFacts227.lean`, their accepted audit and compiler log, and the preserved failed-attempt record. Inspected `search-summary.json`, the complete parsed coverage table, both final native batch results and execution receipts, the saved reduction counts, and the conclusions of the separate model/enumeration reviews. No compiler, solver or software test was run, and no manuscript was edited by this reviewer. The parent reports successful built-in compilation of both corrected sources; this review does not independently repeat compilation or perform PDF visual inspection.

## Numerical and mathematical claims

The complete coverage table contains each ID 0 through 300 exactly once. Its statuses comprise 107 static exclusions, 148 direct native infeasibility results, four port-cover exclusions and 42 new reduced-pair exclusions. Thus the inherited count is 259 and the final total is 301. The new 42 contexts divide into seven shared-prefix contexts and 35 others. All coverage-file dependency hashes match their actual files.

The first reduction has 18 configurations, six literal task groups and five representatives after configuration 17 is contained in configuration 0. The second has 230 configurations, 79 exact groups and 52 representatives after containment. Both batch records are complete, and all 5 plus 52 individual results are INFEASIBLE on their first solve with empty cycle-cut lists. The execution receipts are accepted, exit with code zero and have no external stop reason; their result links and current input pins match. This supports the stated total of 57 native queries without interpreting the batch-completion label alone as exclusion.

The projection argument, lower edge-count formula, mandatory crossing allocations and domain-containment direction are correct within the stated construction. The two seven-member classes are literal redundancies: they have identical lower tasks and identical full-sequence templates when supplied the same lower paths. The manuscripts make no new cube-symmetry claim.

The conclusion consistently retains the fixed normalized seed, appended endpoint 24, two length-preserving replacement blocks of at most 44 edges, retained outside indices and four coordinate-8 crossings. Padding a smaller replacement by unchanged source positions supplies the stated containment implication. The exclusion does not extend to other seeds, endpoints, block counts or lengths. The 193-vertex target would have 192 edges; no such witness is claimed. The maintained global interval remains 191 to 233, and the independent rebuild of the contributor upper-bound assembly remains pending.

The direct DFS is correctly described as TIME_LIMIT after 5,157,314 first-prefix visits, with no completed first path and 14 pending prefixes. Its checkpoint preservation and atomic successor establish no DFS exhaustion. Separate completed native exclusions supersede that frontier. The note identifies width 45 or a changed construction family as possible future work and explicitly records the requested pause after publication; it does not promise an automatic continuation.

## Lean scope and receipts

The current accepted Lean source has SHA256 `e220c40a967fbed8242aca22be69d302b0384acd69895fbb8282b6ad47694b4e`. The audit is PASS, exit code zero, with four reports matching the actual compiler log:

1. `remaining_face_budgets` states the exact 35-row context list and literal endpoint-face/budget conditions, including the upper-list size below 45 in the budget-two case.
2. `first_literal_class` states equality of tasks 0, 2, 4, 6, 8, 10 and 12 to task 0.
3. `second_literal_class` states equality of tasks 1, 3, 5, 7, 9, 11 and 13 to task 1.
4. `task17_contained_in_task0` states equal endpoint pairs and lengths and containment of both literal domains; its proof identifies the deletion of vertex 212.

The first report uses no axioms; the other three report only `propext`. All audit dependency hashes and the compiler-log hash match. The prior attempt remains separately recorded as FAILED with MEMORY_LIMIT on source `70e7b558afc47590b70ce64ff98b8b4dc403a6be2a68591b0609d41ec2178175`. It is not counted as acceptance. The preparation receipt retains its historical pre-compilation status; current acceptance is supplied by the separate final audit.

The documents accurately limit these new checks to literal finite facts. They do not claim that Lean verified JSON extraction, upper-path enumeration, all prepared-domain necessities, the complete coverage assembly or any of the 57 solver contradictions. The earlier general path constructors and crossing/capacity implications remain separate dependencies. This review did not rebuild those historical proofs or independently rerun the native contradiction searches.

## Resolved wording issue

The initial short explanation said that any path with exactly two coordinate crossings has an upper–lower–upper decomposition. This requires the starting face to be upper. Final lines 459–461 now specify an induced path starting in the upper face and identify all three induced pieces. The main proposition and note already contained the upper-face hypothesis. The correction is present in the editor original and exact mirror; the final frontier hash above supersedes the initial reviewed hash `6f51b7a1e0f9f25c4e9e02ae707434e4efd3914a5279cd47e6e0b41fdc17f487`.

## Evidence pins

- `data/search-summary.json`: `7ba92ae16c661c862fb8552617db14ff075b02c8988410a650a6b8b987af0e6a`.
- `data/coverage44.json`: `f02bfee405ddc56db3923d246ea245c035f9fa19bb6132923524d46ff64e01a5`.
- `data/TemplateFacts227-audit.json`: `2ff3b5dbfd1024b8a1e09e3a0bc9bb027199900082d985facc90d8380cf5dea5`.
- Accepted compiler log: `1dccf0d7a879f727f3af5a56af928e931004f3dc9549f3306c86b38ee55955f5`.
- `data/reduced-pairs/result.json`: `80f4de68a0a1efb16da310edae8fbabf10195195fe80b721844cfe384926fcc8`.
- `data/remaining-pairs/result.json`: `0aabfce7de02ef08ec79a3d3ab9a8d3b6c5fac712a947150694158dfb19827af`.
