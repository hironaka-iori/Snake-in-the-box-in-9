# Round 240 full-source review, part 3

Status: complete, with two presentation updates recommended. No blocking mathematical error was identified in the assigned text. This is a written source review, not a new proof-certificate replay or a build.

## Immutable sources and complete reading coverage

- `data/snake9_research-before.tex`: every line 8801–13254 inclusive (4454 lines), including every printed table, witness list and bibliography entry. Whole-file SHA256: `d5f1bfd6d1c3be3de4afabf81d4bb5c81d070e147a45f1c9d499bb8355529f3a`.
- `data/snake9_frontier_explanation-before.tex`: every line 1–1084 inclusive. Whole-file SHA256: `689050097ee05b6ff50afd02780baf02b14be81ee566ce13f87c9b663d6cf900`.

The main-file reading chunks were 8801–9400, 9401–10000, 10001–10600, 10601–10900, 10901–11200, 11201–11500, 11501–11800, 11801–12100, 12101–12300, 12301–12550, 12551–12800, 12801–13050, and 13051–13254. Truncated reads were repeated; specifically 11936–11975 was reread to restore the omitted middle of the 11801–12100 output. The short-file chunks were 1–250, 251–500, 501–750, 751–1000, and 1001–1084. A final newline was not counted as an additional source line.

## Findings

1. **Presentation, minor; main lines 9694–9700.** The verification summary stops at the two-missing-count result and the round-230 review. The detailed sections already state the later results accurately. Extend this summary to describe the actual-cube three-count theorem, the written four-count deduction with 87 checked literal matrix implications, the conditional eight-count deduction, and the current round's completed review. Preserve the distinction between checked arithmetic and an assembled cube theorem. The parent has accepted this update.
2. **Display precision, minor; short lines 301 and 353–357.** Several six-decimal displays are called exact bounds. The underlying saved certificates are exact rational calculations, but these decimal displays should be introduced as approximations to those rational bounds. This does not change any integer exclusion: all displayed values are separated from the threshold 94 or 96.
3. **Round-240 maintenance.** The short file's title date (line 13), opening reconstruction summary (40–44), minimum-support summary (916–920), and remaining-question/pause statement (935–944) describe the immutable round-239 state correctly. Update them only to the scope actually obtained in round 240. In particular, numerical matrix coverage alone must not be described as a fully assembled actual-cube Lean theorem.

## Mathematical deductions reviewed

The reconstruction proof was checked at the level of the written mathematics. The inverse coefficients satisfy the five radial cancellation identities, with the origin coefficient 315. The two- and three-missing-count divisibility cases are consistent. The four-point distance-eight graph is triangle-free and has the stated seven graph types; the direct cases and the seven-triple/five-block residual classifications are consistent with the printed coefficient calculations. The mixed-parity reduction uses the previous three-count result. In the conditional eight-count argument, every off-diagonal coefficient is even and has absolute value at most 16; parity eliminates the ternary right side, and the maximal-coordinate bound is strictly dominant for at most eight entries. Empty selection versus a singleton gives the asserted nine-count ambiguity for arbitrary binary selections. These statements impose necessary consistency conditions and do not produce a new snake or an optimality theorem.

The majority-contraction criterion, partial deficit inequality `2I+L <= 2r+2`, ordered-cut inequality, and overlap deduction 94+92=186 have their necessary hypotheses. The 623 literal cut inequalities, native complete enumerations and unfinished path assembly are distinguished. The six old omissions and seven new additions are a conclusion relative to the specified seed family and its cube-isometric copies.

The historical appendices retain their own hypotheses. Potential telescoping, boundary losses and the displayed deductions for 236, 238, 245, 247, 248, 251, 254 and 255 are consistent. The adjacent-count geometric arguments were read throughout; the three-twos section explicitly identifies its unprinted branches as an outline of a separately checked finite classification. Exact threshold clauses give the claimed Boolean recurrence, including k=0. Local forests, finite automaton cycles and fractional assignments are consistently separated from full connected snakes. The current charge target 230 and separate conditional proof target 231 remain hypotheses.

The construction appendices preserve their restrictions: fixed regions, exact lengths, selected parent classes, finite isometry censuses and unresolved resource-limited runs. The joining, contraction, endpoint parity, component-counting and cell-counting deductions are coherent. The warning that a restricted exact-length exclusion does not exclude larger lengths is correct. No restricted infeasibility is used to assert the global optimum.

The full short explanation agrees with the current detailed scope: interval 191–231 with a pending fresh independent contributor rebuild; maximum seed overlap 186 under the finite covers; full actual-cube Lean recovery through three missing counts; written recovery through four and conditional eight; no improved construction. Its sequential sections retain historical states with explicit later transitions.

## Local provenance inspected

- Round 237 completion record: actual-cube inverse and two-count recovery checked; 623 numerical cuts checked; finite enumeration and the full cut-to-path Lean assembly remain separate. SHA256 `d0ba4e73dc6fabd3a473e95a941fb8129b37361f69ce786c6b7d0bee10c49cd9`.
- Round 238 completion record: three missing counts, 509 observations; 132 recorded modules; the unbounded integer proof is written while the Lean arithmetic uses automatic bounds of nine. SHA256 `653b2a4db34b7587fa229ddbaed206477794cd0dba1f796e85128a6053e78c9b`.
- Round 239 completion record: actual-cube Lean recovery remains three, written recovery four, four/eight cube assemblies false, 87 metric classes and 7047 right-side combinations. SHA256 `56c913815902386f6dd756c503486216090b794b3424603006e71919832eeed0`.
- Round 239 matrix replay receipt: PASS, 87 modules and 87 reports. SHA256 `9254109f96ab2fb80784380989160fed4c7b1d0da9bb72f7f10b02c2ad0f4388`.
- Round 239 dominance replay receipt: PASS, three modules and five reports. SHA256 `3eefc24feb2c52fa7d5d329133b668e973369b2339074f0ddf1910eb8ce891cc`.

Only relevant recorded fields were inspected in the larger provenance JSON files; their complete dependency trees were not rebuilt.

## Citation and source structure

A read-only scan of each complete immutable source found 391 main labels and 430 references, with no duplicate labels or unresolved reference keys. The main file contains 138 bibliography entries; the short explanation contains 23. Both have no duplicate bibliography keys and no missing citation keys. This confirms source-level key consistency only. External links and historical source retrieval were not rechecked in this review; many research-record links intentionally use the mutable main branch, and their archived local files remain the specific provenance.

## Limits

No manuscript was edited by this reviewer. No Lean/compiler command, solver, test suite, search job or numerical certificate replay was run. Printed sequences and large numerical tables were read but not regenerated. This review does not independently re-establish the contributor's whole upper-bound dependency chain, establish novelty, verify remote links, or inspect PDF layout. Root owns the manuscript updates, final compilation, newly developed round-240 results and publication.
