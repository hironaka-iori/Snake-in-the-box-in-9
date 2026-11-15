# Independent first-step review, round 221

The audit passed on its first execution. All fourteen saved branch certificates have valid exact upper bounds. Exactly three exclude a rooted 93-edge partner: $0\to16$, $78\to14$, and $78\to74$. The remaining eleven branches are unresolved by these certificates.

The reviewer created `scripts/audit_first.py` and `data/first-audit.json`. The receipt status is `PASS_EXACT_FIRST_STEP_COVERAGE_AND_UPPER_CERTIFICATES`. Existing reviews, native evidence, and papers were preserved. The producer `scripts/first_step.py` was read to determine its schema; it was neither imported nor executed. No optimizer, compiler, software tests, or new search were run.

## Exhaustive first-step coverage

The allowed neighbours were independently enumerated by flipping each of the eight coordinate bits and retaining vertices present in the frozen long model. They agree with all edges incident to the root, the literal `root_degree` row, the fourteen summary entries, and the fourteen branch filenames:

\[
N(0)=\{2,4,8,16,32,64,128\},
\qquad
N(78)=\{14,74,76,79,94,110,206\}.
\]

The corresponding root-degree equations are $\sum_{v\in N(t)}x_v=1$. Every actual rooted induced path of 93 edges has a first neighbour in this list. That neighbour is selected; any other selected neighbour of the root later in the path would create a chord. Consequently, the seven conditions $x_v=1$ cover every actual partner at each root. For each file, the audit reconstructed the appended equality from the literal variable index and confirmed that the complete branch consists of the previously audited long model followed by precisely this row.

The row counts are 3146 at root 0 and 3111 at root 78. Both models retain 574 variables with bounds $0\le z_j\le1$, and the objective is exactly the sum of vertex-selection variables. Model hashes match the frozen long-model audit. This stage uses that prior receipt for the necessity of inherited rows and does not repeat the long-row audit.

The coverage argument concerns actual Boolean paths. A fractional assignment can distribute the root's neighbour weight among several neighbours and satisfy no equality $x_v=1$. Thus these branch certificates do not constitute exhaustive coverage of arbitrary fractional assignments.

## Exact certificate reconstruction

Each sparse weight list was checked for strictly increasing, unique, in-range row indices and nonzero integer weights. Every omitted weight was explicitly reconstructed as zero. Inequality rows have nonnegative weights; equality rows may have signed weights, including the appended equality. Every stored residual coordinate was recomputed from the model, appended row, objective, scale, and completed weight vector.

For scale $D=10^6$, objective $c$, and row weights $w_i$, the certificate uses

\[
r=Dc-\sum_i w_i a_i,
\qquad
Dc\cdot z\le\sum_i w_i b_i+\sum_j\max(r_j,0).
\]

The second inequality follows from the row senses, allowed weight signs, and variable bounds. The audit checked all 574 residual coordinates in each of the fourteen branches, then independently summed the positive residuals and weighted right-hand sides. All exact numerators and reduced fractions agree with the saved files and summary. No assertion of exact optimality is required.

| Root | First vertex | Exact upper bound, terminating decimal | Status for 93 edges |
|---:|---:|---:|---|
| 0 | 2 | 94.488969 | Unresolved |
| 0 | 4 | 94.613095 | Unresolved |
| 0 | 8 | 94.558772 | Unresolved |
| 0 | 16 | 92.569610 | Excluded |
| 0 | 32 | 95.018845 | Unresolved |
| 0 | 64 | 95.680069 | Unresolved |
| 0 | 128 | 94.188343 | Unresolved |
| 78 | 14 | 93.517327 | Excluded |
| 78 | 74 | 93.927558 | Excluded |
| 78 | 76 | 94.463971 | Unresolved |
| 78 | 79 | 94.406607 | Unresolved |
| 78 | 94 | 94.229213 | Unresolved |
| 78 | 110 | 94.892792 | Unresolved |
| 78 | 206 | 94.951566 | Unresolved |

For the three exclusions, the exact scaled arithmetic is:

\[
\begin{aligned}
0\to16:&\quad 91556090+1013520=92569610<94000000,\\
78\to14:&\quad 93165254+352073=93517327<94000000,\\
78\to74:&\quad 93212566+714992=93927558<94000000.
\end{aligned}
\]

A 93-edge partner would select 94 vertices, contradicting these bounds. The eleven larger upper bounds neither establish an actual partner nor certify exact fractional feasibility. The floating primal arrays were checked only for the expected length and finite entries; they were not used in any exclusion proof.

## Provenance and limits

The saved execution records terminal exit code 0, no stop reason, and approximately 2.546 seconds. All pinned sources and base models match their recorded hashes. Both output-stream hashes match, every parsed output record equals its summary entry, and every summary file hash matches the corresponding branch file. The summary contains exactly the seven expected cases at each root, with no missing or duplicated branch.

This is a reduction from fourteen first-step cases to eleven unresolved cases for the specified parent and roots. It proves neither a complete exclusion of rooted 93-edge partners nor a new global bound or witness. The previously established fixed-parent one-crossing upper bound of 193 edges remains unchanged. Generic Lean proofs and this concrete numerical audit remain separate; no end-to-end Lean assembly was performed.

SHA-256 values below identify the frozen evidence, relative to `E:/Snake-in-a-box/milestones/221-square-parity`:

| Artifact | SHA-256 |
|---|---|
| `scripts/audit_first.py` | `2a15548a8d3f843310320aa99eeb28b0646153a59f5d62c62d9c456173ddc899` |
| `data/first-audit.json` | `84283463d10dc79cc5e375ac1968c562b3e38c47a1a29f5ced842c4ac52b8562` |
| `data/first-summary.json` | `fde80edbbc439321b297303ffabdab6ce330f3c017da6ef70ed0719b504ac2bb` |
| `data/first-execution.json` | `17945518296c6c7cfb5da424c606cdeeae7e981219e0aa38db2400b72e0997c5` |
| `data/long-audit.json` | `a4c93e83583eb9abcc80f56118cbf8fa82e8de52255b2851dc7bc56f463cec54` |
| `data/first-0/vertex-16.json` | `dd19b95ca394c0a6a74873fab5b1c51aaeb1eb588d8ba1e22b4b89065a31ec62` |
| `data/first-78/vertex-14.json` | `33b93efebe7ef38f3446a4f7d7d7cfe177126ebf1c1f89ba9461cfc5e81f1e2b` |
| `data/first-78/vertex-74.json` | `c919c578ca9903c0519833eb59ebce97457512f75db97ac827946fc8531258fa` |

The machine-readable receipt additionally records all fourteen branch hashes, all exact arithmetic components, both base-model hashes, and the producer/launcher hashes. No discrepancy was found.
