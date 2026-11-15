# Independent long-model review, round 221

The frozen baseline audit passed on its first execution. `scripts/audit_long.py` independently reconstructs every newly added row, verifies the preserved square-model prefixes, and recomputes both exact dual-residual upper certificates. Its output is `data/long-audit.json`, with status `PASS_EXACT_LONG_CYCLE_ROWS_AND_UPPER_CERTIFICATES`.

No producer module was imported. No native data was modified, and no optimizer, compiler, software test, search, or basis reconstruction was run. This audit used saved records and integer/rational arithmetic. The long-primal and complete-family certificates are assigned to a separate reviewer and are excluded from this frozen receipt.

## Row reconstruction and preservation

| Fixed root | Preserved square-model rows | Added cycle-parity rows | Added forest rows | Final rows |
|---|---:|---:|---:|---:|
| 0 | 3118 | 27 | 0 | 3145 |
| 78 | 3101 | 8 | 1 | 3110 |

Both models retain the same 574 variables, their bounds, objective, 158 allowed vertices, and 337 edges. The audit independently reconstructed all cube-adjacent pairs of allowed vertices and confirmed that these are exactly the saved edges. Every original row, square witness, and inherited forest witness is preserved. The base model hashes agree with the earlier square audit. That audit and its pinned sources and input records were also checked for unchanged hashes; the earlier square-row computation was not rerun.

For each new parity witness, the audit verified a simple closed cycle in the allowed graph, an odd set of edge indices, and a distinct signed edge pattern. It expanded

\[
\sum_{uv\in F}(x_u+x_v-2y_{uv})
-\sum_{uv\in E(C)\setminus F}(x_u+x_v-2y_{uv})
\le |F|-1
\]

into the model's variable indices and compared every coefficient, right-hand side, sense, name, and row position. Together the witnesses cover the complete added row suffix, with no unaccounted row. The root-0 cycle lengths are eight of length 6, nine of length 8, seven of length 10, two of length 12, and one of length 14. The root-78 lengths are four of length 6, two of length 8, one of length 10, and one of length 12.

The sole additional forest witness is at root 78, with $U=\{8,9,10,11\}$ and marked vertex $9$. Its row is

\[
y_{8,9}+y_{8,10}+y_{9,11}+y_{10,11}
-x_8-x_{10}-x_{11}\le0.
\]

This is precisely $Y(U)\le X(U)-x_9$. The audit reconstructed it from the allowed edges and subset membership. The parent-provided claim that the generic `CutParity221` proof has passed remains separate from these concrete row checks; this reviewer did not compile or audit that generic proof in this task.

## Exact upper certificates

Let $D$ be the positive integer certificate scale, $c$ the objective vector, and $w_i$ the saved weight on row $a_i z\le b_i$ or $a_i z=b_i$. The audit verifies that every inequality weight is nonnegative; equality weights may have either sign. It recomputes

\[
r=Dc-\sum_i w_i a_i.
\]

Since every variable satisfies $0\le z_j\le1$,

\[
Dc\cdot z\le\sum_i w_i b_i+\sum_j\max(r_j,0).
\]

Every residual coordinate, positive part, weighted right-hand-side sum, numerator, denominator, and model hash matches the saved certificate. This argument uses exact integers and does not assume that the numerical optimizer found an exact optimum.

| Fixed root | Scale $D$ | Weighted right-hand side | Positive residual sum | Exact upper bound | Gap below 96 |
|---|---:|---:|---:|---:|---:|
| 0 | 1000000 | 94416979 | 1538218 | $95955197/1000000$ | $44803/1000000$ |
| 78 | 1000000 | 95504780 | 259199 | $95763979/1000000$ | $236021/1000000$ |

There are 431 nonzero row weights at root 0 and 453 at root 78. All 574 residual coordinates were checked in each case. The native result, summary, and exact certificate agree on the bounds $95.955197$ and $95.763979$. The saved native execution has exit code 0, no stop reason, and a duration of approximately 1.828 seconds; its pinned inputs and output-stream hashes match the files. Its floating separation stopping condition is not used to infer complete-family feasibility.

## Consequence and limits

An actual 95-edge rooted partner would select 96 vertices. Both upper certificates are strictly below 96, so such a partner is impossible in the stated fixed-parent models. More generally, an actual odd-edge partner has an even number of vertices and can therefore have at most 94 vertices, hence at most 93 edges.

Every admissible rooted partner with at least 95 edges has an admissible induced 95-edge prefix at the same root. Restricting to this prefix preserves avoidance of the fixed parent outside the joining vertex. Thus arbitrary partners at roots 0 and 78 have at most 94 edges, including even-length partners. A one-crossing join with the saved 98-edge parent consequently has at most

\[
98+94+1=193
\]

edges. This is a bound for that parent and arrangement. It supplies no global upper bound, new path, or exclusion of the 93-edge partner target. The maintained global interval remains $191\le a(9)\le233$ under the previously stated contributor-theorem rebuild qualification.

This receipt does not establish feasibility or infeasibility at total weight 94. It does not verify long-primal rational coordinates, all-subset flows, all occupancy potentials, or all cycle-parity potentials. It does not infer closure from the absence of newly detected floating violations. Any later complete-family claim must cite the separately audited terminal artifacts. No end-to-end Lean composition of the concrete numerical arrays is claimed.

## Frozen evidence

SHA-256 values are relative to `E:/Snake-in-a-box/milestones/221-square-parity`.

| Artifact | SHA-256 |
|---|---|
| `scripts/audit_long.py` | `3d2940885363da3f355433983f50d0038ab137287ea9a7ae31e6aeccc9f6099d` |
| `data/long-audit.json` | `a4c93e83583eb9abcc80f56118cbf8fa82e8de52255b2851dc7bc56f463cec54` |
| `data/square-audit.json` | `cc4c44f77167f7daa681d03de7ab28c2714f2c60307945511ff078353e534993` |
| `data/long-0/model.json` | `a4f0aa53fe7a8c06969643cd7a5b09c50459d6d5013e6568708b42a8ad76ce67` |
| `data/long-78/model.json` | `d0151302ca6cc914f5331befb72dcd00f22e9c0b06c46cc25da8efa8e8896dd3` |
| `data/long-0/upper-certificate.json` | `0e55545c878e897ee82b8a561c31b800b86536a16dc9b804793fcb359621283d` |
| `data/long-78/upper-certificate.json` | `d9bbc14f9c28dd189f693acae73af219a2ea100d2085309724c2bf638ff68987` |
| `data/long-execution.json` | `e98cc97d949d945e2a9dbac44a6448ed841e1dc0a76c33ae2ef3230c69eb1ef8` |
| `data/long-summary.json` | `07ceb22b677a71d3acc7c977c7cb976be30f178a50a1c761d655b0d32ffccdeb` |

The full machine-readable receipt additionally pins both native results, both square base models, and the long-model producer and launcher. The audit is frozen at this baseline; later certificates require a separate receipt.
