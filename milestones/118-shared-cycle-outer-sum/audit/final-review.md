# Independent final review of milestone118

The native evidence is consistent: fourteen attempt records comprise ten positive local witnesses and four `UNKNOWN` results. The four unknown records represent two unresolved queries, each with an initial and a resumed attempt. No record reports an exclusion. The original five-witness audit remains unchanged.

## Probe coverage and independent checks

The review read every record under `data/probes/`, checked its hash against `data/all-probe-audit.json`, verified every recorded source and script hash, and checked exact positive-witness coverage against `data/all-witness-audit.json`. Direct reconstruction of cube adjacency, the radius-four ball, corner counts, connected components and interior endpoints agreed with the saved audits. All564 recorded cycle-cut occurrences were checked for distinct vertices, membership in the ball, connectedness and induced degree two. This count includes inherited cuts repeated in resumed records. No positive witness fully selects any recorded cut.

All ten positive records have direction word $012301$ and window $[0,1,3,7,15,14,12]$:

| Probe suffix | Exact five counts | Components | Interior endpoints |
| --- | --- | ---: | ---: |
| `completed-cycle` | $(4,2,10,2,3)$ | 7 | 2 |
| `conditional-cycle` | $(4,2,10,4,2)$ | 4 | 2 |
| `middle6-outer12` | $(4,4,9,2,2)$ | 5 | 2 |
| `middle6-total19` | $(4,3,6,2,4)$ | 3 | 2 |
| `outer12` | $(2,2,10,4,4)$ | 3 | 2 |
| `outer13` | $(5,3,10,2,3)$ | 13 | 2 |
| `total18` | $(3,2,5,4,4)$ | 3 | 2 |
| `total19` | $(4,4,5,3,3)$ | 4 | 1 |
| `total20` | $(4,3,5,4,4)$ | 16 | 2 |
| `total21` | $(6,4,4,3,4)$ | 5 | 2 |

Every selected component is a tree of maximum degree two, including possible isolated boundary vertices. All selected interior vertices have positive degree, and at most two have degree one. Counts are exact integers; the values $9$ and $10$ in this table must not be replaced by an interpretation as exact $6$.

The two critical witnesses have outer sums $11$ and $12$, with actual middle count $10$. They invalidate outer sum at least $13$, also under the condition middle count at least $6$, within the relaxed local model. The `total18` witness prevents a universal total lower bound $19$ from following from the same local conditions. The `middle6-total19` witness similarly prevents a conditional total lower bound $20$. The two smaller thresholds, unrestricted total at most $17$ and total at most $18$ with middle at least $6$, remain unresolved; the four `UNKNOWN` records supply no contradiction proof.

## Resumed attempts

`scripts/resume_probe.py` refuses to overwrite an existing output and requires the earlier result to be `UNKNOWN`. It checks equality of the direction word, all bounds, summed positions and cap, records the earlier file hash, and imports the old cuts before further solving. It preserves literal multiplicity when constructing the sum counter. Its final provenance check includes the old record and all pinned encoding sources.

Independent comparison confirms the exact old cut list is a prefix of the new list:55 cuts become58 for `middle6-total18`, and101 become111 for `total17`. The original files remain pinned and unchanged. The resumed records have fresh timings, call counts and last census; these are measurements of the new attempt, rather than cumulative measurements. Their mathematical constraints and earlier cuts are preserved. The resume-time `is_cycle_set` predicate is weaker than the final audit's induced-cycle test, but every actual imported and added cut passed the stronger independent test. No unsound cut was found in these records.

## Concrete Lean statements and status

The first combined source timed out after120.438 seconds, with exit code1 and an empty log. Its immutable source, checker and failure record remain preserved. The source snapshot hash is `3e2a4e45d761b1f32156e13cc4d0dcadfcb1806a27dc086828c194a137fb7d35`; the failure-record hash is `216c63684d0652457aec17f586d59a1cb0f6a79e7494fe595413b81ba3550ba1`. No theorem from that attempt is counted as checked.

The revised `lean/Witness118.lean` passed in30.735 seconds. It contains four concrete-data theorems and five arithmetic theorems. Four private constants hold the two path lists and their membership functions, shared between the separate count and path checks. `completed_counts` and `conditional_counts` establish the exact five-count tuples. `completed_path_components` and `conditional_path_components` establish distinct selected vertices below512, inclusion of the seven window vertices, and respectively seven and four path components. The per-vertex condition specifies the exact selected degree and restricts every selected neighbour to the predecessor or successor in its displayed path. Together with distinctness, this establishes induced paths and excludes edges between different listed paths.

The review independently parsed the successful source's literal path lists and checked equality with the original saved selected sets and exact adjacency within those sets. The corner arguments match the successive direction pairs $01,12,23,30,01$. The radius-four identity, selected-vertex membership in that421-vertex ball, and exactly two interior endpoints are checked in Python; they are no longer included in the successful Lean statements. This boundary must be preserved in subsequent descriptions.

The successful receipt reports `PASS_CONCRETE_LOCAL_FOREST_DATA`, exit code0 and no timeout. All151 dependency hashes, current source, source snapshot, checker, checker snapshot, object and log were independently verified. The four concrete-data reports use only `propext`; the five arithmetic reports use `propext` and `Quot.sound`. There are no occurrences of `sorry`, `admit` or `native_decide` in the successful source. No compiler was launched by this review.

There is no actual-snake hypothesis or conclusion and no claim that the disconnected forests extend to a complete snake. The source does not package these data as the imported general `Axioms` proposition or establish satisfiability of an entire auxiliary-variable CNF.

## Hypothetical cycle comparison

The small calculation in `scripts/cycle_limits.py` was reviewed and independently recomputed from the pinned milestone117 cycle record. It assumes, without proving, total at least18 for $012301$ and total at least19 when its middle count is at least6. The only affected saved windows have clipped counts $(4,2,6,2,3)$ or $(4,2,6,4,2)$, with deficits2 and1 respectively. Both contain symbol6, so these assumed inequalities do not delete their complete count buckets. Both placements are checked for possible deletion; only suffix placement1 contributes to the edge credit. Counting both placements as credits would double count.

Under $4a+c\le120$, the total-deficit coefficient satisfies $\min(a,c)\le24$. The old rules have zero deficits on these saved cycles, and simultaneous applicable deficits are combined by a maximum. The completed18-edge cycle has old weight8745 and suffix deficit sum2, giving the ceiling

$$\frac{8745+24\cdot2}{18}=\frac{977}{2}.$$

The conditional3-edge cycle has old weight1488 and suffix deficit sum1, giving

$$\frac{1488+24}{3}=504.$$

The zero-range comparisons are $2205736/9377>235$ and $22979/98>234$. Their positive scaled margins are2141 and2256. The arithmetic deductions in Lean agree with these values and extend the comparisons to nonnegative potential range. The link from saved graph cycles to these arithmetic constants is computational evidence, rather than a Lean graph theorem. These are upper limits on a possible improved minimum mean from this fixed family, not newly computed minimum means or potentials. No full graph computation was performed, and neither assumed inequality is accepted as a theorem.

## Evidence pins and limits

- `data/all-probe-audit.json`: `df7a888b72fa6b3255fb65f1b27e7867a50c807968a5ffde196794b69b7dd09e`.
- `data/all-witness-audit.json`: `05f343003d0b33d48b0a651205efa63167bc406307a5a0872708801760e3a214`.
- `scripts/resume_probe.py`: `3e9956567309c9436640477dbcd448fd721a45ba0b6c13706fe9d736826f2af9`.
- `lean/Witness118.lean`: `183f9b47707051dc8eecd7e7d64c0d630080369a2850cedcdd8d3397f752f568`.
- `scripts/check_witnesses.py`: `bede19681eae30a79b0d46a95573557230265be9942659469d35723f023ef25b`.
- `build-geometry/Witness118.olean`: `8457a0a30f346672c8143cddad9c374bce7fc3679ea36684c659d12746423fda`.
- `logs/Witness118-1793672309962312200.log`: `fbdfcd1df2b0a92926450617d103adb28af9a98f38324d342ea32cd8d8ff40f9`.
- `data/Witness118-audit.json`: `5ee02f8e2164a1ebfb2291e9f16aff6a3ff55e1764149f34610500d72a8defdf`.
- `data/cycle-limits.json`: `db466eb7ab4bdb4e038e9f8ff64edb74fed3a19b3b1c5c547d5635916a59d403`.
- `scripts/cycle_limits.py`: `bb69c17474909645a4e053e549ef493a228b7d7b04889bc456ed1d1cb80e9975`.

No substantive defect was found in the reviewed native evidence or proposition scope. Every positive selected graph is disconnected and uses relaxed boundary conditions. These local counterexamples do not refute a corresponding statement for complete snakes. No graph optimization, improved global bound, SAT refutation or extension theorem is established by this milestone's reviewed results. This review did not run solvers, Lean, or a full graph scan and wrote only this report. Final mathematical documentation was not yet present when the source and native evidence were inspected.
