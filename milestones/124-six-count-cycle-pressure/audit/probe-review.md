# Audit of the six-count probes

The complete representative table now has **19 native-negative classes and two
unresolved classes**, $0120310$ and $0120324$. The initial table had 16 native
negatives and five unresolved classes. No selected path candidate was saved.
These outcomes support further proof work; they do not establish a universal
six-count lower bound.

The audit covers all 28 saved milestone-124 probe records and the explicitly
pinned milestone-123 cap-25 probe for $0123042$. It reconstructs each formula,
checks counter multiplicities and saved cycle cuts, and verifies the source and
case hashes. No solver, compiler or contradiction replay was invoked.

## Formula reconstruction

For each seven-transition window, the six internal centres each contribute 21
opposite-corner literals after excluding their two incident path coordinates.
Every counter preserves all **126 occurrences**. Across these probes there are
100 through 106 distinct vertices, and some vertices occur three times. A
separate sequential-counter construction reproduces the counter clauses and
variable allocation exactly. Deduplicating literals would change the sum.

The ordinary and tagged base encoders agree exactly as clause lists.
All radius-nine probes cover all 512 cube vertices. The three radius-three/four
controls use their recorded local regions; all three remain UNKNOWN. None is
reported as a counterexample or an exclusion.

The audit checks **120 saved cut records, representing 81 distinct vertex sets**.
Every cut has distinct vertices in its encoded region and minimum internal
degree at least two under direct Hamming-distance-one adjacency. A finite graph
with that minimum degree contains a cycle, so such a selected subgraph cannot
occur inside an induced path. This verifies each cut as a necessary restriction
on a snake.

Recorded clause counts are taken before newly discovered cuts are sent directly
to the solver. For example:

- $0120314$: 101,898 recorded clauses and 101,908 final reconstructed clauses.
- $0120324$, resumed: 101,906 recorded and final clauses; all eight cuts were
  inherited and no new cut was added.
- $0123014$, resumed: 101,926 recorded and final clauses; all 28 cuts were inherited.
- $0123104$, resumed: 101,898 recorded clauses and 101,917 final clauses after
  adding 19 cuts.
- Prior $0123042$, cap 25: 102,162 recorded clauses and 102,168 final clauses,
  including thirteen inherited and six new cuts.

The audit records hashes for both reconstructed starting and final formulas.
A later certificate must use its stated formula and correctly account for cuts.
This audit does not inspect or replay the separate certificate jobs.

## Completed resumes and representative coverage

All five requested resume files exist. A fresh process-command inspection found
no matching `probe_resume.py` driver for `data/universal-resume.json` before the
evidence was frozen. Each resume preserves its source directions, six bounds,
count positions, cap, radius, source hash, and initial cut list exactly.

The resumes for $0120340$, $0123014$ and $0123104$ returned native contradictions
in 13.625, 13.313 and 35.250 seconds. The resumes for $0120310$ and $0120324$
remained UNKNOWN after 45.094 and 45.046 seconds. These are verified execution
records, not independently repeated timings or outcomes.

The following table selects the strongest available negative probe for each of
the 21 reversal classes, or the latest unresolved attempt. Every selected probe
uses the full cube. The proposed floor is one more than the forbidden cap; it
remains a candidate until its proof obligations are discharged.

| Representative | Selected probe outcome | Proposed floor | Saved cuts | Solver seconds |
|---|---|---:|---:|---:|
| $0120310$ | UNKNOWN | Unresolved | 0 | 45.094 |
| $0120314$ | Native contradiction | 25 | 10 | 2.438 |
| $0120324$ | UNKNOWN | Unresolved | 8 | 45.046 |
| $0120340$ | Native contradiction | 25 | 0 | 13.625 |
| $0120341$ | Native contradiction | 25 | 0 | 1.359 |
| $0120342$ | Native contradiction | 25 | 0 | 7.672 |
| $0120345$ | Native contradiction | 25 | 0 | 2.656 |
| $0123014$ | Native contradiction | 25 | 28 | 13.313 |
| $0123024$ | Native contradiction | 25 | 0 | 23.531 |
| $0123041$ | Native contradiction | 25 | 0 | 0.188 |
| $0123042$ | Native contradiction | 26 | 19 | 34.313 |
| $0123045$ | Native contradiction | 25 | 0 | 0.687 |
| $0123104$ | Native contradiction | 25 | 19 | 35.250 |
| $0123140$ | Native contradiction | 25 | 0 | 1.391 |
| $0123145$ | Native contradiction | 25 | 0 | 1.125 |
| $0123401$ | Native contradiction | 25 | 0 | 0.171 |
| $0123405$ | Native contradiction | 25 | 0 | 0.187 |
| $0123410$ | Native contradiction | 25 | 0 | 1.484 |
| $0123415$ | Native contradiction | 25 | 0 | 0.141 |
| $0123450$ | Native contradiction | 25 | 0 | 0.703 |
| $0123456$ | Native contradiction | 25 | 0 | 0.640 |

The $0123042$ row uses the explicitly pinned prior milestone-123 cap-25 result.
Its candidate floor 26 is stronger than the floor 25 sought in the universal
screen. The table retains every earlier UNKNOWN record in the evidence JSON;
a later negative outcome does not rewrite the history of an earlier attempt.

## Selected models and remaining obligations

Every saved `selected` field is null. A non-null census describes the last
cyclic model discarded by the search. Its counts satisfy the recorded cap and
its cycles match the last added cuts. The complete discarded selected sets were
not saved, so their count and share values cannot be independently recomputed.
They are not path witnesses or counterexamples.

`data/coverage-audit.json` supplies the independently enumerated 34 canonical
words and 21 reversal classes. The present table covers all 21 classes, but two
of their local questions remain unresolved. Even if all 21 searches eventually
return negative, a universal theorem still needs checked contradiction
certificates, count-sum semantics preserving repeated literals, transfer to
actual snakes, and the reversal argument connecting representatives to all
canonical cases. A resulting length bound also needs its separate counting
argument. No new upper bound is proved by this probe audit.

## Evidence

- `data/probe-audit.json`: SHA256 `16a3987431c7411656510555dbf8244dbd4382944a16b0acdabf942d73c69829`.
- `scripts/audit_probes.py`: SHA256 `3275c4a71d5993753d86288154a0fa8cf19fa1851608a358f47136dbc61bad89`.

The script prints a summary by default. An output argument creates a new evidence
file exclusively. It requires all five resume records and checks that their
matching driver is absent. It does not modify prior records or invoke a solver,
compiler, graph computation or certificate replay.
