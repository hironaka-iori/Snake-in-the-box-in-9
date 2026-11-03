# Audit of the two original orbit-cut searches

Both searches timed out. Neither returned a complete model or contradiction,
so neither establishes a six-count floor for $0120324$. The exact formulas,
cycle exclusions, multiplicities, terminal records and compressed partial trace
passed the independent saved-data audit.

| Attempt | Total cap | Variables | Clauses | Terminal status | Wall time |
| --- | ---: | ---: | ---: | --- | ---: |
| `0120324-total24-orbit` | 24 | 5,072 | 101,933 | `TIMEOUT` | 120.062 s |
| `0120324-total22-orbit` | 22 | 4,820 | 101,431 | `TIMEOUT` | 60.172 s |

The proposed conclusions would have been six-count floors 25 and 23,
respectively. Those conclusions remain unresolved. Both native processes
returned exit code 1 after termination; neither output contains a completed
SAT or UNSAT report. The partial proof traces were preserved without replaying
them as complete certificates.

The common window is $(0,1,3,7,6,14,10,26)$, with directions $0120324$ and six
internal count intervals $[0,21]$. The full-$Q_9$ encoding contains all 512 cube
vertices. The auditor rebuilt each formula and compared every clause with its
saved CNF, including the different total counters for caps 24 and 22.

Each internal centre contributes 21 corner occurrences. Across all six
centres, 79 corners occur once, 16 twice and five three times:

$$
79+2\cdot16+3\cdot5=126,
\qquad 79+16+5=100.
$$

All 126 occurrences are retained in each total counter. The sum is not
replaced by the number of distinct absent corners.

The eight previously saved cycle cuts produce 35 distinct cuts under all 24
permutations of unused coordinates 5 through 8. The auditor verified each
permutation on all 512 vertices and all cube edges, checked that it fixes the
specified window, and reconstructed the exact orbit and provenance records.
Every cut set induces a connected cycle: each vertex has exactly two neighbours
inside that set, and all its vertices lie in one component. An induced path
cannot contain all vertices of such a cycle. Thus each added negative clause
is necessary for an actual snake. This mathematical cut argument has not been
turned into a new Lean certificate by this audit.

The cap-24 partial trace contains 133,763,072 bytes. Its gzip archive contains
21,973,703 bytes. Streaming decompression reproduces the recorded original
length and SHA256 exactly. The original is retained locally and excluded from
the Git manifest according to `data/partial-proof-archive.json`. Its restoration
instruction is to decompress the archive to the recorded original path and
verify that hash. Lossless preservation supplies no contradiction.

The cap-22 partial trace contains 48,173,056 bytes. Its exact hash is pinned
along with both formulas, solver records and outputs, probe records, generators,
search script and inherited inputs. The audit records 24 pinned files.

This review covers only the two attempts named in the table. A later run using
the same formula with different proof-output storage is a separate execution;
changing that storage alone does not change the mathematical model. The saved
statuses and artifacts of these original attempts remain unchanged.

No solver or compiler was invoked by the auditor. The script can validate a
returned assignment against every clause and the actual induced components,
or replay a complete trimmed proof with at most two million hints. Neither
branch was applicable to these timeout outputs, so no model or LRAT-validation
success is claimed.

Evidence: `data/search-audit.json`, SHA256
`37c2994740ce36b741f98eae3319d4cc1a0ba2fc3d551c6abbeb26d594432fce`.
To reproduce this exact scope, run `scripts/audit_search.py` with the two attempt
names above. Its optional `--output` creates a new evidence file exclusively.
