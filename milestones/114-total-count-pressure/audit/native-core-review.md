# Independent native-core and theorem-scope review

The bounded audit passed the CNF reconstruction, cycle-cut validation, extracted-clause mapping and existing theorem receipt checks. It did not run a solver, compiler, native proof replay or graph calculation. No complete checked contradiction was found in the saved evidence.

## Exact formula and sum multiplicity

The canonical direction word $012310$ gives the vertices $(0,1,3,7,15,13,12)$. The audited formula uses the radius-four local encoding, all five individual count intervals $[0,21]$, and the sum of all five absent-corner counts at most 18.

The plain encoding and tagged encoding independently reconstructed identical initial clauses and variable numbering. The audit then rebuilt the sum counter and appended the eight saved cuts, obtaining byte-for-byte equality with `work/012310-total18/full.cnf`: **3,129 variables and 55,860 clauses**. These consist of 51,986 initial clauses, 3,866 sum-counter clauses and 8 additional cuts.

Each centre contributes 21 distinct corner literals. Their concatenation has **105 literal occurrences and 84 distinct literals**: 68 literals occur once, 11 occur twice and 5 occur three times. Sorting preserves this multiplicity. Deduplicating the list would change the intended sum and would be invalid. The rebuilt counter uses the sorted 105-occurrence list and cap 18.

All eight added cuts were independently checked from Q9 adjacency. Each vertex list is distinct, contained in the encoding ball, connected and of induced degree exactly2. Their lengths are $8,8,16,8,16,32,8,8$. Thus each is an induced cycle, whose full selection is impossible in an induced path. This check validates the intended cycle-cut constraints without relying on the probe's UNSAT status.

Full CNF SHA-256: `5cfbc8c1f60b60a7327c6cf0b959b2b2e1cce7302070afccae146472a3f3a3bf`.

## Extracted-core identity

The DRAT conversion wrote a 5,431-clause core despite failing to finish. Each extracted clause was matched as a sorted literal multiset to an original full-CNF clause, consuming distinct input IDs. The independently reconstructed ID list equals `extracted-core-solver.json` exactly. This preserves literal multiplicities, duplicate-clause occurrences and injective input mapping.

Exactly 4,535 extracted clauses have different literal order from their matched original clauses. There is no clause-content discrepancy. The first extractor's order-sensitive rejection was therefore an identity-check limitation. The revised extractor restores each original clause's literal order; its emitted core equals the selected original clauses in the recorded order. No mathematical weakening or new clause was introduced.

Restored core SHA-256: `94439f0d5392490fd18b735028efb0e62ea6293f7a847d46dd7f618f1efe9ff4`.

Because this is an exact input subset, a future checked contradiction for the restored core would also refute the full formula. The subset relation alone does not prove the core inconsistent, and successful extraction during an interrupted conversion does not replace a checked contradiction.

## Saved native attempts

| Attempt | Recorded outcome | Audit conclusion |
|---|---|---|
| Direct full-CNF LRAT | Timeout after 60.109 seconds | Partial 65,544,192-byte LRAT; no empty-clause addition |
| CaDiCaL153 proof logging | `UNSAT_DRAT_UNCHECKED`, 18.343 seconds | 854,353 text records; ends with one empty-clause record; DRAT correctness was not independently checked |
| DRAT conversion | `TIMEOUT_OR_FAILED`, 126.140 seconds | Partial 75,089,435-byte LRAT; no empty-clause addition |
| Restored-core LRAT | Timeout after 60.265 seconds | Partial 40,935,424-byte LRAT; no empty-clause addition |

The restored-core attempt had already terminated when inspected; no wait or additional run was needed. Each of the three partial LRAT files has one incomplete final record. Their structure was scanned, but no deduction replay was performed. They must remain unsuccessful proof attempts.

The successful checker build uses the pinned vendored source SHA-256 `d834b649f437e091597f5347f259b9f681087f89ca0844d0cee250a1a1a0c2ee`; the executable and control logs match the saved receipt. The valid control was accepted, while invalid and truncated controls were rejected. The audit independently checked the two-variable control formula truth tables and the empty truncated proof. Those controls support the recorded checker test; they do not certify the interrupted main conversion. The earlier compiler failure and unavailable-tool launch remain separate unsuccessful records.

## Checked theorem boundaries

`Comparison114` has three successful printed theorem audits. Its source and receipt establish the following arithmetic equivalences over natural numbers:

$$
1098960d+8p+R<(4200d+p)235
\iff 111960d+R<227p,
$$

$$
1098960d+8p+R<(4200d+p)234
\iff 116160d+R<226p.
$$

Its third lemma proves that $5p\le2424d$ implies

$$
(4200d+p)235\le1098960d+8p+R.
$$

These statements check the comparison arithmetic only. Interpreting $p/d$ as a cycle mean additionally uses $d>0$. In particular, the stated slope ceiling cannot exclude 235 through this comparison for any nonnegative range.

`TotalGeometry114.actual_total_sum` has one successful printed audit and retains `hlocal` explicitly. It transfers a local total-at-most 18 contradiction to the actual-snake lower bound 19 when the six directions canonicalize to 012310. Neither this helper nor `Comparison114` supplies the missing local contradiction. The source, object, log and source-snapshot hashes of both modules match their successful receipts. All four axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`, with the third arithmetic lemma using only `propext` and `Quot.sound`.

## Saved independent evidence

The reproduction script performs read-only reconstruction and structural inspection. By default it prints its result; `--output` requires a new file and refuses to overwrite saved evidence. Its JSON includes all core input IDs, corner lists, cycle vertices, inspected proof statistics and input hashes.

| Artifact, relative to 114 | SHA-256 |
|---|---|
| `scripts/audit_native_core.py` | `0f1cff33e292dd7102e717311e9e927f30c3d9a6f79a5cfd0175790992f3f369` |
| `data/native-core-audit.json` | `6fd66ccb4625052a66baac02fe4c4fa8a3f00485f84a663ff4b1021fbeb7e03c` |
| `data/extracted-core-solver.json` | `c3e5d53de633d2a0d3e2689e8d4027685e3cc053a35282a4efc9bf8c8cfbb91c` |
| `data/drat-conversion-bootstrap.json` | `3b904140ac3441a849db11b657685b401b5b5ed46ed2c723754959b82d3627f0` |
| `data/Comparison114-audit.json` | `5fd98f970998fa205ba40a8f7e0a98690f9d48e3cfa7c09a1aee864849871954` |
| `data/TotalGeometry114-audit.json` | `6975b1a3057a32d3bbd6327a184afc4b87f2630cc10c0ee3810933c163a25d6b` |

The remaining proof obligations are a complete checked contradiction and concrete clause semantics, followed by composition with the existing actual-snake transfer. No new local inequality or global upper bound is claimed by this audit.
