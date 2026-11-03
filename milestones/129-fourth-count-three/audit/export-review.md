# Independent audit of the milestone 129 proof export

Result: **PASS_EXPORTED_BYTES_SEMANTICS_AND_PACKED_PROOF**. Completed on 3 November 2026 at 07:22:30 UTC. The successful audit took 11.687 seconds.

The audit independently reconstructed the input formula, checked its selected clauses and semantic labels, verified the variable renaming, compared all generated and ported sources, and replayed the complete packed proof. It launched neither a solver nor Lean. It does not establish that the exported Lean modules have completed compilation or that the actual-snake interpretation has been proved. The earlier transport and native-proof reviews remain unchanged.

## Formula, selected inputs and variable meanings

The auditor imports no encoding, generator, trimmer or proof-checking helper from the producer. Direct enumeration of the nine-dimensional cube reproduced all 112,225 expanded clauses, in the same order and with identical literal order, using 10,175 variable identifiers. The reconstruction includes the vertex and endpoint constraints, every sequential counter, the square and cube exclusions, and the saved cycle cuts. The six corner lists were independently enumerated and matched the saved lists. Each added cycle cut was checked to have distinct vertices and at least two selected neighbours at every vertex.

All 3,500 selected input identifiers, their clauses and their tags match the selected second core. The same selection is present in the exported Lean `raw` list, using the expected signed-literal encoding. The exported direction word is `0120324`, its vertex list is `[0,1,3,7,6,14,10,26]`, and its local bounds specify fourth count three with the other five counts unrestricted in the range zero to 21.

The renaming is a bijection on all 10,175 identifiers. The 1,695 variables occurring in the selected inputs or proof are mapped to the first 1,695 identifiers, in increasing original order. The remaining identifiers follow in increasing original order. Every selected clause and every literal in the renamed proof matches this map; proof clause identifiers and ordered hints are unchanged.

The semantic table has 2,415 entries: all 1,695 proof-active meanings, together with all primary and endpoint inputs. It contains every one of the 512 vertex meanings and every one of the 512 endpoint meanings. All inputs of every retained counter are present, including repeated occurrences. Every retained auxiliary-register meaning belongs to a retained counter.

| Retained counter | Interpretation | Occurrences | Distinct variables | Selected clauses |
|---|---|---:|---:|---:|
| 0 | At most two endpoints | 512 | 512 | 930 |
| 4 | At most 18 selected corners at the fourth centre, equivalent to fourth count at least three | 21 | 21 | 74 |
| 11 | At most three absent corners at the fourth centre | 21 | 21 | 113 |
| 12 | At most eleven absent-corner occurrences across centres three, five and six | 63 | 57 | 980 |

The other nine counter entries are explicitly dummy entries and have no selected counter clauses or retained register meanings. In particular, the selected proof does not use the pair counter or the additional first- and second-count lower counters. The arithmetic used to justify counter 12 for an actual snake remains a separate dependency; deletion of those counter clauses from the selected proof does not remove that mathematical obligation.

The 63 occurrences in counter 12 retain multiplicities. They are not replaced by a set of 57 vertices. Its literals are negative primary literals, so the counter measures absent-corner occurrences. Counter 4 uses positive primary literals; its upper limit of 18 therefore expresses a lower limit of three absent corners. The endpoint counter retains all 512 endpoint inputs even though many do not occur in the selected clauses.

## Packed proof and checker limits

The audit decoded the actual natural-number literals saved in all generated data modules. It checked each decoded clause against the renamed LRAT clause and each hint key against the precise clause identifier currently stored at that key. It independently propagated all ordered hints using the decoded clauses. Every step reached a contradiction before its derived clause was inserted.

All 108 checkpoints were checked in their actual tree order. Every retained clause exactly matched the preceding database. Any discarded clause had no future use. Before overwriting a key, the audit checked that the previous clause had no use after the current step. Thus the check covers the actual reuse schedule, rather than relying on the reported number of slots.

| Quantity | Observed value | Checker limit |
|---|---:|---:|
| Selected inputs | 3,500 | — |
| Deductions | 50,082 | — |
| Ordered hints | 2,628,221 | — |
| Segments | 435 | — |
| Checkpoints | 108 | — |
| Distinct used keys | 6,902 | 8,191 available positive keys |
| Largest actual key | 8,190 | 8,191 |
| Largest proof variable | 1,695 | Strictly below 2,400 |
| Longest derived clause | 62 | Strictly below literal fuel 255 |
| Most hints in one step | 751 | Strictly below hint fuel 4,095 |

The final derived clause is empty, with original identifier 183989, stored at key 4096. The audit verified 43,226 insertions that overwrote a currently retained clause. All replacements respected the final-use test.

The semantic indices 2400 through 2415 exceed or meet the checker’s literal offset. None occurs in the selected input clauses or proof. They remain ordinary semantic inputs used to interpret the full endpoint counter; they are never packed as proof literals. The distinction matters because the proof checker’s offset restriction applies to proof literals, while the semantic table can contain additional unused input meanings.

The inspected `LratFast` source uses 13-bit words, key mask 8191, literal offset 2400, literal fuel 255 and hint fuel 4095. The referenced previously compiled checker object matches the dependency hash in the saved successful milestone 112 receipt. This audit checked that object identity and the current source constants; it did not rerun or independently reconstruct that compiler invocation.

## Source correspondence

All 220 generated proof sources correspond to their 220 ported sources. The complete plan also includes the selected CNF module, for 221 modules in total. Every planned artifact hash matches, and the module order respects every dependency within the exported set.

There is one additional textual normalization beyond import prefixes and the final axiom print: all 220 original generated sources use CRLF line endings, while the ported sources use LF. This follows from the exporter reading text with universal newlines before writing UTF-8 bytes. The audit reported this difference and then compared exact bytes after precisely these three transformations:

1. Replace CRLF with LF.
2. Add the `Recovered129G` prefix to the designated local import paths.
3. Append the single axiom-print command to the final refutation module.

No other difference was found. The selected CNF module was independently parsed and compared with the renamed input selection rather than treated as a port of generated proof text.

## Evidence and remaining scope

The successful audit is recorded in `data/export-review.json`; its auditor is `audit/audit_export.py`. The JSON includes the complete file-hash inventory and rechecks every recorded input at the end of the run. It preserves the producer’s pending Lean-replay and semantic-interpretation statuses.

| File | SHA256 |
|---|---|
| `audit/audit_export.py` | `55196d779b175a1a6eb13f11327abfe2c4fc4b3d6749ddcbdcc1ecaf2cd364b1` |
| `data/export-review.json` | `9228f83c3b1a1f8656375d23016fe94e4d22b38928cf77d1aed94a6ca53a070f` |
| `data/proof-plan.json` | `a2b44308f79587131c3e39a600e824a64137aae6218c1b3c8ef927c5e0952128` |
| `data/selected-core-semantics.json` | `32fce494b2541659c856bd0124ad17533a6df9d9751ca74039a9fee7ea4ea488` |
| `work/export/triple129.cnf` | `aae59337e978a49e0bee8eba96d25c20a350fab92ca172b257f8003f5fcbf5ec` |
| `work/export/triple129.lrat` | `61393d5e85d64750c1a106f18b76c74e9f20034d1a0b3aa7eefebb2d7daedfc2` |

This export faithfully represents the independently checked selected contradiction and satisfies the inspected packing limits. A Lean-checked local exclusion still requires successful completion of the exported proof modules and the actual-snake semantic interpretation, including the fourth-count and other-three constraints. No exclusion of other branches, universal six-count lower bound, or improved global snake upper bound follows from this export audit alone.
