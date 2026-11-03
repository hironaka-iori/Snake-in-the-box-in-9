# Independent audit of the direct cardinality clauses

The audit passes. All 235 added clauses have complete ordered unit-propagation derivations from the original 106348 input clauses. Every one of the 132921 references was replayed. There are no references to earlier derived clauses, future clauses, or the clause being proved.

The independent auditor imports neither the preparation script nor its encoding or proof-checking helpers. It rebuilds the full formula using a separate implementation, reconstructs the six corner lists directly from the cube geometry, parses the saved proof as a stream, and uses a fresh three-valued assignment for each derivation. The audit ran no solver or compiler and changed no input, proof, or job record.

## Formula identity and count interpretation

The seven directions are 0120324, with normalized vertices

\[
(0,1,3,7,6,14,10,26).
\]

At each of the six internal centres, the 21 relevant opposite corners flip two coordinates other than the two prescribed path directions. The ordered lists match the saved lists exactly. An additional enumeration of all 512 vertices independently verifies each set by Hamming distance and its excluded coordinates. Across the six lists there are 126 occurrences and 100 distinct corners: 79 occur once, 16 twice and 5 three times. The summed counter retains those multiplicities.

The original formula has 7277 variables and 106348 clauses. Its complete bytes agree with the milestone-125 bounded-search input. The independent reconstruction also agrees clause for clause, literal for literal, and byte for byte, including allocation of every counter variable. The first 106313 clauses contain the window, degree and endpoint conditions, the six individual count bounds, square and six-cycle exclusions, and the six-count upper bound 22. The remaining 35 clauses are the saved induced-cycle cuts. Each saved cut was independently checked for distinct cube vertices, connectedness and induced degree two.

Selected-vertex variable \(X_v\) is numbered \(v+1\). Therefore each negative literal \(\neg X_v\) means that the corner is absent. The six lower count bounds are

\[
(1,2,1,3,1,1).
\]

For a centre whose lower bound is \(k\), choose every set of \(k-1\) omitted corners and require at least one absent corner among the other \(22-k\) corners. This clause family is equivalent to at least \(k\) absent corners: fewer than \(k\) absent corners fit inside some omitted set, while at least \(k\) cannot all fit inside any such set.

The auditor enumerated the complete family, including literal order and omission indices:

| Internal position | Required absent corners | Clauses | Literals per clause |
| ---: | ---: | ---: | ---: |
| 1 | 1 | 1 | 21 |
| 2 | 2 | 21 | 20 |
| 3 | 1 | 1 | 21 |
| 4 | 3 | 210 | 19 |
| 5 | 1 | 1 | 21 |
| 6 | 1 | 1 | 21 |
| Total | | 235 | |

All 235 clauses are distinct. They contain only negative selected-vertex literals, with no endpoint or auxiliary variables. Their source lower bounds are already represented in the original formula. The audit checks this implication by replay, without assuming that the added clauses are new axioms.

## Ordered proof replay

The proof identifiers are exactly 106349 through 106583 in increasing order. Every streamed proof line agrees exactly with its corresponding JSON row: identifier, centre, omitted indices, clause and ordered references.

For each proposed clause, the checker first assumes the negation of every literal in that clause. It then reads each referenced original clause in order. A reference must be either unit under the current assignment or already contradictory; a satisfied clause or a clause with two unassigned literals is rejected. A unit reference assigns its unique remaining literal. A contradiction is required on the final reference, and no references after that contradiction are accepted.

The replay checked 132686 unit propagations and 235 final conflicts, giving exactly 132921 references. Individual derivations use between 140 and 1006 references. Every reference lies between 1 and 106348, so each derivation depends only on original inputs. No added clause is trusted or used as a premise, even after its own derivation has passed.

The augmented formula has the same 7277 variables and exactly 106583 clauses. Its first 106348 clauses equal the original formula, and its remaining clauses equal the proved clauses in identifier order. Its full serialization was independently reconstructed and compared byte for byte.

## Scope and subsequent proof composition

This proves that the augmented formula is equivalent to the original formula as a propositional constraint system. It does not refute either formula. It does not prove a new six-count floor, and it makes no claim about the result of a subsequent native search.

If a subsequent contradiction uses the augmented input, its proof must be combined with these 235 derivations and replayed against the original 106348 inputs. The derived identifiers occupy 106349–106583; later derivations must respect the augmented numbering and all deletion dependencies. Trimming or exporting with 106583 trusted inputs would omit the justification established here. The later contradiction, its concrete interpretation, and its Lean checks remain separate obligations.

The checked original formula includes the existing actual-count restrictions justified by the repaired milestone-125 theorem. The current theorem source and successful receipt pins agree with the preparation provenance. The earlier timeout and failed-compilation records remain unchanged; this audit does not reinterpret them as completed proofs.

## Reproducibility and pins

Run `scripts/audit_prelude.py` from this milestone for a read-only summary. The optional `--output` argument creates a new JSON file exclusively and refuses to overwrite an existing file. The audit verifies all preparation and proposal pins, records its own source hash, and rehashes every inspected pinned input after the checks to detect concurrent changes.

The saved review records each clause's centre, omission indices, size, reference count, propagation count, final conflicting input and proof-line hash. It also records all input hashes and exact aggregate counts.

| Artifact | SHA256 |
| --- | --- |
| Independent auditor `scripts/audit_prelude.py` | `747f6824581e96a3b49a7cd0effacb27ebab1aab43d9934bb5a9ccc76fb43c9d` |
| Review evidence `data/prelude-review.json` | `3f5eb4263bc4a33259ba94fa96d6334584c6cafb6f5413c19cd33f4e3f80ed5a` |
| Original formula `work/original.cnf` | `467a58303f629688e5c5dd26c83e7d4c64ccede4805ab2577823e4dbed30e91a` |
| Ordered derivations `work/prelude.lrat` | `3e6ca9a67e4cd65e9ebaae83183b17afee274266aeb1ec0a0920c9d0d669a35a` |
| Augmented formula `work/augmented.cnf` | `0f7eb49e98d6adc53bdc66edea78dffab922b8081bf21c8c9598b2eb446ec9e1` |
| Direct-clause data `data/direct-clauses.json` | `1b5ca3b77ed055718fc870b9ccefd36f4ee431dcec3ce98f7de28468a85200b3` |
| Preparation source `scripts/prepare.py` | `470edc269eafb6168ebb35ebf02f1886c7eb58c773ffe506c1d793c8c2ef2984` |

The saved check completed at 2026-11-03 06:14:18 UTC. No substantive defect was found within this scope.
