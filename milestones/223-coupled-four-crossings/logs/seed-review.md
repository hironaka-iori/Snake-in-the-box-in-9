# Round 223: seed and coupled-query review

Use forest index 0 in `milestones/195-shortened-reroutings/data/forest-profiles.json`, extracted from `work/bank9.json[123].vertex_sequence` at coordinate 7. It is the unique listed two-path face with 98 vertices and has minimum crossing count four over all nine coordinates. The recommendation is one target-192 query with both face selections and all four port locations variable, endpoint 0 retained and the other endpoint free.

## Exact seed and schema

`forest-profiles.json` has a `bank_forests` list. Each record gives `seed`, `coordinate`, two ordered `paths`, four `ports`, `vertices`, three ordered `complement_paths`, and `complement_vertices`. `paths` are the alternating inner components; `complement_paths` contain both global endpoints. All values in these component lists are projected Q8 vertices.

For forest 0, the five consecutive component edge lengths are

\[
46,83,32,13,13.
\]

The two-path face has 98 vertices and the three-path face 94. Each face is parity-balanced. The original crossing-edge indices, numbered from zero, are 46, 130, 163 and 177.

| Face | Ordered component endpoints | Edges |
|---|---|---:|
| Three-component face | \(0\to232\) | 46 |
| Two-component face | \(232\to35\) | 83 |
| Three-component face | \(35\to208\) | 32 |
| Two-component face | \(208\to195\) | 13 |
| Three-component face | \(195\to88\) | 13 |

The ports are \(\{35,195,208,232\}\). Normalize coordinate 7 to the final coordinate by deleting bit 7 from each original vertex and placing its old bit 7 in bit 8. Then the three-component face lies in 0 through 255 and the two-component face in 256 through 511. The original endpoints remain 0 and 88.

The bank extraction, component sequences, four crossings, disjointness and full 192-vertex induced path were reconstructed directly from the saved data. The normalized transition sequence, canonicalized by first occurrence in either orientation, has SHA-256 `c408c2b955784a69b4a0ca395de188b12d9579a38c8c144a0fe10483116b1558`.

The alternate balanced seed is forest index 11, bank entry 32, coordinate 7. It has components of lengths 12,47,47,47,34, face occupancies 96 and 96, ports \(\{27,48,208,251\}\), and normalized endpoints 0 and 152. Its two 47-edge paths are exchanged by permutation \([3,1,4,0,2,5,6,7]\) followed by XOR 63. It has minimum crossing count two in another coordinate. The successful `bank-four191-fixed.json` reconstruction used this forest, not forest 0.

Forest 0's unequal 83/13 component lengths prohibit an isometry exchanging those two components. No paired-path involution should be imposed. The empty match list in the saved symmetry comparison is not a classification of its other stabilizing symmetries.

## Previous results that restrict interpretation

The old `bank-four192.json` query fixed forest 0's entire 98-vertex face and all four ports, seeking 95 opposite-face vertices. It returned `UNKNOWN` at 120 seconds, with 89,924 branches, 8,487 conflicts and no witness. Its minimum sampled free memory was 1,670,873,088 bytes. This particular query stopped at its time limit; the separate shortened-state search stopped for low memory after six completed states and 238 discovered states. Neither gives a fixed-face exclusion.

Round 193 exhaustively established closure of the saved 131 symmetry classes under length-preserving contiguous replacements through 33 edges, together with blocked endpoints. It does not exclude arbitrary coupled changes. Round 194 excluded one length-preserving contiguous replacement through 44 edges followed immediately by one endpoint addition. It does not exclude longer replacements, removal of a former global endpoint, simultaneous changes in several regions, or arbitrary reordering through new vertices.

The round-192 at-most-four-omission exclusion concerns normalized bank entry 25. It must not be transferred to bank entry 123 without a matching equivalence argument. Round 196's four-omission result concerns a specific safe quotient and counts omitted orbits. Round 200's trimming and repair results concern specified Q7 parent copies. Neither covers the coupled Q9 query recommended here. The whole fixed 98-edge parent family excluded in round 222 also differs: the proposed two-path face is variable, and the construction has four crossings.

## One finite query

Use all 512 Q9 vertices. Select exactly 193 vertices, exactly four edges in coordinate 8, and exactly two endpoints. Retain vertex 0 as one endpoint. The other endpoint is variable. Both face selections and the four selected vertical edges are decision variables; do not fix the old component lengths, face occupancies, port pairs or component pairing.

Every cube edge variable must equal the conjunction of its endpoint selections. Give each selected nonendpoint degree two and each endpoint degree one; unselected vertices have degree zero in the induced-edge variables. This preserves all same-face and cross-face contacts. A vertical edge is selected precisely when both projected copies are selected, so the four ports are exactly the intersection of the two projected face selections. Do not subtract these four overlaps when counting Q9 vertices: the two layer copies are different vertices.

Require connectedness, or use the degree relaxation with recorded cycle exclusions and accept a candidate only after complete connectivity and all-pairs inducedness validation. With exactly two degree-one vertices and all other selected degrees two, any disconnected selected component is a cycle. Each such cycle gives the valid cut that at least one of its vertices must be omitted. Degree counts alone are insufficient.

For a single bounded first query, a total omission budget of 12 original Q9 vertices is a reasonable explicit search restriction. Require at least one omission in each face and at least one replacement port, for example at most three of the four original vertical edges retained. These choices force the query to change both faces and port locations. They are heuristic restrictions, not necessary conditions for every possible 192-edge snake. Use the known seed as a hint; it has only 192 vertices and therefore is not itself a feasible target assignment. Do not impose a fixed 98/95 face allocation.

The two old endpoints have opposite parity. A 192-edge path has endpoints of the same parity. With endpoint 0 retained, the other endpoint must have even Q9 parity, and the selected colour counts are exactly 97 even and 96 odd. Since four crossings return to the starting face, both endpoints lie in the lower, three-component face. Vertex 88 may remain selected internally, but cannot remain the other endpoint. In projected face counts, lower-face parity and upper-face parity have opposite signs. Keeping both original endpoints would make the target impossible for a purely parity reason.

## Omission span is optional

Requiring the omitted original positions to span more than 44 edges is sufficient to place a candidate outside a single replacement of at most 44 edges, in the fixed seed alignment. It is not necessary for escaping the exhausted family. An endpoint may be removed and replaced, the route may change in another manner, or the operation may involve several changes not represented by that one-replacement-then-addition rule. Nor does such a span condition classify alignments under all cube symmetries.

Therefore do not treat `span > 44` as a sound general pruning rule. Omit it from the recommended initial coupled query. It can be added later only as a clearly labelled restriction if the purpose is to force widely separated edits. The full coupled model already permits changes beyond the completed local-repair families.

## Source pins and limits

| File | SHA-256 |
|---|---|
| `work/bank9.json` | `0b973ddcd371680ad4efe07c01008c29437280514926daf1a67d99b6ba510edb` |
| `195/data/forest-profiles.json` | `9a29adaef98c59a9e6c7d28e633af8bc010defbbda0831aa456a61d46b0a929f` |
| `195/data/symmetry-comparison.json` | `1043424380001ec4216cda13c7d3b414d24f977dcb17c557bc5dcdb0356d5820` |
| `195/data/bank-four192.json` | `ff72459d5ea88ea9e85ec0356aea78434ac89ff9ad94ab55b7bd5ae4d8194f53` |
| `195/data/bank-four191-fixed.json` | `69a06811023901374557152e7c5f4d35a2d25c3a124c3db6c88060120a64e1b7` |

Here `195/data/` abbreviates `milestones/195-shortened-reroutings/data/` under the repository root. This is a bounded source and saved-witness review with small exact reconstruction. No solver, compiler, software tests, new construction search or manuscript edit was performed. Existence within the proposed neighbourhood remains unresolved; a timeout supplies no exclusion, and any infeasibility would apply only to the explicit query restrictions.
