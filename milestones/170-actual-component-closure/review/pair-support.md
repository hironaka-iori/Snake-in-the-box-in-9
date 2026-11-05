# Accepted replacement

The coordinating agent replaced the table-based draft below after it exceeded the memory limit. The accepted source proves bit support using Nat.testBit_xor and Nat.testBit_two_pow, and proves parity preservation by list induction and Boolean algebra. Only nine unit-parity cases and sixteen Boolean exchange cases use ordinary decide. Both public theorems passed the guarded compiler with no new axioms. The source and receipt hashes are in data/PairSupport170-audit.json.

## Historical draft review

# Pair support and adjacency certificates

Source: lean/PairSupport170.lean, namespace Snake9.PairSupport170. Status: drafted, no compiler invoked by this worker.

The public theorem pair_support_unique states that equality of two pair vertices with distinct coordinates determines their unordered coordinate supports. It inspects one coordinate bit, then applies the existing pair_injective_right lemma. The bit-support lemma is a certificate over only three coordinates (729 tuples); there is no four-coordinate equality enumeration.

The public theorem pair_not_adjacent states that any two pair vertices are nonadjacent, including repeated-coordinate pairs that equal zero. A private nine-bit parity invariant is false on every pair and true on every triple. Those certificates use respectively 81 and 729 coordinate tuples. The existing neighbor_pair lemma represents any neighbor of a pair as a triple, giving a parity contradiction. There is no enumeration of all vertex pairs or four-coordinate adjacency tuples.

No new axioms, sorry, admit, native_decide, Mathlib import, or preceding-file edits were introduced. The public results require no new caller-supplied assumptions beyond coordinate distinctness in pair_support_unique. The finite certificates and Lean elaboration still require the coordinating agent's serialized compiler check.
