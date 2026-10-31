# Round 6: final binary checkpoints, standard certificates and an alternative PB prototype

## Final binary checkpoints: complete independent replay

The final agreed snapshots were reconstructed from the source window encoding and the exact folded eight-cycle manifests. No SAT model or empty clause is present in either three-centre query:

- 0120: 28,242 checked RUP steps, 2,708,052 unit hints; 94,557 active static cycle cuts.
- 0123: 25,935 checked RUP steps, 2,852,769 unit hints; 94,280 active static cycle cuts.

Both remain unresolved UNKNOWN/ACTIVE. These numbers supersede round 5's earlier snapshots. The complete replay results are in loop_independent_results.json.

The cached set-based tautology test is semantically equivalent to the earlier quadratic scan: it is evaluated on the clause literal set and subsequent watch operations only reorder that set. Original clause IDs and proof meaning are preserved. Root-propagation regressions passed after this change. Heuristic checkpoint restoration copies only phase preferences and finite nonnegative activities plus a positive finite increment; every logical trail and reason is reconstructed from the CNF. Thus the restored heuristic is not an added mathematical premise.

## Standard DIMACS/LRAT capsule

I independently ran verify_certificate.py --rebuild. It reads the exported compressed DIMACS and positive-hint LRAT, reconstructs the source Encoding and all geometric cuts, and verifies 7,621 RUP steps with 1,604,124 hints including the empty clause. The 77,868 cuts are valid induced eight-cycles. This is a standard-format computational proof capsule, not a Lean-verified theorem.

I found a real scope-label bug in the first exporter: --input was configurable but its manifest always claimed pointwise score>=22. A valid cap-zero proof could therefore have been exported under an unjustified stronger label. The main agent fixed both exporter and verifier to require a one-centre, cap-21, occupancy-bonus query with the exact objective and a radius in 4..9. Five mutations (including an actual valid cap-zero UNSAT input, multiple centres, disabled bonus, wrong objective and radius three) now fail in both exporter and verifier: ten correct negative controls. The proper capsule still passes --rebuild. See certificate_scope_review.py and certificate_scope_results.json.

## Strict mathematical corollary q>=23

The existing project singleton theorem gives alpha>=1. If q=22, nonnegative integer coefficients force alpha=1 and 2e2+e3+V=1, hence e2=0. But D=3e3 and D<=6e2 force e3=0; V=E_le2+3E1<=4e2 forces V=0. This contradicts the remaining sum being one. Therefore the cap-21 computational exclusion together with the existing singleton theorem implies q>=23 on internal vertices. The capsule itself must continue to be labelled as excluding cap 21; the strengthened statement is a separate mathematical corollary.

## Generalized totalizer

The requested alternative positive weighted PB encoding is implemented in gt_pb.py. It supplies an explicit canonical-extension helper and leaves the existing BinaryCNF gate witness mechanism untouched. Forward auxiliary variables are not claimed to be unique or reverse equivalences. Complete proof and interface details are in GT_ENCODING.md.

Small tests cover 1,736 input assignments, including signed/repeated/complementary literals and constants. Every canonical extension satisfies the clauses; all above-cap fixed inputs produce unit-propagation conflicts. Real three-centre geometric bank controls also pass. No large SAT solve was run with GT.

The cost tradeoff is material: GT produces roughly 611,000 PB clauses versus 28,000 for binary addition. Including the same static cycle cuts, each three-centre query grows from about 173,000 to 756,000 clauses. Stronger propagation may still help, but the implementation is an experiment requiring independent review and measured search results, not a demonstrated speedup or a proved new bound.

## Follow-up: bounded GT search, no numerical conclusion

At the main agent's request, the separate gt_probe.py runner performed sequential fresh ten-solve-second experiments on both real cap-254 shapes with all filtered eight-cycle clauses. It restores the temporary builder override immediately after construction and leaves the existing binary checkpoint files unchanged.

0120 ended UNKNOWN with 1,859 checked RUP steps and 119,259 hints, using 15.915 total wall seconds including initialization and saving. 0123 ended UNKNOWN with 1,318 checked steps and 81,513 hints, using 15.994 total wall seconds. Both complete CNFs and checked learned proofs are saved under GT_probes. No SAT witness or final empty clause was obtained.

The GT tests are fresh bounded runs whereas the binary tests accumulated retained learning across multiple slices. Accordingly no performance advantage is asserted from their incomparable samples.
