# Round 221: exact rational-point addendum

The separate rational audit passed. Both saved square models admit exact rational points of objective greater than 94. All saved rows, all variable bounds and every simple-cycle occupancy inequality were checked. An independent convex-mixture calculation also produces objective exactly 94 for each root. The baseline square review and its receipt remain unchanged.

| Root | Exact objective | Saved rows | Fractional coordinates | Cardinality-94 mixture fractional coordinates |
|---:|---:|---:|---:|---:|
| 0 | \(24143609460502861609/251494331833708890\) | 3,118 | 424 | 434 |
| 78 | \(20431726624023570157/213321091551694027\) | 3,101 | 424 | 438 |

Each vector has 574 coordinates. Every coordinate is between 0 and 1; all equalities and inequalities hold using exact rational arithmetic. Objectives match the saved certificates and summaries and lie below the previously audited exact upper certificates. The largest coordinate denominator has 59 bits. No numerical optimality assumption is used.

## Every occupancy cycle

For each of the 337 edges at each root, the audit checks the saved 158-entry potential after deleting that edge. The source potential is zero, the target is reachable, and all 336 remaining edges satisfy the exact difference bound with costs \(c_u+c_v\), where \(c_u=1-x_u\). The closing condition is

\[
p(t)+c_s+c_t\ge 2.
\]

This totals 113,232 edge inequalities per root. For any simple cycle containing the deleted edge \(st\), telescoping along its complementary path gives

\[
p(t)\le 2\sum_{u\in C}c_u-c_s-c_t.
\]

Therefore \(\sum_{u\in C}c_u\ge1\), equivalently \(\sum_{u\in C}x_u\le |C|-1\). Every simple cycle has an edge, so the saved potentials cover the entire occupancy-cycle family. The minimum cost is exactly 1: the saved static cycles with vertex sets \(\{20,22,84,86\}\) at root 0 and \(\{8,9,10,11\}\) at root 78 attain it.

These occupancy inequalities concern selected vertices. They do not establish the disagreement-parity inequalities on longer cycles.

## Exact objective 94

The audit constructs the actual one-edge paths \([0,2]\) and \([78,14]\), encodes their vertex, endpoint and edge-product values, and checks every saved row. Each has objective 2. If the corresponding audited objective is \(Q\), the mixture weight

\[
\lambda=\frac{92}{Q-2}
\]

lies strictly between 0 and 1. The resulting mixture has objective 94. Its 574 variable bounds and all saved rows were independently recomputed. All occupancy-cycle inequalities persist by convexity. The weights are

\[
\lambda_0=\frac{23137478528701217880}{23640620796835443829},\qquad
\lambda_{78}=\frac{19625540422755850484}{20005084440920182103}.
\]

This supplies reproducible exact mixtures without assuming an additional producer target certificate. The mixtures remain fractional and do not describe actual partners.

## Provenance and remaining scope

Model hashes agree with the frozen baseline audit. Certificate, source, summary, execution and output-stream hashes agree. The reconstruction execution is terminal with exit 0 and no stop, elapsed 2.985 seconds, maximum sampled private memory 51,593,216 bytes and minimum sampled free memory 1,350,664,192 bytes. These resource figures are sampled observations.

This audit ran no optimizer, compiler, search, flow computation, basis elimination or software tests. It checks certificate contents directly. It does not certify the full subset-forest family for these new rational points: only the 25 or 29 saved subset rows are included. The round-220 flow certificates refer to different rational vectors and do not transfer. Arbitrary-integer flow certificates would be required to settle that remaining scope without unsafe fixed-width capacity arithmetic.

No Boolean partner, new global snake bound, exact LP optimality or concrete Lean assembly is claimed. The evidence shows that the saved square model together with all occupancy-cycle inequalities still admits objective 94. The source and evidence pins are recorded in `data/rational-audit.json`; these addendum files are frozen after this review.
