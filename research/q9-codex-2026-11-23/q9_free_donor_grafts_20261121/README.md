# Endpoint-aligned donor grafts with globally free repairs in Q9

The source is the 131 induced 191-edge paths in q9_gap_generations/prior191.words. An earlier two-anchor donor experiment preserved the exterior. Here the entire transplanted donor segment stays in place and every exterior vertex incompatible with its interior is released. Additional remote gaps are allowed. The paired experiment simultaneously replaces two nonadjacent recipient intervals using two different donor classes, each different from the recipient.

## Geometry and search

Draw an interior recipient window of 12 to 55 edges and a donor subpath longer by 2, 4, 6 or 8 edges. Match the Hamming distance of the endpoints. A greedy coordinate matching uses local transition agreement at the beginning/end of the windows and a randomized tie term, while respecting endpoint-difference bits. An XOR translation then aligns both endpoints exactly. Reverse orientations are included. Every selected donor's entire transition word, up to relabelling and reversal, is absent from all equal-length windows anywhere in that recipient. The ranking draws 900,000 configurations, obtains 860,984 endpoint-compatible embeddings, and retains 13,063 ranked proposals. Sampling can repeat geometry.

For each graft, remove all exterior positions equal or adjacent to an interior donor vertex. The natural contacts with the two donor endpoints are allowed. Keep the full induced donor arc, so any path containing the fixed points must traverse that arc contiguously, possibly reversed. Choose the lowest cost transplant at each gain for every recipient. For pairs, require more than seven index steps between the first window end and the second window start, and no vertex overlap or adjacency between donor arcs. Rank the pairs by the number of exterior positions incompatible with their union. Select three low-cost pairs per recipient.

There are 524 single and 393 double geometries. For each, three ordinary cases leave 0, 12 or 32 additional holes in the compatible exterior. Release starts include remote holes outside the donor windows. For the widest follow-up cases, retain 100 or 125 total vertices, including the donors and independently sampled exterior runs, releasing up to 93 additional compatible recipient vertices.

The SAT search asks whether there is a connected induced path with **at least** 192 edges containing every fixed vertex. Its initial choice set is the whole nine-cube; pruning removes only vertices provably incompatible with the anchors' degree-two constraints. Ends, parity bounds and connectedness are enforced. The seed is a phase preference only. The two backends use CaDiCaL with totalizers and native Minicard constraints. Four example negative cases also have compressed, independently replayed DRAT traces for a separate degree/cardinality relaxation.

## Positive controls and audit

In the single control the 52 donor vertices and 136 compatible exterior vertices are retained. A 191-edge solution uses four vertices outside the recipient/arc hint. A separate double control transplants two nonadjacent longer arcs from two actual donor paths into an actual third host, preserving 53 donor vertices and 104 exterior points. Its recovered 191-edge solution uses 23 vertices outside the recipient/arc hint. The second SAT backend also recovers 191 at both controls. The saved control anchor sets were chosen using known complete paths, which are not supplied to the solver. The double control is constructed separately in double_control.py. The first-pass selected double pool in control.py had no planted witness of this form.

verify.py reconstructs the cube embeddings by replaying the donor transitions, checks all 13,063 ranked proposals, verifies distinct donors and novelty relative to the whole recipient, recalculates all exterior conflicts and fixed-vertex constraints, tests the paired separations, verifies all positive output distances, and confirms each donor appears as a contiguous arc in the output. The final counts are in verified.json.

## Reproduction

From the workspace root, use the host macOS clang++ and a Python installation with python-sat, CaDiCaL 1.9.5 and Minicard. The following commands belong in this order.

```sh
d=q9_free_donor_grafts_20261121
clang++ -O3 -std=c++20 "$d/rank.cpp" -o /tmp/q9-free-grafts
/tmp/q9-free-grafts 900000 172921 < q9_gap_generations/prior191.words > "$d/grafts.txt" 2> "$d/ranking.log"
python -B "$d/prepare.py" > "$d/prepared.json"
python -B "$d/wide.py"
python -B "$d/run.py" single cadical 4000 192 0 1572 > "$d/single-cadical.jsonl"
python -B "$d/run.py" double cadical 4000 192 0 1179 > "$d/double-cadical.jsonl"
python -B "$d/run.py" single minicard 3500 192 0 400 > "$d/single-minicard.jsonl"
python -B "$d/run.py" double minicard 4000 192 0 400 > "$d/double-minicard.jsonl"
python -B "$d/run.py" single minicard 7500 192 400 1572 > "$d/single-minicard-tail.jsonl"
python -B "$d/run.py" double minicard 7500 192 400 1179 > "$d/double-minicard-tail.jsonl"
python -B "$d/run.py" singlewide cadical 8000 192 0 240 > "$d/singlewide-cadical.jsonl"
python -B "$d/run.py" doublewide cadical 8000 192 0 234 > "$d/doublewide-cadical.jsonl"
python -B "$d/run.py" singlewide minicard 7500 192 0 240 > "$d/singlewide-minicard.jsonl"
python -B "$d/run.py" doublewide minicard 7500 192 0 234 > "$d/doublewide-minicard.jsonl"
python -B "$d/retry.py" > "$d/retry.jsonl"
python -B "$d/final_case.py" > "$d/final_case.jsonl"
python -B "$d/control.py" > "$d/control.jsonl"
python -B "$d/double_control.py" > "$d/double_control.json"
python -B "$d/verify.py" > "$d/verified.json"
python -B "$d/certify.py" /path/to/drat-trim --replay
```

Across all four batches, the 3,225 case records comprise 3,222 distinct fixed-vertex sets. Every record returned UNSAT at 192 edges or longer. Both solvers returned UNSAT independently for all 2,751 ordinary cases. In the 474 wide cases, 17 initially remained unresolved by either solver; 16 were settled at the next budget and the final instance by the 350,000-conflict run. This excludes only the tested anchor sets.
