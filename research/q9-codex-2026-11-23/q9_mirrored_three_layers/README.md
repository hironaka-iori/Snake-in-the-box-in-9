# Three-layer construction for central reflections in the nine-cube

Paths are measured in edges. The first frozen input contains 798 supplied seven-cube paths. A separate input contains 41,010 other seven-cube paths of 34–51 vertices extracted from the local eight-cube path and coil libraries. Each input row lists its vertex count followed by the vertices. The program checks each donor for repeated vertices, wrong edges, and chords.

The reflection exchanges three or four disjoint coordinate pairs and fixes the center vertex 0. Classify an orbit by the two bits of the first pair. Orbits with bits 00 form one wing and orbits with bits 11 form the other. In the remaining orbits take the representative with bits 01. These representatives form a full seven-cube. The two wings have no edges between them. An internal wing vertex represents a nonfixed two-point orbit under the remaining two or three swaps. The wings have 48 vertices for three swaps and 56 for four.

For a selected middle path in the seven-cube, project each of its vertices onto the remaining-coordinate orbits. Remove all occupied projections from each wing and restore only its connecting port. Reject nonunique ports, fixed ports, and a middle path touching the orbit of a neighbor of the center. In the 00 wing, compute a longest induced path from its port to a neighbor of the center. Stop at the first such neighbor to prevent a chord. In the 11 wing, compute a longest induced path from its port with free endpoint. An intersection between the two chosen wing projections is allowed. The resulting quotient path visits the 00, middle and 11 parts consecutively. The procedure does not cover revisits or middle paths outside the supplied inputs.

The DFS removes all neighbors of the previous endpoint other than the selected next vertex. Its upper bound counts the reachable vertices of each bipartite color. With color counts a and b, an extension uses at most min(a+b,2 min(a,b)+1) vertices. For each row the two wing optima are independent. Placements are enumerated under seven-coordinate permutations modulo the 48 center-preserving permutations commuting with the residual reflection, followed by all 128 translations. This gives 105 × 128 = 13,440 placements per input row, before considering the two traversal orientations. Rows and placements can describe isomorphic constructions.

In the first input the largest resulting paths had 168 edges for three swaps and 180 for four swaps. Both logged vertex lists passed independent pairwise nine-cube verification. Each row retained by the scanner was also checked before output. The logs give the number of orientations surviving the port and reachability tests. The result is exact within this finite template.

Run from this directory with a C++20 compiler and Python 3.10 or newer.

```sh
c++ -O3 -std=c++20 q9_mirror_3layers.cpp -o /tmp/q9_mirror_three
/tmp/q9_mirror_three 3 q7_quad_short20.txt 798 > /tmp/three3.result
/tmp/q9_mirror_three 4 q7_quad_short20.txt 798 > /tmp/three4.result
python3 verify_q9_mirrored_three_layers.py 3 /tmp/three3.result 4 /tmp/three4.result
gzip -dc q7_extra_middles.txt.gz > /tmp/q7_extra_middles.txt
/tmp/q9_mirror_three 4 /tmp/q7_extra_middles.txt 41010 > /tmp/three4_extra.result
/tmp/q9_mirror_three 3 /tmp/q7_extra_middles.txt 41010 > /tmp/three3_extra.result
```

For the additional 41,010 paths, each symmetry class covered 551,174,400 placements. With three swaps 159,438,878 oriented candidates survived the initial filter and the best lift had 170 edges. With four swaps 248,459,369 passed and the best lift had 180 edges. The independent all-pairs checker passed on all 18 and 12 running records respectively. The maxima over both tested libraries are thus 170 and 180 edges.

Separate experiments retained wings from the running records, trimmed up to four vertices off their inner ends, and allowed the complete seven-cube middle to change. With a conflict limit of 3,000 per port choice, targeting 192 gave 73 UNSAT and 27 UNKNOWN for three swaps, and 221 UNSAT and 54 UNKNOWN for four. The positive controls recovered 4 and 11 nine-cube paths. The bounded results concern these wing and trim combinations only. Raw logs and control witnesses are included.
