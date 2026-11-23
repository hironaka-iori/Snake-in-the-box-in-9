# Four-donor recombination with three free junctions

The bank *q9_three_axis.in* has 5,062 transition words. The 2,059 rows with exactly one nonconsecutive unit-distance pair supply the candidate donors and the orientation templates. A four-piece trial requires four different donor classes, also different from the template class. Splitting a template around three variable cuts leaves four target intervals. To propose a donor fragment, find a matching twelve-step pattern up to axis renaming at an arbitrary offset in either orientation of a different input walk. Match the remaining axes greedily by agreement with template transitions. An XOR translation identifies the common starting vertex of the motif. The two ends of proposed fragments can also shift along their own donor trace. Duplicate per-interval placements are removed. Any pair of retained pieces that overlaps or touches is rejected. At least two of the four retained geometries must differ from the template intervals.

The port solver inherited from the workspace searches the induced path with these pieces retained, with arbitrary order, orientation, three variable bridges and free terminal extensions. The goal is 192 edges. A total of m free vertices allows m+1 bridge edges and m terminal steps. The solver imposes limits of 18,000 matching nodes and 350 routes per pool. The narrow experiment samples gaps of one to six vertices, and the wide experiment samples one to twelve. Each instance allows randomly shifted quarter cuts. All donor placements, template sampling and caps are recorded by the source and the final log counters. Geometries can recur across trials.

For a further check, every 199th wide solver system is saved if all four arcs differed from the template. Its complete vertex arrays and donor intervals appear after FIELD in wide.log. Drop the first and final two vertices of each arc, retain the four interiors in place, and use the independent local CaDiCaL vertex-selection model to search for any induced path of at least 192 edges with those vertices. Every third saved case is also tested at 191, as a check on what this family constructs. Distinct 191-step results are compared against the 131-class reference. The independent verifier checks the saved arc's ordered transition pattern against its actual oriented donor interval, checks the union induced graph and verifies output paths and fixed-set membership. No formal SAT proof traces are saved.

The planted control has four altered fragments in its template. Four distinct single-chord parents with damage elsewhere donate the corresponding valid arcs; the control reconstructs a valid 191-edge snake across three separate gaps. The final verifier checks this path by all pairwise Hamming distances and compares the four original fragments to their source donors. A pilot with a too-short interval was interrupted, the minimum length check was added, and the reported wide run starts again from its original seed.

From the workspace root, using the host compiler and bundled CaDiCaL:

```sh
d=q9_four_donor_motifs_20261121
clang++ -std=c++20 -O3 "$d/search.cpp" -o /tmp/q9-four-donors
python3 "$d/control_input.py" | /tmp/q9-four-donors 0 1 1 71993
/tmp/q9-four-donors 2059 42 24 82311 < q9_three_axis.in
/tmp/q9-four-donors 24708 64 48 912019 wide < q9_three_axis.in
python3 -B "$d/relax.py" control
python3 -B "$d/relax.py" wide
python3 -B "$d/relax.py" stepping
python3 -B "$d/verify.py"
```


For the initially capped port systems, a deterministic replay built with `-DREPLAY_PORT_CAPS` prints every capped system (REPLAY lines). Its DONE summary matches the wide run. The caps mode of relax.py checks these fixed sets with the independent at-least-192 SAT formulation. Any remaining 191-edge stepping-stone cases capped by the SAT connectivity loop are passed to the independent port query. Reproduce the extra checks with:

```sh
clang++ -O3 -std=c++20 -DREPLAY_PORT_CAPS "$d/search.cpp" -o /tmp/q9-four-donor-caps
/tmp/q9-four-donor-caps 24708 64 48 912019 wide < q9_three_axis.in | awk '/^(REPLAY|DONE|FOUND)/' > "$d/caps.log"
python3 -B "$d/relax.py" caps
clang++ -O3 -std=c++20 verify_q9_matching_query.cpp -o /tmp/q9_four_donor_191_retry
python3 -B "$d/retry191.py"
```

