# Integer periods, colour-layer fragments, and controlled exceptions

The main bank is q9_three_axis.in, with 5,062 192-step Q9 transition words. This experiment differs from the earlier local motif-growth model, four-donor seam alignment, fixed-coordinate reordering, and the exhaustive strictly periodic p≤8 computations. It uses empirical integer lags inside an individual source word. A large lag score is a rule for selecting templates, not evidence that the underlying optimal snake is periodic.

**Colour-layer fragments.** For a row w, rank lags p=12,…,80 by the fraction of positions where w[i]=w[i-p]. Sample one of the top six. Select a separator coordinate with a prescribed crossing-count range and split the word at all its occurrences. The pieces live in alternating colour layers of that coordinate. Find a coordinate permutation π fixing the separator that maximizes the number of matched letter pairs w[i]=π(w[i-p]) involving nonseparator transitions. A finite assignment dynamic program solves this objective. Independently for every used fragment, allow either orientation and one of identity, π, π inverse. All fragment orders are allowed. A further option replaces a 1-, 2-, 3-, 5- or 8-transition interval by a word at displacement +p or -p, mapped through the appropriate π inverse or π. Donor candidate counts and the number of repaired blocks are bounded per configuration. Unit crossings separate consecutive fragments and the walk is reconstructed from the origin as the order changes. Every strict target has 192 transitions. The three flexible runs additionally allow any remaining one to three transitions, split arbitrarily between the two ends of a legal 189–191-edge prefix. Repeated configurations and prefixes are possible.

Across 43,000 sampled fragment trials, 17,043 reached their search cap. No 192-edge witness was found. The three flexible runs constructed, respectively, 100, 103, and 96 distinct 191-edge equivalence classes, all in the existing 131-class reference. These counts can overlap across runs. A second Python implementation independently exhausted the exported option domains of 48 additional uncapped cases, recomputing every eligible option from the donor word, lag and permutation. Reassembling any permutation of these saved fragments with at most two borrowed motifs gave zero 192-edge paths in all 48 cases.

**Recurrence on phase classes.** For a separate sample, take one of the five highest-scoring lags from 12 through 60. Choose two, three or four distinct positions modulo p. All transitions in those residue classes are reselected. Each residue starts with any one of nine axes. On its subsequent appearances require x[t+p]=π(x[t]), with at most one exception per selected residue; any coordinate can be chosen at that exception and the recurrence then continues from the new value. Outside the selected residues, the source word is retained. Among 100,000 sampled templates, 90,448 were exhausted, including every one of the 45,000 two-residue trials. The other 9,552 reached their node caps. No target run found 192 edges. These partial-coordinate templates do not describe every globally periodic or nonperiodic path.

**Controls.** Two damaged 191-edge source words were reconstructed by fragment assembly, including a seven-piece permutation and a case using a donor exactly 80 transitions away. A separate recurrence control recovered 191 with p=48 and exactly one genuine deviation on each of residues 33 and 36. Python independently checks every pair of output vertices, reconstructs the selected blocks and verifies the prescribed recurrence and exceptions. The target counts describe the searched templates, not a global Q9 bound.

From the parent workspace, compile with the local macOS compiler and libc++. Deterministic samples use std::shuffle.

```sh
d=q9_periodic_layer_words_20261121
clang++ -O3 -std=c++20 "$d/search.cpp" -o /tmp/q9-period-layers
clang++ -O3 -std=c++20 "$d/snapshot.cpp" -o /tmp/q9-period-snapshot
clang++ -O3 -std=c++20 "$d/residues.cpp" -o /tmp/q9-period-residues
/tmp/q9-period-layers 240 7711 120000 0 8 1 7 < q9_gap_generations/prior191.words
/tmp/q9-period-layers 1000 13681 120000 1 80 2 6 < q9_gap_generations/prior191.words
/tmp/q9-period-layers 6500 91177 35000 1 18 0 7 < q9_three_axis.in
/tmp/q9-period-layers 3500 8137 80000 2 36 0 10 < q9_three_axis.in
/tmp/q9-period-layers 12000 927589 45000 2 30 3 8 < q9_three_axis.in
/tmp/q9-period-layers 12000 39821 55000 2 42 3 12 < q9_three_axis.in
/tmp/q9-period-layers 9000 835721 85000 3 48 3 8 < q9_three_axis.in
/tmp/q9-period-snapshot < q9_three_axis.in
/tmp/q9-period-residues 4500 3263 2 1 200000 1 < q9_gap_generations/prior191.words
/tmp/q9-period-residues 45000 71149 2 1 45000 0 < q9_three_axis.in
/tmp/q9-period-residues 35000 90833 3 1 65000 0 < q9_three_axis.in
/tmp/q9-period-residues 20000 93103 4 1 85000 0 < q9_three_axis.in
python3 -B "$d/verify.py"
```
