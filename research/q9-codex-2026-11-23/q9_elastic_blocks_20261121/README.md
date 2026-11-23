# Q9 open paths reassembled from independently transformed blocks

Both experiments target a simple induced path with 192 edges. The 800 near-paths are the local q9_onechord_expanded_800.txt rows. The 131 clean inputs are decoded from q9_four_piece_191_classes.txt. Each input row was independently checked for the expected number of vertices and chords.

## Two blocks and one additional vertex

Cut one of the 131 clean paths at any of its 191 edges, obtaining two nonempty ordered pieces. Fix the longer piece in the cube, allow independent reversal of each piece, and embed the shorter piece by any coordinate permutation and translation. Connect their facing ends by a two-edge path through a newly placed middle vertex. Fixing the embedding of the longer piece preserves generality because cube isometries act on both pieces simultaneously. The exhaustive search returned no 192-edge witness for the 25,021 row/cut choices. It considered 100,084 orientations, counting equivalent choices separately, with 197,930 viable placements of the middle vertex and the facing endpoint of the moving piece.

The solver in two_blocks.cpp assigns target axes in a precomputed order, pruning an assignment when one of the determined offsets violates the distance constraints. The separate program two_check.cpp follows transitions in order and branches over all unused target axes at each first occurrence. It uses different neighbourhood construction and does not use the first solver’s coordinate-symmetry pruning. Each accepts an ordered vertex list per input line and prints a witness at the first success. A deleted internal vertex in a known 191-edge path supplies the positive control.

## Multiple blocks

Sample partitions into 5, 7, 9 or 12 blocks of at least three vertices. Keep the longest block in place and choose each remaining block’s direction, translation, and either the identity or an allowed coordinate transposition independently. Join neighbours by one edge. For the clean 191-edge inputs choose one random join per partition where a two-edge link inserts a new vertex. For the one-chord inputs use single-edge connections throughout. A partition is eligible if every block is internally induced. A search truncates at its per-partition placement budget. The eight runs drew 214,000 partitions, including 159,820 eligible partitions and 5,356 truncated searches. They returned no 192-edge witness. These are restricted families; the optimal Q9 snake length does not follow from the results.

Use the commands below from the workspace root with the system macOS clang++ and libc++ to reproduce the runs. The multi-block enumeration uses std::shuffle. Each run’s seed is part of its log filename.

```sh
cd q9_elastic_blocks_20261121
clang++ -O3 -std=c++20 search.cpp -o /tmp/q9-elastic
clang++ -O3 -std=c++20 two_blocks.cpp -o /tmp/q9-elastic-two
clang++ -O3 -std=c++20 two_check.cpp -o /tmp/q9-elastic-check
/tmp/q9-elastic-two < parents191.vertices
/tmp/q9-elastic-check < parents191.vertices
python3 -B verify.py plant | /tmp/q9-elastic 1 5 1893 30000000 37 1
python3 -B verify.py missing | /tmp/q9-elastic 1 5 1277 30000000 37 3
python3 -B verify.py missing | /tmp/q9-elastic-two
python3 -B verify.py missing | /tmp/q9-elastic-check
/tmp/q9-elastic 60000 5 7183 220000 37 0 < ../q9_onechord_expanded_800.txt
/tmp/q9-elastic 24000 7 14997 220000 37 0 < ../q9_onechord_expanded_800.txt
/tmp/q9-elastic 25000 9 30011 220000 18 0 < ../q9_onechord_expanded_800.txt
/tmp/q9-elastic 18000 12 6221 150000 12 0 < ../q9_onechord_expanded_800.txt
/tmp/q9-elastic 24000 5 94873 220000 37 2 < parents191.vertices
/tmp/q9-elastic 20000 7 19679 170000 37 2 < parents191.vertices
/tmp/q9-elastic 25000 9 34031 220000 18 2 < parents191.vertices
/tmp/q9-elastic 18000 12 9821 150000 12 2 < parents191.vertices
python3 -B verify.py verify control.log insert_control.log two_control.log second_control.log
```
