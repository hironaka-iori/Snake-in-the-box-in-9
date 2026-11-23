# Q9 one-chord vertex replacement search

The input contains 340 ordered walks with 193 distinct vertices apiece. Each walk has one extra adjacency among nonconsecutive vertices. There are 302 distinct vertex sets, and all 340 ordered walks are inequivalent after translation, coordinate permutation and reversal.

For position-independent tests each repeated vertex set can be examined once. For the positional deletion windows, use all 340 orders. Only full connected induced paths pass the last check, which compares every vertex pair.

## Results

The completed unrestricted search through four deletions and four additions found no 192-edge path. Restricted searches also found no witness while deleting six arbitrary vertices near the chord incidences and endpoints (index radius four), or seven or eight using index radius three. All replacement vertices can be taken from the full complement of the original set. The bounded SAT solvers returned UNKNOWN for all full six-replacement instances. See results.json for counters and separate construction families.

## Replay

Use a C++20 compiler. From this directory run:

```sh
clang++ -std=c++20 -O3 windows.cpp -o /tmp/q9_windows_replay
/tmp/q9_windows_replay 4 0 340 192 6 < walks.txt
```

The arguments set the index radius, first row, exclusive end row, target edge count and number of deleted vertices. With no extra option, the search uses as many additions as necessary for the exact target. The optional final argument `--unbounded-additions` permits any number of additions and treats the target as a lower bound.

To recover a mechanically checked exact-six control on 14 vertices:

```sh
/tmp/q9_windows_replay 3 0 1 13 6 < control14.txt
```

The unrestricted small-neighborhood program takes maximum deleted vertices, first row, exclusive end row and target edge count. The global exact-six SAT replay requires Python-SAT. For example:

```sh
python search.py walks.txt results-replay.jsonl 6 12000 0 340 --native
```
