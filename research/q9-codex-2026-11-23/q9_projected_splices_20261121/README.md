# Editing Q8 projections and relocating Q9 layer switches

Inputs are the 58 single-chord walks in q9_all_newsingle_hinge.vertices and 800 in q9_onechord_expanded_800.txt. The 858 rows have 193 distinct vertices, unit edge distances, and exactly one nonconsecutive pair at distance one. They are distinct up to cube isometry and reversal. Projection deletes one of the nine axes and contracts consecutive duplicate vertices. The 58 new inputs give 450 distinct canonical projected transition words; the 800 old ones give 5,801, counted separately.

The first family chooses a contiguous strictly interior interval, optionally reverses it, optionally swaps two coordinates, and translates the piece. Its ends must connect to the unchanged adjacent vertices. A projection eligible for a clean lift is simple: revisiting a column nonconsecutively puts two vertices in that column at distance zero or one. All nine projections are considered. The new-input identity run tests every internal interval length; the new-input transposition run uses lengths 2–100. Old-input runs use maximum lengths 32 and 28. In transposition runs, one axis pair is sampled per interval.

The second family cuts a projected subpath, keeps its endpoints, and replaces it by a simple Q8 detour. The fresh-input run uses gaps of 2–12 edges and replacement lengths between the original length minus two and the original length plus four, with the required parity. The floor is one edge. For old inputs the maximum gap is 6, maximum increase 2. An outside-only necessary condition rejects label contradictions before enumeration. For every candidate considered, the existing exact two-layer lift routine optimizes switch number and placement over the prescribed projected order. Thus editing the horizontal step count can shift how many cross-layer steps the target requires.

| Input | Simple interval edits | Detours evaluated | Detour gaps capped | Longest witness at or above 191 |
|---|---:|---:|---:|---|
| 58 new | 509,676 | 20,510,518 | 46,732 | None |
| 800 old | 5,189,887 | 14,045,921 | 104,034 | 191 |

The target length is 192. The searches reported no such path, and all 191-edge witnesses constructed on old inputs belonged to the known 131-class reference. The four interval runs and two detour runs total 40,256,002 edited candidate evaluations, with possible repetitions. Original unedited projections are also evaluated by the first family and are excluded from that count. The reference comparison concerns constructed witnesses; the SAT verifier below does not independently repeat every failed candidate.

For each positive control, damage a projection of a known induced 191-edge path until its projected trace cannot realize 191. In the first control the repaired interval is reversed and translated. In the second, a two-step projected subpath is replaced by a four-step subpath. An independent CaDiCaL model represents the entry layer at each column, forbids consecutive switches, constrains nonlocal adjacent columns to opposite layers, and enforces the requested number of switches. It establishes the damaged inputs are UNSAT at 191 and the repaired inputs are SAT. The independent Python checker also verifies every logged witness by pairwise Hamming distances and reconstructs its projected edit.

Run from the parent workspace, with the system macOS clang++/libc++ and a Python environment with python-sat/CaDiCaL:

```sh
clang++ -O3 -std=c++20 q9_projected_splices_20261121/search.cpp -o /tmp/q9-splice
clang++ -O3 -std=c++20 q9_projected_splices_20261121/detour.cpp -o /tmp/q9-detour
clang++ -O3 -std=c++20 q9_projected_splices_20261121/detour_control.cpp -o /tmp/q9-detour-control
head -1 q9_elastic_blocks_20261121/parents191.vertices | /tmp/q9-splice 18 0 191 1963 1 plant
head -1 q9_elastic_blocks_20261121/parents191.vertices | /tmp/q9-detour-control
/tmp/q9-splice 192 0 192 2411 58 seed < q9_all_newsingle_hinge.vertices
/tmp/q9-splice 100 1 192 3719 58 seed < q9_all_newsingle_hinge.vertices
/tmp/q9-splice 32 0 192 199391 800 seed < q9_onechord_expanded_800.txt
/tmp/q9-splice 28 1 192 78173 800 seed < q9_onechord_expanded_800.txt
/tmp/q9-detour 58 12 4 400 142751 < q9_all_newsingle_hinge.vertices
/tmp/q9-detour 800 6 2 80 137091 < q9_onechord_expanded_800.txt
python -B q9_projected_splices_20261121/verify.py
```
