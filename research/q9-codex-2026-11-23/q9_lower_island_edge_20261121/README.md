# One complete Q8 path and one isolated lower edge

The lower layer consists exactly of the given mother path and an additional edge whose two vertices have distance at least two from every mother vertex. Both components need a vertical crossing. Crossing both ends of the additional edge forces all four points of a coordinate square and hence an induced 4-cycle. A connected induced open path cannot contain this square. All possible layouts therefore have two or three crossings. With three, the long mother crosses at both ends, one end of the extra edge crosses, one global endpoint is the other end of the edge, and the other global endpoint lies upstairs.

## Geometry and constructions

We canonicalize complete input arms by translation, coordinate permutation and reversal. In the rooted-arm file, the 95-, 94-, and 93-edge classes permitting the additional edge number 2, 47 and 382. They give 2, 59 and 550 canonical mother/edge pairs. The second source is all 753 words in q8_catalogue_96_98.words, with a total of zero to three steps removed from the two ends and a minimum length of 93. It contributes another 2 and 964 placements of lengths 94 and 93. The overall 1,577 pairs have independent enumerations in prepare.py and check.py. Canonicalization is relative to the mother; specific edge placements sharing a mother are retained.

The direct catalogue matcher takes rooted upper paths from both sources, independently renames their eight coordinates, and tests intersection with the fixed lower layer. The 1,577-case complete run covers every rooted prefix of lengths 92 through 98 that occurs in the two source files in either direction, every choice of which end of each lower component crosses, and all 40,320 coordinate permutations. The full upper bridge must join the two specified portals. A free third arm may grow if the other mother endpoint can cross. There were 22,444,121,088 mask tests, six placements of a bridge, two 189-edge snakes, and four 191-edge snakes. None of the six accepted a third arm. There is no unrestricted-upper completeness claim for this matcher.

A separate construction searches over template prefixes, arbitrary short cube bridges and fresh tails. A second free upper search picks several short bridges and grows the terminal arm by a beam in its available connected component, with no upper reference path. It visited all 1,577 placements at width 35. Selected placements were revisited at widths 45 and 550. Exact depth-first end regrowth released up to 69 edges on ten high-scoring completions. Exchanging the resulting long upper arms and regrowing from both free ends gave three-crossing 184-edge paths for cases 1249 and 1250. All saved candidates are checked by testing every pair of vertices as well as the exact set of lower vertices and the portals.

Of the 131 archived 191-edge classes, four admit this exact layer decomposition. Cases 1249, 1250, 1251 and 1252 match zero-based archive rows 118, 104, 128 and 103, respectively. All four use two crossings. The matcher rediscovered each 191 witness from the upper catalogue alone. Separately, occupancy SAT recovered 191 at all four after deleting every other upper point from the phase hint and fixing approximately every sixth upper point. The 130 unrestricted-upper SAT attempts at 192 were conflict-limited. Tight local SAT experiments on the four 191 seeds and the two 189 seeds are summarized in verified.json.

## Conditional certificates

Each exact lower geometry has four endpoint-colour-compatible 192-edge port assignments. Enumerating the degree-one vertices of the lower graph gives the same four branches independently. For each branch the fixed lower endpoint colours determine the required upper endpoint counts and colour balance. certs.py stores a nonnegative-support maximum bound via signed integer local prices; verify_q9_intact98_all_crossings.integer_bound independently recomputes the upper envelope. A root numerator below 1,930,000 at scale 10,000 excludes the 193-vertex target. These bounds have the endpoint colour counts required by the even-length target. In particular the four observed 191-edge solutions use different endpoint-colour requirements.

The eight root bounds for the two 95-edge mothers and the sixteen root bounds for the four actual 191 placements all exclude the 192 target. All 61 placements from the 49 eligible 94-edge mother classes also exclude 192. Of their 244 branches, 10 close at the original integer root, 95 close by a fully replayed table tree and 139 close at a tighter integer root. The largest refined root numerator was 1,922,020. The original open trees are kept compressed alongside the original and refined price certificates. bounds_summary.json lists every geometry and all coverage counts. The tree's local full assignments also undergo physical graph checks. These certificates concern the exact layer occupancy and target length.

## Reproduce

Use the workspace root as the parent of this directory. Run these commands here. Python 3 with its standard library suffices for data preparation and independent geometric checks. The optional occupancy experiments require python-sat; price generation requires SciPy and uses the existing tree and replay binaries in the workspace. Computation was local.

```sh
python3 -B prepare.py
python3 -B controls.py
python3 -B archive_subpaths.py
python3 -B run_inputs.py banks
clang++ -O3 -std=c++20 catalogue.cpp -o catalogue
clang++ -O3 -std=c++20 construct.cpp -o construct
clang++ -O3 -std=c++20 tail.cpp -o tail
clang++ -O3 -std=c++20 freebeam.cpp -o freebeam
clang++ -O3 -std=c++20 regrow.cpp -o regrow
./catalogue both.words cases.dat allmatch.paths 92 1 0 0 6000 1577
./catalogue both.words cases.dat controlmatch.paths 90 1 0 1249 3000 1253
./catalogue both.words cases.dat rootmatch.paths 85 1 1 0 6000 63
./construct both.words cases.dat wide.paths 12500 50 90 1577 1
python3 -B run_inputs.py high
./freebeam cases.dat high.ids beam.paths 45 2
./freebeam cases.dat all.ids beam_all.paths 35 1
python3 -B run_inputs.py deeper
./freebeam cases.dat deeper.ids beam_deep.paths 550 5
./regrow beam_deep.paths regrow.paths 125000 176
python3 -B run_inputs.py upper
./tail regrown_upper.words cases.dat mixedupper95.paths 55 1 0 2
./tail regrown_upper.words cases.dat mixedupper191.paths 65 1 1249 1253
python3 -B sat.py 6500 65 192 mini > sat192.jsonl
python3 -B local.py positive > positive.jsonl
python3 -B local.py scores > local_scores.jsonl
python3 -B local.py search > local_full192.jsonl
python3 -B local.py extra_search > extra192.jsonl
python3 -B local.py extra_scores > extra_scores.jsonl
python3 -B check.py
python3 -B certs.py 0 2 > certs.log
python3 -B certs.py 1249 1253 > controls_bounds.log
python3 -B certs.py 2 32 4 > bounds94a.log
python3 -B certs.py 32 63 4 > bounds94b.log
python3 -B tighten.py 1 4
python3 -B archive_trees.py
python3 -B check_bounds.py --trees
```
