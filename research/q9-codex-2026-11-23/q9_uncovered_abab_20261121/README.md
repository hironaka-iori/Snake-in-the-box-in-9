# Four reordered fragments from the 22 uncovered Q9 records

The two coverage files used by q9_uncovered_endpoint_relocation.py identify archive rows 19,20,21,22,51,52,63,64,65,66,81,82,83,84,92,93,108,109,110,111,115,126 (zero-based). prepare.py tries matching twelve-step intervals, in both orientations and up to coordinate permutation. It retains strong alignments and samples overlap bands with fixed seed 297694. The resulting 2,728 placements include all 231 distinct pairs of records. The poses are a sample of the cube isometries.

Starting in either record, search.cpp follows four oriented intervals in the order A,B,A,B. Every interval must contain a vertex absent from the other record. Each record must supply two separated intervals. At least one record must have its intervals traversed in an order incompatible with following its original trace in either direction. The search also permits growth at both ends in the full cube. Mode 0 uses three direct cube edges. Mode 1 permits an intermediate vertex outside both parents at each switch. Modes 2 and 3 require this at one or two distinct switches, respectively. Where both adjoining vertices are shared by the parents, a direct crossover is skipped. Endpoint growth starts at the fourth arc's last feasible vertex or sampled intermediate lengths divisible by four when above the specified threshold. Starting positions of the first arc are offsets 0,1,3,7,13,21,34,55 from either end. Other three interval starts are chosen by actual cube edges or bridges.

The largest direct run completed all 2,728 poses with zero segment or end-growth budget truncations under its restrictions. It made 337,506,056 interval-start calls and 281,079 end-growth queries. The tested four-arc prefixes had at least eight vertices per interval. The longest direct core and longest completed snake both had 191 edges. The one- and two-required-outside-bridge runs finished at 190 and 188 edges, respectively; 2,600 and 2,627 poses met their segment budget at least once. These results give no general upper bound.

The complete output across nine runs includes 291 independently verified 191-edge rows and 70 distinct classes, each found in the 131-class archive. The audit validates every stored candidate with all pairwise Hamming distances and checks pose coordinates, fragment membership, source indices, orientation, bridges and free ends. The separate positive replay on pose 1457 reconstructed 17 distinct archived classes, each different from the two input rows 63 and 93. One is row 35 and uses fourth-arc reconstruction plus 6 and 21 further edges at the two ends, including four vertices outside the union of the parents.

shorter.py compares the saved candidates with complete 189-, 190- and 191-step digit-token records in local .words and .words.gz files, also including their contiguous 189- and 190-step subpaths. Among the saved 570 classes of length 189, 16 are absent from this comparison. The 310 length-190 and 70 length-191 classes all match. The 16 candidates are in outside_wordbanks189.words. Other encodings or uncatalogued results may contain them. End growth to 192 failed for the 107 cores after total trim 12 and one square flip, the 200 cores after total trim 18, and the 96 cores after total trim 18 and two square flips.

Reproduce from this folder with a C++20 compiler and standard Python 3.

```sh
python3 -B prepare.py
clang++ -std=c++20 -O3 search.cpp -o search
./search poses.dat pilot.witness 550 145 8 0 0 47 0 > pilot.log
./search poses.dat direct.witness 850 179 8 0 0 1 0 > direct.log
./search poses.dat bridge.witness 350 177 9 0 1 3 0 > bridge.log
./search poses.dat deep.witness 12000 178 9 0 0 1 0 > deep.log
./search poses.dat bridges_all.witness 1300 174 8 0 1 1 0 > bridges_all.log
./search poses.dat recovered.witness 550 145 8 0 0 999999 1457 > recovered.log
./search poses.dat full_direct.witness 1500000 170 8 0 0 1 0 > full_direct.log
./search poses.dat outside_one.witness 3600 166 8 0 2 1 0 > outside_one.log
./search poses.dat outside_two.witness 2400 165 8 0 3 1 0 > outside_two.log
python3 -B audit.py pilot direct bridge deep bridges_all recovered full_direct outside_one outside_two
python3 -B shorter.py pilot direct bridge deep bridges_all recovered full_direct outside_one outside_two
clang++ -std=c++20 -O3 ../q9_catalogue_tip_core.cpp -o tip
Q9_CORE_FLIP=1 ./tip 192 12 outside_wordbanks189.words
./tip 192 18 outside_wordbanks189.words
Q9_CORE_FLIP=2 ./tip 192 18 outside_wordbanks189.words
```
