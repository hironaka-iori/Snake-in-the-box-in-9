# Chord-end window and freely placed distant window

The input is `q9_all_newsingle_hinge.vertices`. Its 58 symmetry classes are checked independently for distinct vertices, 192 proper edges and exactly one chord. For each end of that chord, remove a window centered on that endpoint, clipped to the walk. Remove a second window of the same nominal width at each possible start, requiring at least one intervening original vertex. Any retained component reduced to a singleton is also freed. The remaining islands keep their positions in the cube. Their order and directions are unrestricted. The path may also grow new terminal arms. The original chord ends remain interchangeable.

The port CSP in `search_q9_port_matching.cpp` searches all mutually compatible routes for the selected islands, including two free tips and any order that forms a single path. If m vertices are free, a bridge of m+1 edges and a terminal arm of m edges cover the full feasible lengths. Window configurations with identical islands are deduplicated within each seed. Overlap between the families for different windows and different seeds is possible. Solver and route caps are explicitly tracked. The 17-wide initially limited cases get a larger port budget. A separate CaDiCaL encoding on vertex selections handles the initial 17- and 23-wide port cutoffs, imposing degree, count and parity constraints, then excluding disconnected models. Its negative answers have no saved proof traces. Independently, all five-wide cases run through a C++ vertex-subset enumerator checking degrees and connectivity.

A deliberately damaged known 191-edge path supplies the control. After removing the assigned windows and shuffling the islands, the port solver recovers a true 191-edge path whose original retained pieces change order. The subset and SAT implementations independently recover solutions on the same fixed set. The Python verifier checks the resulting paths and recomputes each row's original window count and surviving fixed-set count.

Run in the workspace root with the local C++20 compiler. The SAT adapter uses the bundled CaDiCaL in the local Lean 4.19.0 installation. The main log reports are in `verification.log`.

```sh
d=q9_chord_remote_windows_20261121
b=q9_all_newsingle_hinge.vertices
clang++ -O3 -std=c++20 "$d/search.cpp" -o /tmp/q9_chord_remote_windows_20261121
clang++ -O3 -std=c++20 "$d/subset_check.cpp" -o /tmp/q9_chord_remote_subset_20261121
python3 "$d/control_input.py" | /tmp/q9_chord_remote_windows_20261121 2 5 100000 10000 1
python3 "$d/control_input.py" | /tmp/q9_chord_remote_subset_20261121 control
python3 "$d/sat_replay.py" control
/tmp/q9_chord_remote_windows_20261121 2 5 100000 10000 0 < "$b"
/tmp/q9_chord_remote_subset_20261121 < "$b"
/tmp/q9_chord_remote_windows_20261121 5 11 150000 12000 0 < "$b"
/tmp/q9_chord_remote_windows_20261121 8 17 100000 3500 0 < "$b"
/tmp/q9_chord_remote_windows_20261121 8 17 2000000 120000 0 "$d/width17.log" < "$b"
/tmp/q9_chord_remote_windows_20261121 11 23 60000 3000 0 < "$b"
python3 "$d/sat_replay.py" "$d/width17.log"
python3 "$d/sat_replay.py" "$d/width23.log"
python3 "$d/verify.py"
```


An additional vertex-selection SAT run requires *at least* 193 vertices, so it can produce a longer snake whose first 192 edges give the desired witness. Its released chord neighborhood has radius 13. It groups up to twelve consecutive possible starts of the distant 23-vertex window by releasing their union (up to 34 vertices). Every nominal 23-wide distant placement is contained in one enlarged release. Releasing additional vertices can only reduce the required fixed set, including when singleton residual components are freed. The grouped search includes overlapping releases. Its coverage and remaining limits are recorded in the verifier output. Reproduce with `python3 "$d/grouped_lower.py" control` and `python3 "$d/grouped_lower.py"`.

