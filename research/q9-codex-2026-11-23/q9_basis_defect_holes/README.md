# Q9 near-path defects under a free binary basis

All lengths count edges. Input vertex identifiers are integers from 0 through 511. A free basis consists of nine linearly independent nonzero 9-bit vectors. A translation of the input vertex set has no effect on completion existence. Each basis is searched as an unordered set of generators.

The principal corpus has five simple 192-step walks with one chord from the Q8 single-cross corpus and seven simple 192-step walks with two chords from the monotone Q8-derived corpus. The larger registered corpus includes the principal twelve and has 800 one-chord and 1,571 two-chord canonical walks. Canonicity here means renaming standard axes by order of appearance and reversing the walk. The registration does not claim inequivalence under all affine changes of basis. Source rows and zero-based walk indices are stored in `source_seeds.json`. Use the canonical transition word as the join key.

For an input near-walk, the deleted indices must meet every original nonconsecutive distance-one pair. This is a restriction on the tested family, since changing the basis can also remove a chord directly. Within a retained set, the solver permits every basis and all 512 choices of position for each new point. A freshly added point may equal a deleted one. The following files describe overlapping families.

* `primary.jobs/results` and `neighbors.jobs/results` cover the twelve principal walks for all one-, two- and three-point hole sets drawn from the chord endpoints, their walk-index neighborhoods of radius two, and the two ends of the walk.
* `endpoints.jsonl` and `unmasked_endpoints.log` cover all 14,581 chord-endpoint-only configurations from the larger registered corpus. `registered.jobs/results` repeats 200 selected cases from the larger corpus with the parity-form solver. Some of these 200 use additional neighboring positions.
* `broader.map` and `broader.results` cover every one- and two-point chord cover of the twelve walks. Three-point configurations include all supersets of a minimal two-point cover, plus triples containing a minimal singleton cover and at least one other deleted position within walk-index distance two of a chord tip or equal to an endpoint. The map columns are seed ID and deleted walk indices. The independent audit regenerates the expected sets.
* `minimal.jobs` and `minimal.txt` represent the 24 minimal covers of these twelve walks. `joint.results` searches each retained set with a total of three replacements, allowing every remaining deletion to occur anywhere in the set. `joint_first2.log` replays the first two rows at a higher budget. Row numbers in the combined summary refer to `minimal.jobs`. A closed singleton-cover row applies to all pairs of further deletions, with no locality condition. By set containment, even a deletion set missing the designated cover is excluded if the union of that deletion set and the cover has size at most three. Thus a closed singleton-cover row excludes all unrestricted deletions of at most two points in that mother, and a closed two-point-cover row excludes every single deletion.
* `joint_shared_fast.log` is an auxiliary low-budget run on the last seven rows of `minimal.txt`. `early.results` and `early_hard.log` are a secondary first-violation search, with explicit UNKNOWN for a reached budget.

## Reproduction

Run the following commands in this directory. C++ sources depend on the sibling directory `../q9_change_basis`.

```sh
c++ -O3 -std=c++17 joint.cpp -o joint
c++ -O3 -std=c++17 early.cpp -o early
c++ -O3 -std=c++17 unmasked.cpp -o unmasked
python3 prep.py
python3 jobs.py
python3 minimal.py
python3 run.py controls 80000
python3 run.py primary 80000
python3 run.py neighbors 100000
python3 run.py registered 65000
./unmasked 192 1700000 < endpoints.txt > unmasked_endpoints.log
python3 broader.py
./joint 192 600000 3 < minimal.txt > joint.results
head -2 minimal.txt | ./joint 192 4000000 3 > joint_first2.log
python3 check_joint.py
./early 191 4500000 2 < joint_control2.txt > early_control2.log
./early 191 4500000 3 < joint_control3.txt > early_control3.log
python3 symmetry.py
python3 audit.py
```

The general joint interface is `./joint TARGET NODE_LIMIT NUMBER_ADDED`. Each stdin line begins with `points` followed by the distinct input vertex IDs. The solver discards exactly `NUMBER_ADDED + input_size - TARGET - 1` original points. A real 191-edge mother has 192 points, so `./joint 192 600000 2` deletes one and adds two and `./joint 192 600000 3` deletes two and adds three. A geometric hit prints its basis, ordered coordinates in that basis, and original vertex IDs discarded under `EXTRA`. A search continues to the next input after CLOSED or UNKNOWN and exits at the first FOUND. The per-row index starts at zero for each invocation.

If a completion has target length T and h added vertices, the retained forest has between T−2h and T−h induced edges. Deleting t further vertices can remove at most 9t edges before reaching this interval. The joint search enumerates independent generator sets meeting those necessary bounds. Every degree-three obstruction supplies four alternatives, consisting of its center and three neighbors. Each retained vertex must eventually have degree at most two. At a complete basis, the solver tests permitted deletion sets, verifies that the retained components are paths, then grows or merges components until the required vertices have been added. CLOSED means this finite family finished in this solver. UNKNOWN means its configured node cap was exceeded. These logs are computational results, without a formal proof certificate.

The six blind positive controls scramble previously validated 191-edge paths by non-coordinate affine maps, shuffle their retained point order and remove one to three points. Both the parity-form and unmasked solvers return full 191-edge paths. For the joint controls the input also includes one or two extraneous points which are removed by the returned witnesses. The audit checks all vertex pairs and maps every retained point back through the returned basis. Six affine-negative controls compare every eligible parity mask and number of complete basis tests after the contragredient relabeling.
