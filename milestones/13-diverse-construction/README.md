# Diverse walks and solver-guided repair

Checkpoint: 18 October 2026. Target: construct a 196-edge snake. No valid
improvement over 191 edges was found. This continues milestone 12 without
undertaking the collaborators' upper-bound work.

## Equal-budget comparison

The population variant retains up to 32 equal-best-score walks, deduplicated
under translation, coordinate permutation, and reversal. The comparison mode
retains only the first walk attaining each new best score. Both use the same
move types, annealing schedule, and proposal budgets. Population sampling
changes the random trajectory, so these are matched seeds rather than identical
trajectories. An exact proposal limit avoids conflating search quality with
output speed. The original milestone 12 sources and records remain unchanged.

| Seed | Capacity | Score after 10 million proposals | Score after 100 million proposals |
|---|---:|---:|---:|
| 41 | 1 | 8 | 6 |
| 41 | 32 | 6 | 6 |
| 113 | 1 | 9 | 6 |
| 113 | 32 | 7 | 7 |

The shorter runs initially favored the population variant; the longer runs do
not establish a consistent benefit. All saved best walks have distinct vertices,
so their scores count forbidden chords. Every run's longest reported valid
segment has 191 edges. The larger archive ultimately held only two best-score
classes in each long run. The current-score archive is cleared on improvement;
its final size does not measure diversity over the entire run.

The eight runs used 440 million proposals in total. An additional 10,000-proposal
audit independently recounted every evaluated move (8,524 checks). Assertions
and periodic quadratic checks remained enabled in the other runs. All final
walks and retained pool members passed a separate Python pair-count audit.
The mathematical acceptance rule remains the Lean-checked zero-defect
equivalence from milestone 12. No new Lean verification of the search program
is claimed.

## Structural diagnosis

In all four long runs, the saved best walk's first 192 vertices form a published
191-edge bank path up to the stated symmetries. The corresponding bank indices
are 16, 43, 19, and 45 in table order. Every forbidden chord in these four saved
best walks touches one of the final five vertices. The other two retained
population members have internal chords and do not furnish new 191-edge prefixes.

Thus these saved improvements still concentrate defects in the appended tail.
This observation concerns the saved states, not every state visited by the
search. It gives a concrete reason to try constructions that do not start by
appending to a bank path. The score of six is not a statement that six edits
suffice to obtain a snake.

## Solver-guided repair

For two six-chord walks, an exact small branching calculation finds a minimum
set of walk positions meeting every chord. Removing these positions gives an
initial fixed vertex set. Selected vertices in that set become assumptions in
the induced-path model; their order and endpoint roles are unrestricted.

After a solver INFEASIBLE result, the solver returns a sufficient conflicting
subset of these assumptions. The block policy releases a vertex from that
subset and its nearby positions along the original walk. The scattered policy
releases up to five vertices from the subset. Every relaxation is recorded.
Neither policy claims to find minimum conflicting sets. The initial chord-cover
cardinality was checked independently by enumerating all smaller covers.

| Source | Policy | Initial fixed vertices | Infeasible rounds | Final fixed vertices | Final status |
|---|---|---:|---:|---:|---|
| Seed 41, capacity 32 | Block | 192 | 17 | 140 | UNKNOWN |
| Seed 41, capacity 32 | Scattered | 192 | 19 | 97 | UNKNOWN |
| Seed 113, capacity 1 | Block | 194 | 20 | 131 | UNKNOWN |
| Seed 113, capacity 1 | Scattered | 194 | 22 | 84 | UNKNOWN |

Each run had a 60-second overall budget, a 10-second per-round budget, and one
solver worker. A run stops at its first unresolved round. The policies therefore
finish with different constraints; their final counts are not a ranking of
search quality. The infeasible rounds and assumption cores are unverified
solver evidence about restricted families, not Lean certificates or global
exclusions. A control fixing the known 191-edge path succeeded, and all 18,336
unordered pairs of its returned witness passed independent checks.

`data/verification.json` checks all saved scores, pool keys, minimum chord
covers, monotone relaxations, and the control witness. It records LF-normalized
source hashes. It does not certify solver impossibility results.

## Reproduction and next experiment

Use the Lean, Python, and OR-Tools versions recorded in milestone 12. Build
`scripts/population_search.cpp` with a C++17 compiler, optimization, and assertions
enabled. This run used MSVC 19.44 with `/O2 /EHsc /std:c++17`. Create `build/`
and generate the bank input as described in milestone 12. From the repository root:

```sh
milestones/13-diverse-construction/build/population_search --input milestones/12-construction-196/data/bank-input.txt --target 196 --seed 41 --seed-index 41 --capacity 32 --proposals 100000000 --seconds 240 --output milestones/13-diverse-construction/data/new-population.json
python milestones/13-diverse-construction/scripts/core_repair.py --source milestones/13-diverse-construction/data/new-population.json --policy block --output milestones/13-diverse-construction/data/new-repair.json
python milestones/13-diverse-construction/scripts/verify_experiments.py
```

On Windows the executable has the `.exe` suffix. Use new output names. C++
random distributions and parallel machine load can affect cross-platform
reproduction; saved vertex sequences provide independently checkable evidence.

The next method should relax connectivity instead of inducedness: select 197
vertices with exactly two degree-one vertices and all other selected vertices
of degree two, then remove cyclic components through explicit cycle cuts until
a single path is obtained. This allows several components to change together
and avoids freezing a long prefix. It is a proposed constructive search, not
an existence assertion. The repository's existing general Lean cycle-exclusion
theorem supplies the mathematical justification for cycle cuts; the new solver
encoding and each produced witness will still need separate checks.
