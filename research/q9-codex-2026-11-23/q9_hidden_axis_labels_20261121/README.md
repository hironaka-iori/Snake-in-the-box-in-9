# Four or five free Q9 coordinates along fixed visible trajectories

The input is the 5,062 distinct 192-step transition words in q9_three_axis.in. For each instance choose d=4 or 5 hidden axes, delete those coordinate bits at every one of the 193 vertex times, and seek a new assignment of all hidden coordinates. The complete specified visible trajectory is held fixed; the identity of each hidden transition is free. The samples favour many hidden transitions or few distinct contact constraints per pair of hidden states. “Loose” refers only to those measured quantities. There is no claim that the sample is statistically representative.

## Model and controls

A hidden state is constant through each visible transition and moves one hypercube step through each hidden transition. The new SAT formulation represents each state with d bits and a parity-compatible colour. A one-hot step label selects the changed bit; first occurrences of labels are ordered to remove coordinate-permutation symmetry. A nonconsecutive pair of times creates a constraint only when visible distance is 0 or 1. For equal hidden parity, this forbids equal hidden colours. For opposite parity, visible distance 0 forbids neighbouring hidden colours; visible distance 1 already gives total distance at least 2. Several contacts on one hidden-state pair share the constraint. Complete models are reconstructed and checked by pairwise distance.

The previous 4,000 four-axis and 8,000 five-axis selections from q9_threechord_one_paths.txt were reproduced in their original shuffled order, including template deduplication, and were excluded. A template records the time of every hidden transition and the visible transition word, identifying visible axis relabelling and reversal. All final results are deduplicated with this rule. The independent replay uses the older repair_q9_time_projection.py parity-domain CNF on every distinct new target. The two implementations encode hidden states and unit transitions differently, but both call CaDiCaL 1.9.5. UNSAT outcomes are solver reports without retained proof traces.

Positive controls start from the same deliberately damaged 191-edge walk. Both formulations recover a valid induced path at each dimension, and independent pairwise checks verify the recovered length, edge distances, and all nonconsecutive distances.

## Reproduction

Run in this directory with Python, python-sat and CaDiCaL 1.9.5.

```sh
python -B search.py 4 1 5099 50000 --control > control4.json
python -B search.py 5 1 5099 60000 --control > control5.json
python -B search.py 4 128 99109 6500 > d4_99109.jsonl
python -B search.py 4 96 70189 16000 > d4_70189.jsonl
python -B search.py 5 64 117979 4500 > d5_117979.jsonl
python -B search.py 5 48 129193 12000 > d5_129193.jsonl
python -B check.py 4 16000 > independent4.jsonl
python -B check.py 5 16000 > independent5.jsonl
python -B deep.py > deep5.jsonl
python -B remaining.py > remaining5.jsonl
python -B summarize.py > summary.json
```

## Results

None of the 335 distinct new templates admitted a 192-edge witness according to the solver runs. Both encodings returned UNSAT for all 223 distinct four-hidden-axis templates (115–145 free transitions). All 112 five-hidden-axis templates (141–171 free transitions) returned UNSAT in at least one run. The independent formulation resolved 32 of the five-axis cases at its budget. After the 100,000-conflict repeat resolved 23 additional cases, all final 26 returned UNSAT at 250,000 conflicts. The shared 191-edge positive control was independently recovered in each dimension. This conclusion concerns only these sampled visible trajectories. See summary.json for the stage-by-stage counts.
