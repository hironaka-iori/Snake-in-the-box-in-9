# Globally placed insertions and reconstruction of four coordinates in Q9

The two source banks are q9_gap_generations/prior191.words (131 paths) and prior190.words (1,042 paths). verify.py independently tests all vertex pairs in every source path. Each SAT instance keeps the ordered projection onto five coordinates and reconstructs the other four bits at all 193 target vertex times. A 191-edge source receives one extra transition and a 190-edge source receives two. All insertion positions are free, including consecutive insertions and both ends of the word.

For an inserted transition there are six possible projection types: no change of visible bits (allow any of the four hidden directions), or one of the five visible directions. In the sampled batch the type or ordered pair of types is specified per instance. Additional covered batches enumerate every one of the 6 or 36 types for each chosen source/axes pair. Together the corresponding SAT cases cover arbitrary insertion directions for those pairs.

At time t, an alignment state k records how many inserted steps have occurred. It starts at zero, ends at the number required, and can stay constant or increase by one on each step. The visible vertex is the seed vertex at time t-k with the first k inserted visible directions XORed into it. One-hot target-vertex variables select a compatible hidden colour and alignment, enforce cube adjacency between consecutive times, and forbid repeated vertices or chords. The model includes all 192 single insertion positions or all 18,336 ordered-by-time choices of two positions. These position counts describe the scope of a single SAT instance and count equivalent paths more than once. The translation symmetry of the four hidden coordinates fixes their starting colour to zero.

For positive controls, deletions in known 191-edge paths give clean 190- and 189-edge sources. No known witness or insertion positions are supplied as solver phases. The recovered single insertion was at position 4 instead of the planted 3. A planted double deletion at positions 0 and 3 was repaired by insertions at 3 and 4. A mixed hidden/visible two-insertion control was repaired at its original pair of positions. All indices are zero-based output transition indices. The alternate verifier reconstructs the visible trajectory and invokes a separate fixed-time hidden-colour SAT formulation on all three returned insertion-site assignments. It also enumerates every one of the 192 positions for two negative single-insertion examples and independently checks 128 site pairs for each of four negative two-insertion examples. Four sampled global-slot instances additionally include compressed Glucose DRAT traces independently validated by drat-trim and replayed from disk. The other negative cases have solver statuses only. The certificate log includes the row, axes, extra types and SHA-256 of the regenerated CNF.

Run from this directory with Python and python-sat with CaDiCaL 1.9.5:

```sh
python -B search.py control > controls.jsonl
python -B search.py 191 120 39113 2400 > run191_39113.jsonl
python -B search.py 191 64 81041 8000 > run191_81041.jsonl
python -B search.py 190 96 7919 2400 > run190_7919.jsonl
python -B search.py 190 48 62901 7000 > run190_62901.jsonl
python -B retry.py 190 42000 > retry190.jsonl
python -B retry.py 191 42000 > retry191.jsonl
python -B all_directions.py 191 20 113927 > all191_113927.jsonl
python -B all_directions.py 190 4 286031 > all190_286031.jsonl
python -B all_directions.py 190 4 91849 > all190_91849.jsonl
python -B verify.py > verified.jsonl
python -B summary.py > summary.json
```

To replay the four saved DRAT traces from this directory, run `python -B certify.py /path/to/drat-trim --replay`.

## Results

All 736 source-row/hidden-axis/insertion-type configurations returned UNSAT. There were 304 single-insertion configurations from 191-edge sources and 432 double-insertion configurations from 190-edge sources. The complete-direction subset contains 20 source/hidden-axis pairs at length 191 and 8 pairs at length 190. No instance remained unresolved after the configured retries. Distinct configuration keys can describe equivalent paths. These experiments do not determine the Q9 optimum.
