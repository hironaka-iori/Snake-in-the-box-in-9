# Repairing the entry-87 chord in the nine-cube

The source is the 88th record (zero-based index 87) in the [191-edge bank](../../milestones/204-cyclic-symmetry/data/bank9-input.json). Keep vertices 0 through 190. Append the last two source vertices translated by 16. The resulting ordered sequence has 193 vertices and one chord, between positions 7 and 192. The objective is to realize an induced 192-edge path while retaining selected coordinate histories. Coordinates and positions are zero-based.

## First six hours of research

Start 00:49 Singapore time on November 15, 2026. The initial six-hour window reaches 06:49. These are work periods, not completion predictions.

| Elapsed time | Work and deliverable |
|---|---|
| 0–1 hour | Pin the source and establish a sound projection model. Search all six-coordinate choices with a finite conflict budget. Extract checkable combinatorial obstructions. |
| 1–2 hours | Develop consequences of equality and near equality in the parity capacity bounds. Try to certify further triples or reduce their remaining domains. |
| 2–3 hours | Use opposite-parity adjacency and multiple retained slices together. Compare domain reductions on the first-priority model and the strongest near-saturated models. |
| 3–4 hours | Re-express the one-chord example as a cycle with an attached tail. Prove a recombination or endpoint-packing criterion and investigate constructions which preserve different data. |
| 4–5 hours | Apply the best deductions to selected open cases and independently audit any structural exclusion or 192-edge path. |
| 5–6 hours | Consolidate reproducible certificates and examine which arguments apply beyond entry 87. Publish substantial verified conclusions on the research branch. |

## A weighted obstruction from the retained traces

Let the free coordinates have dimension $d$, and write each vertex as $(z_i,u_i)$. On a step that changes $z_i$, the word $u_i$ must be constant. Group consecutive positions joined by such steps into intervals, and let $T_r$ be the set of retained words visited by interval (r). At each interval boundary exactly one free bit changes. Hence intervals of the same index parity use free words of one common parity. Each parity class has $2^{d-1}$ words, by toggling one coordinate.

**Lemma.** Two different intervals of the same parity can receive the same free word only if every pair of retained vertices from their two traces has Hamming distance at least two.

**Proof.** Their indices differ by at least two. An entire nonempty interval lies between them, so every pair of positions in the two intervals is nonconsecutive. If their free words agree, the distance between the full vertices equals the distance between their retained words. An induced path requires that distance to be at least two. ∎

**Weighted capacity theorem.** Give each trace type $T$ a nonnegative weight $w_T$. Suppose every family of mutually separated types has total weight at most one, where separated means minimum cross-distance at least two. In either interval parity, let $m_T$ be the number of occurrences of each type. Then any lift satisfies

$$
\sum_T m_T w_T \le 2^{d-1}.
$$

**Proof.** Group the intervals by their actual free word. By the lemma each group contains distinct, mutually separated types. Repeated copies of the same nonempty type cannot share a word. Each group contributes at most one, and at most $2^{d-1}$ groups are available. ∎

### A six-coordinate exclusion

**Theorem.** Entry 87's one-chord candidate has no induced 192-edge repair keeping coordinates {0, 1, 4} fixed at all 193 indices.

**Proof.** The remaining six coordinates provide 32 free words of each parity. There are 85 intervals. Among the 43 even intervals, take

```
0, 2, 4, 6, 10, 12, 14, 16, 18, 20, 22, 24, 28, 30, 32, 34, 36,
42, 44, 46, 48, 50, 56, 58, 60, 68, 70, 72, 74, 76, 80, 82, 84.
```

Every pair has intersecting or adjacent traces. For example, interval 0 visits retained words 0, 1, 17, 19 and 18, while interval 2 visits 2. The pair (18, 2) differs only in retained bit 4. [The witness generator](witnesses.py) supplies the actual two path positions for each of the 528 pairs. Thus 33 intervals require distinct words from one parity class of size 32. ∎

The theorem excludes one of the 84 possible retained triples for this specific indexed candidate. It is independent of the SAT run. In particular, retaining {0, 1, 4} here differs from the first-priority search, which retains {0, 2, 3}. The repository's round 212 concerns the separate 98-edge parent in dimension eight.

### Reproduction

The working input SHA-256 is `0b973ddcd371680ad4efe07c01008c29437280514926daf1a67d99b6ba510edb`. Run `python witnesses.py` inside this directory to regenerate the concrete certificate from the input. Run `python exact_cover.py --output color-duals.json` with Python 3.11, NumPy, SciPy and python-sat to find rational weighted obstructions for the 84 triples. After using numerical linear programming to suggest weights, the program checks every independent group and calculates the bound with exact rational arithmetic. The geometric exclusion above also has the explicit 33-interval proof.

For the bounded SAT screen, run `python solve.py --dimension 6 --budget 12000 --output six-screen.json`. An `OPEN` row exhausted the conflict budget. A positive row includes an explicit reconstructed path checked against every pair and against its fixed projection. The first-use coordinate normalization follows from renaming the free coordinates in order of first occurrence, after translating the first word to zero. Either operation preserves the projection and all Hamming distances.

Lean 4.19.0 accepted the pigeonhole argument, all 528 concrete conflict witnesses and the theorem ruling out a word assignment on the recorded intervals. Run `python replay.py --lean /path/to/lean` to regenerate and check all 36 modules. The generated source is reconstructed from the pinned bank. The Lean statement takes same-parity membership and the nonedge inequalities on the literal interval arrays as premises. The identification of those arrays and premises with any geometric lift is the written argument above, together with the generator's comparison to the input.
