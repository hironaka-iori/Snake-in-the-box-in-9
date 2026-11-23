# LP-initialized Q9 site swaps

The inputs are the first 52 complete rows of q9_facet_bank_primal.jsonl and the first 10 rows of q9_facet_191_donors_four.jsonl. The 62 distributions represent 31 distinct catalogue donors and both target endpoint colours. The two-colour occupation counts for a 192-edge goal are 97 and 96. A 191-edge control occupies 96 vertices of each colour. Every move replaces a selected free vertex by an unselected vertex of its colour. The unchanged central donor interval is compulsory. Vertices that cannot coexist with it by the degree constraint are omitted from the movable sites. The 512-vertex representation retains the full ambient Q9 adjacency.

Cold starts draw vertices without replacement separately by colour according to perturbed LP logits. For a trimmed donor, discarded donor vertices are scored as donor vertices and previously unpriced external vertices receive a fallback weight of 125 per thousand. Warm starts are genuine 191-edge paths with one added vertex of the required colour, chosen using degrees and LP scores. Mixed starts combine 77% reference membership and 23% LP occupation probability before sampling. On the five distinguished catalogue donors, signed-axis relabelling and reversal place five source words each, for 25 reference placements. Warm and mixed searches use releases of 0, 3, 8 and 14 vertices per donor end. Cold searches use 0, 4 and 10.

At each ordinary step the native solver scores every allowed one-site same-colour exchange by its resulting degree defects, using incremental degree differences. Among eight shortlisted exchanges it computes connected-component counts and cycle ranks exactly. Tabu penalties and LP tie-breaking diversify the moves. Every 83 steps, a one- to four-swap perturbation from the incumbent can escape the preceding basin. A zero score requires one connected acyclic component with correct degree and endpoint counts. Every zero-score path is reconstructed and checked pairwise immediately.

The 192-edge runs use 240 steps and one restart per input. The random seeds for cold, blend and warm runs are 8712, 49117 and 63411 respectively. The independent 191-edge controls start with one, three or five actual exchanges away from their witness. Only the mutated occupation set, its fixed donor interval, the allowed sites, colour and the LP vector are sent to the solver. They receive 120 steps and seed 43791. Input and output site masks, scores and budgets are archived for every run.

The 615 distinct incumbent-mask and fixed-anchor combinations receive complete native searches at exchange radius two. Every fifth combination is also searched at radius three. Twenty-four representatives are searched at radius four. After deleting at most k non-anchor sites, a valid completion must retain a linear forest with at most k+1 components. If a retained vertex has degree above two, at least it or one of its neighbours must be removed. The enumeration then tests all compatible additions from the original exterior with the required parity counts. The separate MiniCard connectivity model searches radius six at 5000 conflicts per incumbent and radius fifteen at 9000 conflicts on every fifth. Solver cutoffs are logged as unknown.

To run the independent check from the workspace root:

```sh
python3 -B q9_facet_occupancy_search_20261121/audit.py
```

The preparation and audit need only the standard library. The native tools build with C++20. The optional SAT experiment uses python-sat. summary.json includes all positive-control counts, the degree profile of the best 193-vertex sets, the search budgets, exact small-radius results, and the outcome of deleting one non-anchor vertex from the incumbents. No global upper bound follows from these sampling or neighbourhood runs.
