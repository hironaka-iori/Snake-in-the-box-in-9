# Round 218 saved partner-model and result review

Result: PASS_SAVED_MODEL_AND_RECORD_AUDIT. The read-only audit ran after session 99902 was confirmed terminal. It parsed the exported protobuf files through the generated message definitions directly, without loading the OR-Tools initializer, CP-SAT solver, NumPy or Pandas. No solver, compiler, software tests or proof replay ran.

## Verified outcomes

Both 240-second retry queries ended UNKNOWN. Each recorded exactly one solver iteration, with no feasible relaxation selection and no dynamically added cycle cut. No rooted component was available to validate or retain as a warm start. No 93-edge partner or 192-edge Q9 construction was found, and neither fixed-root query was excluded.

| Root | Allowed vertices | Boolean variables | Initial/final constraints | Initial cycle cuts | Solver seconds | Peak private bytes |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 158 | 237 | 520 | 279 | 240.042279 | 73,646,080 |
| 78 | 158 | 237 | 515 | 274 | 240.002094 | 73,531,392 |

The retry solver total is 480.044374 seconds, excluding the original failed attempt. Both retry executions have exit 0, no resource stop and pinned result hashes. Wrapper wall times are 247.000 seconds for root 0 and 241.313 seconds for root 78. Minimum sampled free memory is 2,098,442,240 bytes and 2,335,391,744 bytes respectively. The four thread settings recorded by the wrapper are all 1.

## Model reconstruction

Reconstructed each allowed graph directly from the 99-vertex parent in Q8. Each graph has 158 allowed vertices, comprising 79 even and 79 odd vertices. The parent itself passes the complete induced-path and distinctness check. Each root is one of its two even endpoints, and the allowed set excludes exactly the other 98 parent vertices.

Verified every static cut: distinct allowed vertices, correct length, connectedness and induced degree two. Root 0 has 156 squares and 123 six-cycles; root 78 has 154 squares and 120 six-cycles. There are no duplicated cut sets.

For both initial and final protobuf exports, independently checked all 237 variable names and Boolean domains, and every linear constraint, coefficient, bound and enforcement literal in exact constraint order. The exports consist of 158 selection variables and 79 endpoint variables. The 241 base constraints express the selected root, 47 vertices of each parity, exactly one selected odd endpoint, root degree one, and the selected-only degree equations for all other vertices. The remaining constraints are exactly the listed initial cycle cuts. No additional objective, assumption, replacement condition, symmetry restriction, auxiliary variable or unlisted constraint appears.

Both final models are byte-identical to their respective initial models, consistent with zero feasible iterations and zero dynamic cuts. Model-description vertices, endpoint choices, cut lists, empty restriction lists and all input/model hashes agree with the source and result records.

## Native records and preserved failure

Verified script/input pins, execution-receipt hashes, stdout/stderr hashes, commands, output-directory arguments, thread environment, recorded resource gates, result hashes and the batch ledger. Result status, target length, time limit, iteration numbering and solver counters agree. No terminal receipt is missing for either root. All selected-path and joined-path fields are null, matching the absence of a feasible selection.

The first root 0 attempt is kept separately: INTERRUPTED/MEMORY_LIMIT, exit 1, 2.734 wall seconds and sampled peak private memory 590,295,040 bytes. Its stdout and stderr are empty; it has no model or result artifact. The archived original script snapshots match that attempt's pins exactly. This failed attempt is excluded from all retry iteration, cut and solver-time totals. The data establish no precise cause for the original memory growth.

## Reviewed next step: explicit linear degree bounds

For a nonroot vertex, let \(x,e\in\{0,1\}\) indicate selection and endpoint status, let \(s\) be its selected-neighbour count, and let \(d\) be its available degree. Under \(e\le x\) and \(0\le s\le d\), the conditional equation \(x=1\Rightarrow s=2-e\) is equivalent to

\[
2x-e\le s\le d-(d-2)x-e.
\]

If \(x=0\), then \(e=0\), and these inequalities reduce to the already assumed bounds \(0\le s\le d\). If \(x=1\), both bounds equal \(2-e\), giving the conditional equation. At the chosen root, retain the separate equation \(s=1\).

The coefficient \(d-2\) uses signed integer or real arithmetic. This qualification matters for vertices with degree below two; truncated natural-number subtraction would change the expression. Relaxing the indicators to \([0,1]\) gives valid necessary linear inequalities. Equivalence to a conditional equation is asserted only for Boolean indicators. No LP run or improvement in relaxation/search strength has been established.

## Scope

This audit verifies the complete saved Boolean model formula and the terminal native records. UNKNOWN gives no exclusion and no new bound. The generic cycle theorem does not by itself certify the Python encoding, solver execution or a global search over parents. No solver infeasibility certificate was produced. Further work can use the reviewed linear reformulation, while retaining the fixed-parent and fixed-root scope of these two queries.

## Evidence pins

- Root 0 initial/final model: `939b9b757bc71eafe736bb74197e8043c4892b0c4a8b0df2ddef3dfff6c7957f`
- Root 0 result: `2a684927082b696f98d3fed61a9578e7e9c1a2d9ee0612d0bcd914f956a78e86`
- Root 0 execution receipt: `479018d3cbeb4b40ff7770278e41873571a8fb2a03451713868173b6ccadf3c1`
- Root 78 initial/final model: `d66e3eac8ef583819515928f352e62d9282397efc6f296b00af82c21656a5c48`
- Root 78 result: `ebcbc3b34db486b3835465757fe6a5d201ce223bf4c8c7ee3694e586d6d3d989`
- Root 78 execution receipt: `9686595b8bb7440294066dc8cd15f7db67795c84a6b400cb51ff4046f1539102`
- `scripts/audit_partner_results.py`: `e4e6ee3c455cf518501bad7c961788139ad56ec46eb759cc569d79426e480723`
- `scripts/partner_search.py`: `cebcf267fe2ba1ae2d19bfb917246e296221b0e3f719500b7e2e42c7190b45c5`
- `scripts/run_partner.py`: `107140d550ed4ec8706d64f324fdda888f7e8bf834db396e2e428baa930aca97`
- `scripts/native_resources.py`: `2e9e7d499ef7068d10d7ca7e31c9a9dc7ef19abb72b0396d3eab9824376b4413`
- `data/seed98.json`: `2b328e537867b097316150be170a9af68e5af492bc7667d3b781b77d39e4e2f5`
- `data/complement-graph.json`: `6af4976a40d897be2c43790c75b66fac0473f0a97226d3fdb106140744a94c82`
- `data/threads1/batch-progress.json`: `b05fb6bbb81a8bad86d30ea1e9fc1876a54391d4b197e0ac5001f40120db3936`
- `logs/partner-model-review.md`: `83a8d6b3c44e22806fecb8445a26c6d1d40a1abda7739c028d744c9b9ee79d33`
- `data/partner-audit.json`: `922632ea9fe4b75b36b42736c72da56e8baa452936895997a84d85bfb29f9bb0`
