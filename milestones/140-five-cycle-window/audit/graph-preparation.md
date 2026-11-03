# Preparation of the weak five-count exclusion experiment

Status: **PREPARED_NOT_EXECUTED_PROOF_REQUIRED**. The generator, generated evaluator, and preparation receipt are saved. Only preparation and small saved-row checks were run. No graph array was loaded; no graph evaluation, solver, or Lean compiler was run. No proof-completion record was created.

## Rule and implementation

The proposed ordinary exclusion has canonical six-direction word `012032` and internal count conditions

\[
(\alpha_1,\alpha_3,\alpha_5)=(3,4,3),\qquad
\alpha_2\le5,\quad\alpha_4\le5.
\]

The current exact `35453` certificate is not by itself the weak theorem required by this evaluator. Execution requires the later successful audit of the actual-snake theorem with the stated upper bounds.

The nine-direction graph row stores six count symbols at local vertices 3 through 8. Both available six-direction placements are checked:

| Placement | Direction slice | Count slice |
|---|---|---|
| 0 | `word[2:8]` | `digits[row,0:5]` |
| 1 | `word[3:9]` | `digits[row,1:6]` |

The primary mask checks both orientations, reversing the count slice with the direction slice. All five matching symbols must be below 6. Thus every matched count is exact; a clipped symbol 6 cannot satisfy any of these bounds. The two outer counts are 3, the middle count is 4, and the other two are at most 5.

The canonical shape and bound predicate are invariant under reversal. A separate mask uses reversal-independent shape recognition and the explicit chronological columns at both placements, then checks equality with the primary mask. Recognition overlap is combined by Boolean OR; it does not add weight or occurrence credit.

The prior suffix credit remains exactly \(83/3\), with allowance 24 and integer weights \(3w+83\mathbf 1\). Its exact-count guard, the shared maximum of earlier charges, both profiles, and the comparison formula are unchanged.

## Predecessor reconstruction and saved cycles

Before applying the new mask, the evaluator reproduces milestone139's exact removal set, retained-edge count, and both full retained-weight hashes. The existing earlier reconstruction checks remain in place. The new deletion is applied only after this predecessor comparison.

The saved milestone139 completed five-cycle loses exactly:

| Edge ID | Row | Placement | Count slice |
|---:|---:|---|---|
| 308566 | 0 | Suffix | `(3,5,4,5,3)` |
| 3806548 | 1 | Prefix | `(3,5,4,5,3)` |

Both orientations match each row. These four recognition results represent two graph edges and one physical window in the period. The saved milestone139 conditional six-cycle has no match and survives unchanged.

The earlier milestone131 completed four-cycle also has matching edges 2220858 and 146782, with chronological counts `(3,5,4,4,3)`. Its survival checks occur before the new deletion. The later historical 18-cycle check and the assertion reconstructing the earlier nine-direction deletion now explicitly use `previous139_mask`. They are not assertions that every historical cycle survives the new mask. The result records this predecessor interpretation of the old 18-cycle mean.

Because the conditional six-cycle survives and the weights are unchanged, the old conditional potential remains valid on the smaller graph and this cycle retains mean 496. This is a finite-graph deduction under the inherited assumptions, not a new actual-snake bound. No new completed-profile minimum was calculated.

## Required future proof-completion interface

The generated evaluator calls `_checked_weak_exclusion` before resource allocation, output-directory creation, or importing the graph code. The parent invocation and worker both pass through this gate. A missing or unsuitable record produces `NOT_STARTED_PROOF_GATE` and exits with code 2.

The future `data/proof-completion.json` must have a `status` beginning with `PASS` and a `weak_actual_theorem` object containing:

| Field | Required value or meaning |
|---|---|
| `checked` | Boolean `true` |
| `directions` | `[0,1,2,0,3,2]` |
| `bounds` | `[[3,3],[0,5],[4,4],[0,5],[3,3]]` |
| `theorem` | Nonempty name of the checked weak actual-snake theorem |
| `source` | Source path, relative to the repository or absolute, inside milestone140 |
| `source_sha256` | SHA-256 of that saved Lean source |
| `receipt` | Path to its successful audit receipt, inside milestone140 |
| `receipt_sha256` | SHA-256 of that saved audit receipt |

The audit receipt must have `status: "PASS"`, the matching `source_sha256`, and a `source` resolving to the same file. The named theorem must occur in the source. The gate verifies all three saved hashes: completion record, source, and audit receipt. These pins are retained in the run record and final result and rechecked with the other source pins before a successful result is written.

This interface requires a successful audit for the weak actual-snake statement. It does not accept the current exact-pattern proof alone. Completion and truth of that audit remain the responsibility of the separate proof-verification workflow; this preparation does not fabricate or replace it.

## Preparation checks

- Parsed the generator and generated evaluator.
- Checked all 7,776 five-symbol vectors from `{1,...,6}`: the oriented bounds, their reversals, and the closed chronological predicate agree; every match has all symbols below 6.
- Checked 1,010 direction/placement combinations from the saved extension metadata: explicit orientation recognition agrees with canonical shape recognition.
- Verified the saved five-cycle deletions and conditional six-cycle survival from JSON rows.
- Executed only the isolated gate function against a deliberately absent receipt path; it rejected the missing record. The evaluator itself was not executed.
- Retained exact predecessor checks, all-edge potential verification, attained-cycle verification, integer overflow checks, resource gating, and timeout/failure records for any future authorized execution.

Both profiles retain all inherited count-sum and count-free-floor assumptions, the hypothetical `0123104` six-count floor 25, and the odd-length restriction behind pair-floor-nine deletions. The occurrence theorem does not remove the graph's odd-length restriction. Even-length bounds and the complete graph-to-snake comparison require their own arguments. No new numerical global bound is claimed.

## Source pins

| Repository-relative path | SHA-256 |
|---|---|
| `milestones/139-exclusion-occurrence-credit/scripts/evaluate_graph.py` | `c38a19a4e6288f8c1e88bbc9c004525527bc613339683157569c88f0d0e244c7` |
| `milestones/140-five-cycle-window/scripts/prepare_graph.py` | `f3dd3f9850dceb43dfb64b9430779a3050afaa89795cde2f36c1ff1e49eb9e1d` |
| `milestones/140-five-cycle-window/scripts/evaluate_graph.py` | `ef83027eb70f0c2dd2a6e519d2cee78bcfe72e1559b6c04134d51dd5f55e6b42` |
| `milestones/139-exclusion-occurrence-credit/data/exclusion-credit83/results.json` | `f641bff071d86701feca3a0c80e5ee3e7f65b35e511e91029ba14813d23eb23f` |
| `milestones/59-extended-share-window/extended/data/model.json` | `2334325d650cc9b71c0c6ab836183cecd4f1fc4d8b6555f63211592a22a0e2bf` |

The preparation receipt contains the same generator/evaluator pins and the detailed saved-row recognitions. The only intended next activation is after the weak actual theorem's successful proof-completion record is available.
