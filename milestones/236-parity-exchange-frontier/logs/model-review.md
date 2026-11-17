# Round 236 degree-model review

## Source and parameter review

No new model restriction or source-level defect was found. `scripts/degree_search.py` is byte-identical to the frozen round-235 producer, SHA-256 `ea4685761c79ae140d07023477c0bd9cbc67ac5301a6c4176079a5f923e59e60`. The wrapper is likewise unchanged, SHA-256 `01334f18dfc66804fb7fa2135c1d57b749d9ae9b3ac0f9b3f9edc8437a291a37`. The native producer still defaults to two exchanges; the round-236 process command explicitly supplies three.

The necessary-model argument is unchanged. There are exactly 96 minority and 97 majority selected vertices. Exactly two selected majority vertices are endpoints. The selected degree is one at those endpoints and two at every other selected vertex. Unselected vertices impose no degree constraint. Consequently a feasible selection consists of one path and zero or more disjoint induced cycles, and every intended 192-edge path satisfies the model. With exchange count `k`, the retained saved-class count must equal `96-k`. This prescribes exactly `k` removals and `k` insertions; it does not mean at most `k`.

The independent auditor now requires an explicit `--exchanges` value and explicit batch tags. It uses that value in every model equation, row, selected-component check, witness comparison and output scope. It independently parses the execution command and requires its arguments to match the saved result arguments. The historical producer default of two therefore cannot silently substitute for a required count of three. Output receipts include the required exchange count and retained count; an existing receipt is never overwritten.

Each initial model must still have exactly 768 Boolean variables and 772 constraints, including all 512 positive selection guards. The independent parser consumes every field and rejects extra model content. Feasible iterations, if present, are reconstructed into components; added cuts must be exactly the cycle components observed previously and must appear in subsequent models. Native UNKNOWN and time exhaustion remain unresolved. Full saved-base coverage is asserted only when all 145 distinct IDs are actually present and the optional `--require-all-145` condition passes.

The adapted auditor SHA-256 is `1d416d0d27bfc5ac86647f4c7021a32e441230f69ed0c75845c5ddfcc18b0693`. The prior round-235 auditor remains unchanged at `55e746b2b52c468347d6b680ba7414c8eaea382a0fbc9673b93d194ea26ac8c2`.

## Frozen initial batch

Following explicit authorization to inspect the terminal initial batch, the four saved models in `three` were audited independently while the separate remaining-base worker continued. Only frozen initial-batch inputs were read; no live remaining-batch record was inspected. The direct saved-data calculation took approximately 0.19 seconds and invoked no solver, compiler, producer or software test.

The audit passed for bases 139, 7, 6 and 0. Each recorded process and row specifies three exchanges, every retained-class equation is exactly 93, and every model contains the complete expected degree relaxation. Each native outcome is INFEASIBLE in its initial model; there are no cycle cuts. Source/input/model/result/log pins and stdout correspondence all match.

Receipt: `data/three-initial-audit.json`, status `PASS_FROZEN_INITIAL_BATCH_AUDIT`, SHA-256 `c978c25865020a5b19c570ca643c085ed73fd2d9b7f6ff3c0ea78744958ad80a`.

This initial receipt covers four saved classes only. It does not assert an all-145 cover, replay native contradiction certificates, or establish a global bound. The full union audit is pending the terminal remaining batch.

## Full-union command after completion

```text
audit_degree.py --execute --tags three,three-rest --exchanges 3 --audit-tag three-audit --require-all-145
```

The main audit refuses execution while the native worker lock exists. This command will preserve the initial receipt, write a separate `data/three-audit.json`, and append the complete union outcome below if all checks pass. No old round-235 artifact has been modified.

## Executed saved-model audit

Status `PASS_DEGREE_MODEL_AUDIT`. Covered 145 saved bases and checked 145 exported models. Native statuses: `{'INFEASIBLE': 145}`. Verified added cycle cuts: 0.

Required exchange count: 3; retained saved vertices: 93. All 145 saved families at this exact count have native exclusions: `True`. Unqueried bases: `[]`. This records native evidence and exact model inspection, without independent native contradiction replay.

Auditor SHA-256: `1d416d0d27bfc5ac86647f4c7021a32e441230f69ed0c75845c5ddfcc18b0693`. Receipt SHA-256: `f5bd12ab1e5739cecb48142e1b2d3f46e36e5a95cd279aa2a93ae6bb3d3abba4`. Complete evidence pins are in `data/three-audit.json`.

## Executed saved-model audit

Status `PASS_DEGREE_MODEL_AUDIT`. Covered 4 saved bases and checked 4 exported models. Native statuses: `{'INFEASIBLE': 1, 'UNKNOWN': 3}`. Verified added cycle cuts: 0.

Required exchange count: 4; retained saved vertices: 92. All 145 saved families at this exact count have native exclusions: `False`. Unqueried bases: `[1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 140, 141, 142, 143, 144]`. This records native evidence and exact model inspection, without independent native contradiction replay.

Auditor SHA-256: `1d416d0d27bfc5ac86647f4c7021a32e441230f69ed0c75845c5ddfcc18b0693`. Receipt SHA-256: `2d2a340e61e859edd5b2f2a76a9e753764a7575f80654ec352d00fdb963966b1`. Complete evidence pins are in `data/four-audit.json`.
