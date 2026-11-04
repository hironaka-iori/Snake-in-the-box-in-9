# Bounded implementation review

Status: `PASS_CODE_REVIEW_NO_MATHEMATICAL_BLOCKER_FOUND`.

Reviewed `reconstruct_mapped.py`, `potential_range_v4.py`, the version-4 launcher, the milestone-157 worker, the preceding version-3 worker and its failure records. The mapped reconstruction agrees with the independently reviewed scalar formula. The version-4 discovery and certificate mathematics agree with milestone 157. This review did not run graph computation, replay a journal, compile Lean, or claim that the running version-4 experiment had completed.

## Reconstruction and integer representation

The loader extracts only `U`, `V`, `weight`, `direction` and `count_code` from the original NPZ into a fresh run directory, then opens them as read-only mapped arrays. It checks each column's size and raw hash against the pinned source metadata. The launcher also checks the archive and metadata input pins. The unused history column is unnecessary for this weight formula.

Direction indices are checked for sorted order and the expected endpoints. Each direction interval is handled in batches of at most 65,536 rows. The code decodes counts using signed 64-bit division before storing symbols 1 through 6 as signed 16-bit integers. These symbols, interval endpoints through 21, five/six-count sums through 36, and the pair calculation are within range. In particular, `9-counts[:,2]-counts[:,4]` cannot wrap as unsigned arithmetic. Bonuses and final weights use signed 64-bit arrays.

The old-rule orientation, saturated interval containment, suffix-only credit placement, pair bonus without an exact-count guard, and chronological first-count guard on the six-count bonus match the scalar formula. The three bonuses enter through their maximum. No later modification was found.

The loader reuses the accepted milestone-144 removal list. It checks its size, uniqueness and index bounds, then the worker compares the resulting removed rows with that list again. This carries the accepted exclusions without reconstructing their provenance. Those mathematical assumptions remain inherited.

Before changing the floor, the worker checks the old milestone-144 weight hash and source floor-18 hash. It then requires the entire reconstructed graph summary, including the complete milestone-156 retained-weight hash and retained-row-ID hash, to equal both accepted milestone-156 records. The accepted potential's archive and raw hashes are checked, and every original retained inequality is scanned before the floor is weakened.

The floor change recomputes the source/floor maximum. It does not indiscriminately subtract one from every 012034 row. The alias `weaker_conditional = conditional` is safe at this point: all original-profile checks have completed and no later computation needs the original conditional vector. Earlier deletion of the large temporary arrays does not remove a later dependency.

## Equivalence with the milestone-157 worker

The complete text diff from milestone 157 to version 4 changes the reconstruction import and call, thread limits, preparation/environment names, progress reporting, temporary-array lifetime, the harmless conditional-array alias, and bounded file-replacement retries. It does not change the relaxation, selected mean, target range, obstruction threshold, journal predecessor rule, witness checks or final certificate scan.

The mathematical checks are correctly separated:

- A stabilized distance array gives a candidate potential only after the range is checked to lie from 603 through 631.
- A discovered deficit of at least 632 yields a fixed-mean target obstruction, after exact walk recovery and verification.
- Time, iteration or journal exhaustion remains unresolved. A recovered deficit may support a lower bound, but no feasible potential is claimed without stabilization and the all-edge scan.
- The old range-602 potential is recorded as invalid under the weaker floor, with minimum slack minus one. It is never used as a feasible upper bound for discovery.

At mean 496, the threshold is exact: range at most 631 gives a comparison strictly below 235, while range 632 gives 235. A fixed-mean obstruction does not exclude a retuned mean.

The relaxation is synchronous: candidates use the previous distance array throughout each iteration. The distance array begins at zero, so it records shortest-walk costs from a zero-cost super-source. The integer bound checks 1,503 times the largest possible absolute one-edge contribution against \(2^{62}\), safely covering 1,500 iterations, candidates and their differences within signed 64-bit arithmetic.

Journal records contain the changed vertex and its chosen edge, each encoded as an unsigned 32-bit integer. Both state and edge counts are checked below \(2^{32}\); each record occupies eight bytes. Changed vertices are sorted by `flatnonzero`. Each chosen edge attains the new distance and ends at the recorded vertex. Reverse traversal of the journal correctly skips layers in which the current vertex did not change. The recovered sequence is checked for adjacency and for exact equality between its deficit and the endpoint distance. A successful potential is additionally checked on every retained edge and for its claimed minimum and maximum.

## Version-3 evidence and the version-4 retry

The saved version-3 `original156-reconstruction.json` is exactly equal to the accepted milestone-156 graph object. Thus that run had already reproduced the complete old weight data before its I/O failure. Its weaker graph record reports 995,435 decreased source rows, 936,928 decreased retained rows, maximum decrease one, unchanged fourteen-cycle total 6944 and nine-walk total 3861. These are saved-run observations; this review did not recount the rows.

The exact version-3 traceback is a `PermissionError: [WinError 5] Access is denied` at `potential_range_v3.py`, line 46, in `temporary.replace(path)`, called by the discovery-progress save at line 269. The failing rename is

`data/floor17-mapped/progress.json.tmp` to `data/floor17-mapped/progress.json`.

The saved progress reports iteration 21 and maximum deficit 605. This is an interrupted progress observation, not a completed certificate or recovered final witness. The exception is an I/O failure and contains no failed mathematical assertion.

Version 4 changes the worker's save routine to try the same replacement up to 40 times, with 50 ms sleeps between failed attempts. There are at most 39 sleeps, totalling 1.95 seconds. It raises the final `PermissionError` if all attempts fail. The corresponding launcher save routine receives the same treatment. Other than versioned preparation paths, this is the complete worker diff from version 3. The retry does not change graph data or any numerical decision. Permanent access failures or failures while writing the temporary file can still stop the run; they cannot silently produce a successful certificate.

The version-4 launcher retains bounded resource checks: at least 2 GiB free memory at startup, at least 768 MiB while running, at most 1 GiB aggregate owned private memory, one owned graph task, no Lean process, a 600-second discovery budget and a 900-second total budget. These limits govern completion; this review does not certify their live enforcement by rerunning the monitor.

## Limitations and hashes

No mathematical blocker was found in the reviewed changes. Completion must still be established from the parent-owned run's final receipt, exact recovered witness and, if successful, its all-edge certificate. The source, mask and inherited geometric assumptions remain conditional. No accepted file was edited.

SHA-256 values at review:

- `reconstruct_mapped.py`: `97e893f5f4e1bbc13ba9227f74ae6e1d9f55b080e16f8553d7e8518f6248db81`
- `potential_range_v3.py`: `c0697b32d1ab8b6d77a1e937cc39bce637eafd6a057aba0f78b2b8924de02da3`
- `potential_range_v4.py`: `e1f939dbd8f247cf2ebac8af369643e31c9cf346bb7e270fa8781f084faab3ec`
- `run_potential_v4.py`: `6e016c8a2f96fe2c1b0bb845b292ef2026e2fb15b0c6acf03be45cc9fa8e8fd1`
- Milestone-157 worker: `a3688af5eaefe7ae152f7bd89f35eb959c0fe0900823aa5720d14a3272d2ddbf`
- Version-3 `stderr.log`: `5fb39bf509b812f30a0eb69f6b48d795507a87b1f73d89d2ac3e60daf1b0a025`
- Version-3 original-156 reconstruction: `3918a595d10198db5cbe49fa2477aa421a4622f2e4bd013c318b4792e2c07022`
- Version-3 weaker retained weights, as recorded: `22497b6436475fbd248e456d87ed9e7eb7ac4cf9d78ef2804704f1ef905024b2`
