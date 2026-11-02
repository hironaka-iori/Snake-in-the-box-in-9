# Witness batch plan

The pinned materialized data reduces to **507 base validity jobs and three history-head checks**, covering all **791 contexts** and all 127 geometric classes. The whole-list grouping is exact: no two remaining jobs at the same direction contain identical ordered geometry/witness pairs. This count does not assert minimum work under possible per-entry sharing or additional proof lemmas.

Every base is checked at history zero. `entries_valid_transport` then reuses its validity at the same direction and any required history below 75. The base job also requires `entriesHistoryFree = true`. There are **210 distinct base-list data records**, derived from the original 211 lists. Reusing list data across different directions does not transfer validity; the corresponding direction-specific jobs remain distinct.

The three history constructors occur at original position zero:

| Direction | History | Class | Original list | History rule | Witness ID |
| --- | --- | --- | --- | --- | --- |
| 177 | 43 | 85 | 112 | 0 | 4363 |
| 177 | 70 | 85 | 113 | 2 | 4364 |
| 180 | 68 | 89 | 117 | 1 | 4366 |

The two class 85 contexts share one identical tail job at direction 177. Their heads are checked separately. `SharedAssembly.base_after_history_valid` restores the head before the transported tail. Appending it would change the box order and cannot be substituted without a separate reordered cover proof. Class 89 similarly uses its tail and its own history head.

For every context, the script reconstructs the full ordered geometry/witness pairs from its base slice and optional head and compares them with the original zip. All lengths, class positions, original list IDs, direction/history IDs and context mappings agree. No geometry or witness validity is recomputed.

## Work counts and first jobs

- `contexts`: 791.
- `classes`: 127.
- `original_witness_lists`: 211.
- `base_lists_after_removing_history_head`: 210.
- `base_validity_jobs`: 507.
- `history_validity_jobs`: 3.
- `whole_list_jobs_total`: 510.
- `base_entry_checks`: 357820.
- `history_entry_checks`: 3.
- `context_entry_occurrences`: 543827.
- `context_nonhistory_occurrences`: 543824.
- `base_context_checks_saved`: 284.
- `base_jobs_reused_for_multiple_histories`: 104.
- `max_contexts_per_base_job`: 12.
- `base_list_groups_reused_across_directions`: 126.
- `base_list_reuses_across_direction_jobs`: 297.
- `further_whole_entry_list_merges_within_direction`: 0.
- `smallest_base_job_entries`: 302.
- `largest_base_job_entries`: 963.
- `entry_checks_saved_by_history_transport`: 186004.

Smallest global job: job 212: direction 210, class 108, 302 entries, original lists [139].

Largest global job, with deterministic tie-breaking: job 68: direction 68, class 26, 963 entries, original lists [45].

Smallest job with an observed completed geometric class: job 0: direction 0, class 0, 375 entries, original lists [0].

Class 1 supplies a useful six-job integration batch: directions **1, 3, 307, 308, 310 and 312**, each with 640 entries, all at history zero. Directions 1 and 310 use original list 1; the other four use original list 3. These are two data lists and six validity checks. Their exact job IDs and original context indices are in `class1_contexts`.

## Manifest and evidence boundaries

`base_lists` records the exact witness IDs and original class-position slice `[start, stop)`, plus an ordered pair hash. `base_jobs` gives direction, history-zero equations, source lists and every receiving context. `history_jobs` preserves the original head position, geometry ID and constructor. `contexts` maps all original payload rows to these jobs. Box geometry and witness constructors are addressed by their original IDs in the hash-pinned payload. No class or list is relabelled.

Job IDs, complete mappings and the core manifest hash are deterministic. Receipt observations are separate and may change between runs. The current matching geometric receipts were observed once, without waiting: classes **0, 1, 2, 3, 4, 5**. This observation checks source/object/log hashes and the printed original-cover theorem where applicable; it does not independently rebuild their transitive dependencies.

The existing generic transport and head-restoration sources, objects, logs and receipts were hash-checked. No new Lean validity proof, context membership theorem, saved-row theorem or global snake bound follows from the plan. Entry counts measure batch size; they are not runtime estimates.

- Input witness payload SHA-256: `5dd985dc9e31441f481881895a827b7d88d68864b5104f07483adaaf86932d51`.
- Planning script SHA-256: `5a03df6ab15d1c8fa68d5a0c38833d2954130d221058e4babcc239b1a89a98a4`.
- Deterministic core manifest SHA-256: `22eec8fb9d7dda688f7cf62244fc5023d15fca601028e42b7ae707c640b9e302`.
- Complete plan SHA-256: `68ae7c1c81d6c714a63964c5859d0e8b3cfaa93bf7a30569252dcb22bd9f376c`.
- Observation time: `2026-11-02T13:30:17.704696+00:00`.
