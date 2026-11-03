# Independent saved-result review

Status: `PASS_INDEPENDENT_SAVED_RESULT_REVIEW`.

Both saved cycles were rebuilt from original source-array rows with exact credit and scaling checks. The new deletion and retained event counts were checked independently from direction/count-code attributes. Potential hashes, lengths, ranges, and saved-cycle zero slacks were checked. No independent all-edge potential scan or graph search was performed.

| Profile | Original mean | Original range | Cycle length | Credited events | Exact comparison | Integer part |
|---|---|---|---:|---:|---|---:|
| completed | 2446/5 | 2973/5 | 5 | 0 | 5520661/23446 | 235 |
| conditional_floor18 | 496 | 602 | 6 | 0 | 552097/2348 | 235 |

Newly removed source edges: [992157]. Each original NPZ member was read once; the largest array held 19788032 bytes.

All source pins and detailed checks are recorded in `data/result-review.json`. The producer reports the full all-edge certificate; this independent review checks saved cycle slacks only.

The inherited odd-length restrictions and hypothetical local floors remain. The actual-snake graph and charge assembly remain separate obligations. No new actual-snake upper bound is claimed.
