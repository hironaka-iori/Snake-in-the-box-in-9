# Milestone 93: optimal comparisons for three fixed weighted graphs

Seven new Lean theorem audits establish a general cycle-and-path comparison and three conditional rational applications. Exact numerical certificates, independently checked, show that the current comparison values are jointly optimal in the constant slope and global potential range on each of the three pinned weighted array graphs.

| Profile | Cycle mean | Normalized potential range | Best comparison | Integer comparison |
| --- | ---: | ---: | ---: | ---: |
| Completed floors | $483$ | $551$ | $157625/669$ | $235$ |
| Additional assumed 012034 floor 20 | $9259/19$ | $11301/19$ | $20965613/89059$ | $235$ |
| Full conditional floors | $496$ | $600$ | $137941/587$ | $234$ |

The [mathematical note](mathematical-note.md) defines the path deficit and proves the joint comparison. The [independent review](audit/range-certificate-review.md) checks all 4,947,008 edge inequalities for each profile and 73 witness occurrences, representing 61 distinct full keys. Concrete graph embedding remains computational evidence; the Lean applications retain its hypotheses.

The consequence is specific: changing only these two potential parameters cannot improve the fixed-model fractions. Stronger credits, additional actual-snake restrictions, stronger boundary accounting and endpoint-dependent estimates remain possible. The selected next task is the exact credit-to-five-centre-share theorem, especially complete variant coverage for the 55 history share rules. See the [weight interface audit](audit/weight-bridge-plan.md).

The maintained interval remains $191\le a(9)\le235$ edges, with 234 conditional. The 235 upper bound still relies on the inspected contributor theorem and saved audit, pending a complete independent rebuild. No new numerical snake bound is claimed.

## Saved evidence and reproduction

- `data/*-range-certificate.json`: full cycle and path keys, weights, endpoint potentials and input hashes.
- `data/PotentialComparison-audit.json`: successful Lean run and seven printed axiom audits.
- `data/range-certificate-review.json`: independent numerical review.
- `data/checkpoint.json`: frozen proof-job observations, remaining obligations and paper hash.
- `data/file-manifest.json`: exact saved bytes, excluding build objects and mutable jobs.

Run `scripts/check_comparison.py` to check the standalone theorem source. It creates a unique log for each attempt and checks the printed axiom sets. Run `scripts/verify_saved.py --verify` to check the saved manifest. The numerical extractor reads the pinned local arrays and potentials; its paths and hashes are recorded in the certificates.

The independent implementation is preserved in `scripts/review_range_certificates.py`. Its saved-script rerun passed, and every report field matched the original review except the timestamp. It creates a new output file and refuses to overwrite saved evidence. The reproduction and comparison receipt are included in `data/`.

The geometry and witness batches continue separately. Case7302 reached a 900-second timeout in Check1. Its owner exited while a compiler child remained; exact process evidence was preserved and the confirmed orphan was stopped. No local-share theorem follows from the partial replay. The witness batch was stopped only while idle, with no children, to check the small comparison module, then resumed with its unchanged checker. Inspect the checkpoint and actual process state before restarting any batch.

Paper revision 86 is preserved byte-for-byte in both locations, including all three authors and hyperlink settings. The next scheduled full paper revision is milestone 96.
