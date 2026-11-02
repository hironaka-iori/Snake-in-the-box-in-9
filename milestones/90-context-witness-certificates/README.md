# Milestone 90: witness compatibility and count conditions

This checkpoint records **17 Lean theorem audits**, including a concrete
retained-code membership result for six direction words. It also checks a
general separation of witness compatibility from count conditions. The
complete 791-context certificate remains open. No new upper bound is claimed.

The [mathematical note](mathematical-note.md) gives the definitions and the
deduction from a witnessed rejection cover to retained-code membership.
The [proof summary](data/proof-summary.json) and
[checkpoint](data/checkpoint.json) specify the checked scope and dependency
limits. Sources, logs, receipts, data and current handover files are pinned
by the [file manifest](data/file-manifest.json).

## Checked results

| Module | Theorem audits | Result |
| --- | ---: | --- |
| WitnessLookup | 4 | Replacing only catalogue lookups and length preserves the original validator |
| WitnessTablesChecks | 8 | Balanced tables contain exactly the original 505 direction words and 1,378 reference keys; all-index lookups and defaults agree |
| Class001WitnessChecks | 2 | Six witness assignments are valid and imply membership in the original class-1 diagram |
| WitnessFactors | 3 | Compatibility and count factors equal the original checker; separate list certificates can be combined |

All printed axiom dependencies are subsets of `propext`, `Classical.choice`
and `Quot.sound`. No proof source uses `sorry`, `admit` or `native_decide`.
Data-module compilations have separate receipts and add no theorem audits.
The inherited dependency environment is reused; a complete independent
rebuild is not claimed.

The concrete pilot uses 640 boxes and two witness lists for directions
1, 3, 307, 308, 310 and 312. Its six jobs check 3,840 entries. Since all those
witnesses are history-free, the resulting theorem holds for every history
index below 75 under the original numerical retention predicate. The proof
module passed in **21.125 seconds**, excluding data compilation and shared
table checks. It does not certify the complete context-to-class assignment.

The generic factorization retains every catalogue and placement guard,
orientation, length condition, count test and lookup default. History retains
the original decoded-direction computation. The normalized shape expressions
do not contain count values or catalogue indices; a reference key's separate
guards and count assertions still need checking. Concrete descriptor equality
and finite assembly have not yet been proved.

## Complete job plan and computational profile

The [job plan](audit/witness-batch-plan.md) reconstructs all 791 materialized
contexts as **507 base validity jobs and three history-head checks**. The
three heads retain their original position zero. There are 210 base lists,
357,820 base entries and three separate heads. This saves 186,004 repeated
entry checks relative to the 543,827 original occurrences. Different
directions still require their own compatibility proofs.

The [factor profile](audit/witness-factor-profile.md) compares the original
and factored Boolean evaluations on all **357,823 planned entries**. They
agree throughout. The profile contains:

| Factor | Distinct descriptors |
| --- | ---: |
| Outer guards | 508 |
| Catalogue and placement guards | 2,329 |
| Direction or history shape tests | 15,353 |
| Box/count tests | 2,651 |

Reference rules account for 338,697 entries. Their 337,485 catalogue-indexed
shape calls reduce to 12,560 normalized shape expressions. This is the most
substantial reuse opportunity in the saved data. The profile preserves
usage counts, source provenance and every entry-to-factor map. All its
saved entries are true; its finite comparison alone proves no general
identity on invalid inputs. The checked generic identity is separate evidence.

The [independent pilot review](audit/witness-pilot-review.md) checks the exact
table ordering, witness alignment and theorem scope. Its earlier status
snapshot predates the successful table and pilot compilations; the final
receipts record those subsequent successes.

## Continuing proof runs

At this frozen checkpoint, the existing geometric run has completed
**classes 0 through 12**, out of 127. Eleven classes completed after the
milestone89 snapshot, adding **44 geometric theorem audits** outside the
17 audits of this milestone. Their immutable receipts and logs are included
in this manifest. The active process is tool session **23168**,
`milestones/89-shared-cover-certification/scripts/check_balanced_covers.py --classes all`.

The case7302 replay is still tool session **14427**, through
`milestones/89-shared-cover-certification/scripts/resume7302_unique.py`.
This snapshot records **449 distinct successful modules**, including 60
newly observed since milestone89. Repeated composition rows are counted
separately in the checkpoint. Its final local-share theorem and audit remain
pending. The prior timeout and output-path failure remain preserved in
milestone89. No successful source has been regenerated.

These are frozen observations. Both processes may have advanced since the
snapshot. Inspect their actual processes and active records before any
restart. Completed logs are archived separately from mutable run records;
the checkpoint records source/object hashes and inherited hash provenance.

## Next task and reproduction

Test normalized reference-shape reuse on the same six class-1 jobs. Include
the descriptor-to-source equalities, finite factor checks and assembly in
the comparison. No speed improvement has yet been measured. If the experiment
is effective, expand it to the saved 507-job plan and three history heads.
The simpler checked pilot remains an available baseline.

Then certify the complete context assignment and the saved full-key rows
and endpoint columns. Keep `AllRefuted6K235` and `AllRefuted236` explicit until
their closed dependencies are supplied. Pending local shares, credit
interpretation and complete potential checking remain separate obligations.

The relevant check entry points are:

```text
python scripts/check_witness_lookup.py
python scripts/check_pilot.py
python scripts/check_witness_factors.py
python scripts/verify_saved.py --verify
```

The saved plan and profile have reproducible scripts. The planning script
also records the live geometry receipts observed when it runs; rerunning it
can change the observation metadata. Preserve this checkpoint's exact bytes
when creating a later snapshot. Do not regenerate sources used by a live
compiler. Use the pinned Lean 4.19 installation and dependency paths in the
checkers. Built objects remain saved locally and are excluded from Git.

The maintained project interval is **191 through 235 edges**, with **234
conditional**. The 235 upper bound uses the inspected contributor theorem
and saved audit; a complete independent rebuild remains pending. Paper
revision 86, its three authors and hyperlink settings are unchanged. The
next full paper revision is scheduled for milestone96.
