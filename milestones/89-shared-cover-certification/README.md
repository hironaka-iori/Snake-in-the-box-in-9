# Milestone 89 checkpoint: shared covers and balanced lookup

This checkpoint records **28 Lean theorem audits** and successful geometric
coverage certificates for **classes 0 and 1**. The sequential run for all 127
classes is active. The full witness data for all 791 compatible contexts is
materialized and computationally validated; its concrete Lean validity
equations remain pending. No new numerical upper bound is claimed.

The [mathematical note](mathematical-note.md) defines shared rejection covers
and history-free witnesses. It explains how the geometric certificate, witness
validity and history transport combine. The [proof summary](data/proof-summary.json)
identifies the checked modules and the exact finite scope at this checkpoint.

## Completed work

| Result | Evidence |
| --- | --- |
| All shared cover trees generated | 127 classes, 82,659 box occurrences, 152,643 tree nodes; 5,925,312 independent pointwise checks |
| All context witnesses materialized | 543,827 occurrences in 791 contexts; 4,387 constructors and 211 aligned witness lists |
| History transport | Four Lean audits; reference, short and interval witnesses transfer across bounded histories of the same direction |
| Separate geometry and witness assembly | Four Lean audits; equal list lengths prevent truncation; the leading history witness keeps its original position |
| Array/list checker equality | Two Lean audits; no runtime improvement follows from this equality alone |
| Balanced lookup and general lookup checker | Seven Lean audits; lookup agrees with the original list for every index and default |
| Concrete graph table | Three Lean audits; validity, exact flattened contents and transition equality |
| Classes 0 and 1 | Eight Lean audits; box-table validity and identity, balanced coverage, and the original coverage equation |

The standard audited axioms are subsets of `propext`, `Classical.choice` and
`Quot.sound`. The concrete balanced coverage equations use no axioms. The
inherited proof environment is reused; no full dependency rebuild is claimed.
Data-module compilation is recorded separately and adds no theorem audits.

Only three materialized witness occurrences depend on history. They occupy
position zero in the lists for contexts (177,43), (177,70) and (180,68).
The other 788 contexts have history-free lists. Identical list data across
different directions still requires direction-specific validity checks.
See the [witness audit](audit/context-witnesses.md) for the complete schema.

## Lookup experiment

The direct class-1 check was stopped after 685.187 seconds, and the array-box
variant after 475.312 seconds, with no successful coverage result. Their logs,
records, process observations and source versions are preserved. Both ran
concurrently with other checks, so these are censored observations, not a
controlled speed ratio.

The balanced version checks the same original coverage equation. Its class-1
proof module passed in 51.828 seconds, with 32.985 seconds for its box-data
module. The shared graph-data and graph-check modules took 148.079 and 133.078
seconds and are reused by subsequent classes. Class 0's proof module passed
in 66.453 seconds. Complete batch performance remains to be measured.

The graph-check compiler succeeded on its first run. The audit script then
incorrectly demanded zero axioms for an equality involving arrays; the
recorded proof uses standard `propext` and `Quot.sound`. The checker was
corrected, and `recover_graph_audit.py` verified the existing source, output
and compiler record before preserving the successful object. No recompile
or proof-source change was used for that recovery. The earlier checker bytes
are saved in `data/check-balanced-covers-before-axiom-repair.py.txt`.

Independent source/data reviews cover the [original shared certificates](audit/shared-cover-review.md)
and the [balanced tables](audit/balanced-cover-review.md). Their proof-status
snapshots are historical. Later successful receipts provide the current
checked results; the reviews alone do not certify a Lean compilation.

## Live processes and reproduction

At this checkpoint the existing full-class process is tool session **23168**,
running `scripts/check_balanced_covers.py --classes all`. It checks classes
sequentially and reuses matching successful receipts. Inspect the actual
process and `data/balanced-cover-active.json` before any restart. A lock file
alone is insufficient evidence that a process remains live.

The case7302 replay is tool session **14427**, started by
`scripts/resume7302_unique.py`. Its original driver stopped at Check66 after
300 seconds. A first resume then encountered a stale temporary-output error.
The second resume uses a 900-second limit and a unique temporary filename;
Check66 passed in 130.02 seconds and later modules continued. Proof sources
and final object names are unchanged. Both failed attempts and their source
driver bytes are preserved. The case is still awaiting its final local theorem
and audit. Do not start another replay while this process is live.

The inherited driver repeats composition records when resumed. This checkpoint
therefore counts **distinct successful modules**, separately from raw successful
rows. Its delta archive reuses previously pinned object hashes and freshly
hashes newly completed objects. See [checkpoint.json](data/checkpoint.json)
for exact counts, process observations and the frozen run records.

The generator and checker entry points are:

```text
python scripts/materialize_witnesses.py
python scripts/build_shared_covers.py
python scripts/build_balanced_covers.py
python scripts/check_balanced_covers.py --classes all
python scripts/verify_saved.py --verify
```

Use the existing pinned Lean 4.19 installation and the paths in the scripts.
Do not regenerate sources while a compiler is using them. Earlier generic
modules have their own check scripts and exact source/object/log receipts.
The live run records and active output logs are excluded from the frozen
manifest; immutable copies of their observed state are included instead.
Later completed modules do not retroactively enlarge this checkpoint's claim.

## Remaining work

1. Complete the existing 127-class geometric batch.
2. Check the concrete context witness equations, using history transport where
   applicable, and certify the context-to-class assignment.
3. Connect diagram membership to saved full-key rows and both endpoint columns.
4. Close the reference-catalogue premises, remaining local shares, credit
   interpretation and complete potential replay.

The project interval remains 191 through 235 edges; 234 remains conditional.
The 235 upper bound uses the inspected contributor theorem and saved audit,
without a fresh full independent rebuild. The paper remains revision 86;
the next full revision is scheduled for milestone 96. Authors and hyperlink
settings are unchanged.
