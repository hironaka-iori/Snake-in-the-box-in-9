# Milestone 128: the proved pair constraint

The proved 012032 pair inequality is now connected in Lean to the concrete
0120324 search: at most 34 of its 42 paired corner occurrences are selected.
Five repeated vertices retain both occurrences. Lean also checks satisfaction
of all 2863 added counter clauses for actual snakes. Two modules and ten
dependency reports passed. The conjunction with the preceding 101666 clauses
and a complete contradiction remain separate requirements.

An independent audit reconstructs the new input exactly, and a separate
parser matches the Lean certificate data to the added clauses. The bounded
search timed out after 180.062 seconds, using 24.59375 seconds of process CPU
time. Its first 1000 deductions pass a check against the new input; no complete
refutation or new count floor is established. The partial trace is saved in
a verified lossless archive.

The next selected task splits the fourth count into equality to three and
at least four. In the equality case, existing results force the first count
to be at least three and the second at least five, leaving at most eleven
for the other three counts under the total-22 hypothesis. The split assembly
is written but not yet checked in Lean; neither branch has been excluded.
See `milestones/128-coupled-pair/data/next-case-task.json`.

The maintained range remains 191–235 with the documented independent-rebuild
limitation. The optimum, 196, and the hypotheses for 234/233 remain open.
No new mathematical definition is introduced. Paper revision 126 is unchanged;
the next scheduled full revision is 136.

## Saved evidence

- `MATHEMATICAL_NOTE.md`: the count argument and the next exhaustive split.
- `lean/`: actual normalized count bound and concrete added-clause proof.
- `audit/pair-derivation.md`: successful Lean receipts and exact proof scope.
- `audit/pair-counter-review.md`: independent encoding and bounded trace review.
- `data/lean-data-review.json`: parsed Lean data matched to the new input.
- `data/search.json`: the terminal timeout and measured CPU time.
- `archives/pair.raw.lrat.gz`: verified lossless copy of the partial trace.
- `data/next-case-task.json`: the next task with checked-premise source pins.
- `data/checkpoint.json` and `data/file-manifest.json`: the resumable checkpoint.

The early concrete-generation record says generated, not yet checked, and the
independent review records the semantic work as pending at its own timestamp.
The later successful Lean receipts supersede those statements for the added
2863 clauses. They do not establish a complete contradiction.

Run `scripts/verify_saved.py --verify` to verify the saved checkpoint.
Use `--restore-archives` when the raw partial trace is needed after checkout.
All source, failed attempts, resource-gated attempts, successful logs, objects,
and dependency pins are retained. The original raw trace is excluded from Git
because the verified archive preserves its bytes below the repository size limit.
