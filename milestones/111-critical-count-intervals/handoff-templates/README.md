# Research handover

Work in `E:/Snake-in-a-box`. Read milestone 111's
`mathematical-note.md`, `data/proof-summary.json`, `data/checkpoint.json`
and `audit/final-review.md`. `CURRENT_STATUS.md` starts with the latest
checkpoint; its older sections are historical. Follow `NEXT_AGENT_PROMPT.md`
for the next bounded task.

For canonical transition pattern `012340`, the latest Lean-checked result
requires the second internal count to be at least 4, the third at least 3,
or the fourth at least 6. The first and fifth internal counts are free.
The actual-snake transfer and both graph orientations are checked.

Three proposed outer-sum inequalities together improve the completed
finite-graph mean from 483 to 3384/7. The integer comparisons remain 235
and conditional 234. The sum inequalities and their common excess-charge
argument are still unproved in Lean. The sum-22 instance has a complete
native contradiction certificate with independent replay; the two other
sum instances have solver results only. These evidence levels must remain
separate.

The maintained range is 191 through 235 edges. Evidence for 235 consists
of the contributor proof and archived audit; its complete independent
rebuild remains pending. The exact optimum, including the proposed 196,
is unresolved.

Preserve the running milestone 104 batch and all exact proof inputs and
logs. Large proof files remain locally, with verified gzip copies in the
repository. `data/large-artifact-archives.json` records both sets of hashes.
Use `scripts/verify_saved.py --verify` to check the saved package and
`--restore-archives` if raw files are missing after a fresh checkout.

The three paper authors and hypersetup settings are unchanged. Paper
revision 106 remains current; the next full revision is scheduled for 116.
Introduce definitions only for essential concepts that will be used repeatedly.
