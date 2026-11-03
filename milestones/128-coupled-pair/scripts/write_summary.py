"""Write the continuation record after both actual-snake checks have succeeded."""
from pathlib import Path
import hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
passed=[j for p in (H/'logs').glob('*/record.json') if (j:=read(p))['status']=='PASS']
assert {Path(j['importable_object']).stem for j in passed}=={'PairLower128','PairClauses128'}
assert sum(len(j['axioms']) for j in passed)==10
assert read(H/'data/lean-data-review.json')['status']=='PASS_EXACT_LEAN_PAIR_DATA_AND_CNF_TAIL'
assert read(H/'data/search.json')['status']=='TIMEOUT'
update='''# Research update: milestone 128

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

'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
 p=R/name;old=p.read_text(encoding='utf-8-sig');assert not old.startswith('# Research update: milestone 128')
 p.write_text(update+'## Earlier record\n\n'+old,encoding='utf-8',newline='\n')
next_text='''# Continuation after milestone 128

Work in E:/Snake-in-a-box. Use the requested research skill. Introduce a
definition only when it is essential and repeatedly used. Preserve the authors,
local hyperlink settings, unrelated .gitignore and milestone 50 critical-family
edits, and active proof jobs. Fetch GitHub and inspect the checkout first.

Read milestone 128's MATHEMATICAL_NOTE.md, audit/pair-derivation.md,
audit/pair-counter-review.md, data/lean-data-review.json, and checkpoint.
The independent counter review was frozen before the concrete Lean check;
its statements that this new semantic connection was pending are superseded
by the later pair-derivation note and successful receipts. That completion
covers the added 2863 clauses only.

Lean checks the actual 0120324 selected-corner cap34 and the concrete new
counter. Preserve42 occurrences over37 distinct vertices, including the five
doubled vertices18,34,66,130,258. The new input has104529 clauses and6248
occurring variables. Counter8 uses fresh variables7278 through8705. Its
geometric justification is not an original-input-only RUP derivation.
The preceding101666-clause conjunction still needs to be accounted for in
any complete actual-snake refutation. Do not reuse127's identifier mapping
for the added pair clauses without a new justification.

One180-second native run timed out, with24.59375 seconds process CPU.
Only its first1000 positive-RUP deductions were replayed against the new input.
No model or contradiction was obtained. Preserve the verified gzip archive;
verify_saved.py --restore-archives restores raw trace bytes when needed on
a fresh checkout. A partial trace is not an exclusion certificate.

Next selected task: data/next-case-task.json. Under a total at most22, split
alpha_(r+4)=3 from alpha_(r+4)>=4. The existing pair theorem gives
alpha_(r+2)>=5 in the first case, while first_fourth_exclusion gives
alpha_(r+1)>=3. The remaining three counts then sum to at most11.
First check this actual-snake split and arithmetic in Lean; then encode
and test the restricted branch. Keep both branches in the overall obligation.
Neither branch is encoded or excluded at this checkpoint. Avoid simply
repeating the unchanged unsplit input for another short wall-time timeout.

The target remains a six-count floor23 for0120324. A proof would remove the
sum22 edge of the saved conditional comparison cycle but would not automatically
improve the full graph minimum or the global upper bound. Universal floor25,
or the sufficient total-shortfall inequality retaining2s0, remains a separate
requirement for234. The current maintained range is191–235 with the contributor
upper-proof rebuild limitation. Neither the optimum nor196 is established.
The overall research goal remains active.

At the128 observation, drivers104/115/122 were live, with343 selected potential
modules,522 total-count modules, and340 endpoint-plan receipts. These are
point-in-time partial counts. Inspect actual process commands and terminal
records before restarting anything. Preserve all old attempts and locks.
New Lean checks use an isolated build and a fresh resource gate of at least
1.5GiB available memory and at most two other Lean processes.

The paper is revision126, unchanged SHA256
4667daec19f0b83af9fb129a263c8ae992757105414bad817c1ad13e1e11bb90,
identical at E:/Snake-in-a-box/paper/snake9_research.tex and the open editor
D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex. The last built-in
compile failed before TeX in the Windows helper. The next full revision is136.
Keep implementation names out of mathematical publication text. Save and push
reviewed checkpoints without treating the unresolved overall goal as complete.
'''
replacements={'Preserve42':'Preserve 42','over37':'over 37','vertices18':'vertices 18',
 'has104529':'has 104529','and6248':'and 6248','Counter8':'Counter 8','variables7278':'variables 7278',
 'preceding101666':'preceding 101666','reuse127':'reuse 127','One180':'One 180',
 'with24.59375':'with 24.59375','first1000':'first 1000','most22':'most 22','most11':'most 11',
 'floor23':'floor 23','for0120324':'for 0120324','sum22':'sum-22','floor25':'floor 25',
 'retaining2s0':'retaining 2s0','for234':'for 234','is191':'is 191','nor196':'nor 196',
 'the128':'the 128','drivers104':'drivers 104','with343':'with 343','modules,522':'modules, 522',
 'and340':'and 340','1.5GiB':'1.5 GiB','revision126':'revision 126','is136':'is 136'}
for old,new in replacements.items():next_text=next_text.replace(old,new)
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text(next_text,encoding='utf-8',newline='\n')
readme=update.replace('# Research update: milestone 128','# Milestone 128: the proved pair constraint',1)+'''## Saved evidence

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
'''
(H/'README.md').write_text(readme,encoding='utf-8',newline='\n')
note=H/'MATHEMATICAL_NOTE.md';s=note.read_text();assert '## Verification in this round' not in s
s+='''
## Verification in this round

Two Lean modules passed with ten dependency reports, all using only
`propext`, `Classical.choice`, and `Quot.sound`. They verify the actual count
conversion, normalization, and satisfaction of the 2863 added clauses. A
separate parser confirms that the checked source contains exactly the new
clauses, literals, tags, and variable meanings used in the search. The complete
conjunction with the older input is outside these two modules' scope.

The native run timed out after 180.062 seconds, using 24.59375 seconds of CPU
time. Its first 1000 deductions were independently replayed against the new
input, with no empty clause in that prefix. The full partial trace is preserved
in a lossless archive. These checks establish no new six-count floor.

The next split above is a written deduction from checked premises. Its new
actual-snake assembly remains to be checked in Lean before the next branch
exclusion is claimed.
'''
note.write_text(s,encoding='utf-8',newline='\n')
print('Wrote milestone summary and eight continuation documents.')
