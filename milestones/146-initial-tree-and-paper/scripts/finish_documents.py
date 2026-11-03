"""Save current status, retaining earlier records and exact source bytes."""
from pathlib import Path
import datetime, json, subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
assert read(H/'data/bridge-completion.json')['status']=='PASS_ORIGINAL_CNF_TO_INITIAL_TREE_AND_CHECKED_PREFIX'
paper=read(H/'data/paper-source-review.json')
assert paper['status']=='PASS_SOURCE_STRUCTURE_AND_PRESERVED_CONTENT'
semantic=read(H/'data/semantic-progress.json')
assert semantic['status']!='RUNNING' and semantic['active'] is None
assert not (H/'data/semantic-batch.lock').exists()
checked=len(semantic['checked_modules'])
pilot_detail=('The pilot covers encoded input, data and counter structure; all 102\nconcrete clause checks remain pending.' if checked==3 else 'The exact checked modules and any failure are listed in the progress record.')
summary=f'''# Research update: milestone 146

The original-clause-to-initial-tree check is complete. Three Lean modules
with four accepted axiom reports connect all 104 chunks of the preserved
share-18 certificate to its initial tree and the checked prefix of 1,055
deductions and 6,006 propagation references. The full share proof remains
unfinished; no new global bound is claimed.

The full paper revision is saved in the open editor and repository. It
places proved results before current conditional comparisons and retains
earlier work in appendices. Mathematical statements, displayed formulas,
witnesses and original references survive; one proof gains an explicit
short-path case. Authors and the complete preamble are unchanged. Source
checks pass. The built-in compiler failed before TeX; no new PDF is verified.

The exact 012301 share-16 interpretation is prepared in 105 modules;
{checked} have accepted receipts at this checkpoint. Read the semantic progress
record for the remaining work. {pilot_detail}
The immediate target is this local theorem,
with the 012032 and 012340 requirements retained jointly. The completed
1,397-module 012310 count proof must not be restarted.

Maintained interval 191--235, contributor rebuild caveat and conditional 234
premises are unchanged. The optimum and 196 remain unresolved. Goal ACTIVE.
Read [the complete checkpoint](milestones/146-initial-tree-and-paper/MATHEMATICAL_NOTE.md).
Last full paper revision: 146. Next scheduled full revision: 156.
'''
def write(p,s):p.write_text(s,encoding='utf-8',newline='\n')
write(H/'README.md',summary.replace('(milestones/146-initial-tree-and-paper/MATHEMATICAL_NOTE.md)','(MATHEMATICAL_NOTE.md)'))
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
    p=R/name;old=p.read_text(encoding='utf-8');assert not old.startswith('# Research update: milestone 146'),name
    local=summary.replace('(milestones/146','(../milestones/146') if '/' in name else summary
    write(p,local+'\n## Earlier record\n\n'+old)
write(R/'handoff/NEXT_AGENT_PROMPT.md','''# Continue after milestone 146

Work in E:/Snake-in-a-box. Apply tensai-bishoujo with the user's formal
tone, no emojis and only necessary recurring definitions. Keep the open
paper D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and repository
mirror synchronized. Preserve authors Iori Hironaka, Tommy Ma, Steven Zhan
and the entire preamble. Leave unrelated .gitignore and milestone50
critical-family edits intact. Goal ACTIVE; round146 made progress.
Full revision146 is complete; next156. Do not repeat completed work.

Read milestones/146-initial-tree-and-paper/MATHEMATICAL_NOTE.md and
data/checkpoint.json, data/semantic-progress.json and data/verification.json.
RawChunksAssoc146, AssemblyAssoc146 and PrefixAssoc146 passed with four
standard axiom reports. Original144 core-CNF truth transfers through104
chunks to the exact initial tree and its1055-deduction/6006-reference prefix.
The constructor body is unchanged; extraction normalizes conjunction
association once. Preserve failed144/145 and first146 attempts. Full
share18 replay, contradiction and actual-snake transfer remain unfinished.

Selected task: complete count-free012301 share16 in both orientations.
145 direct replay checked285541 deductions,31017505 references and12977
core clauses, including six induced-eight-cycle exclusions.146 semantic
plan pins105 modules, original clause IDs and all proof variables. Follow
current semantic-progress rather than assuming the pilot completed all.
Respect the import-support manifest. No semantic pilot alone proves
unsatisfiability or the actual share bound. Complete the clause
interpretation, bounded full Lean replay, cycle clauses, coordinate
transport and reversal. Preserve the original proof and failed records.

The012310 five-count theorem has no extra count, parity or endpoint premise.
All1397 modules finished and were audited in145; do not restart its driver.

145 two-cycle obstruction: other weights and graph fixed,012301/012340
floors at most16 plus arbitrary existing credit cannot bring comparison
below235. Lower bound551875/2348; necessary325F+159G>9074. The012032
floor16 increases the eleven-cycle total by57 and changes that hypothesis.
Keep all three targets explicit. A saved-cycle relaxation or restricted
Boolean model gives no global theorem alone. Maintained191--235 uses the
archived contributor upper proof; complete independent rebuild is pending.
Conditional234 retains local-share, reference and potential-certificate
premises.196 and optimum are unresolved. Keep the goal ACTIVE.

Use exact source/object/log/checker/dependency pins and accepted axioms only.
Inspect current processes before resuming one completion driver. Lean gate
free>=1.5GiB, at most2 existing Lean processes; own-process limit3GiB and
free-memory floor768MiB. Current semantic pilot may require zero existing
Lean processes. Fullgraph requires>=3GiBfree and no other fullgraph job.

Paper source checks pass; built-in compilation failed before TeX due to
Windows restricted-token helper configuration. Save exact diagnostics
after future edits; no rebuilt PDF is verified. Keep the editor open.
Fetch each round, stage only manifest files, commit quietly, push and verify
origin/main. Publication receipts belong under work/. Preserve audited bytes.
''')
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
repo=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    head=subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip(),
    remote_tips=subprocess.check_output(g+['for-each-ref','--format=%(refname) %(objectname)','refs/remotes/origin'],cwd=R,text=True))
write(H/'data/repository-final-check.json',json.dumps(repo,indent=2)+'\n')
print(json.dumps(dict(status='SAVED_CURRENT_DOCUMENTS',semantic_modules_checked=checked,paper_sha256=paper['source_sha256'])))
