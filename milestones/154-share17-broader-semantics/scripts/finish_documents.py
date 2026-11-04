"""Preserve the checked implication and the remaining single contradiction."""
from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
j=read(H/'data/semantics-completion.json')
assert j['status']=='PASS_BROADER_CORE_SEMANTICS_AND_CONDITIONAL_ACTUAL_SNAKE_SHARE17'
assert read(H/'data/paper-source-review.json')['status']=='PASS_TARGETED_PAPER_SOURCE_CHECKS'
assert j['checked_modules']==98 and j['core_unsat_is_explicit_premise']
protected=read(R/'milestones/152-countfree-share16-completion/data/completion-checkpoint.json')['protected_unrelated_files_sha256']
for p,d in protected.items():assert sha(R/p)==d,p
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
base=subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()
assert base=='1069c2a32aaa9be26f7f10eb6efb282f0063f8dc'
intro='''# Research update: broader critical-window interpretation checked

All 98 modules interpreting the shared share-17 certificate and transferring
it to actual snakes have passed Lean. The count conditions are alpha1=4,
alpha2<=4, alpha3=4, alpha4<=5 and alpha5=3, with reversed conditions for
reversed canonical directions. The contradiction remains an explicit
premise. The final share-17 theorem and any new global bound remain pending.

The universal 012032 share-16 theorem is complete in milestone 152. Next,
run the single share-17 replay in milestone 155, audit its pilot, then emit
and check the full contradiction and compose the actual-snake consequence.
Inspect live processes before starting another compiler. Use the v2 native
resource scripts. The original CIM monitor was delayed during a low-memory
event; its failed run and all accepted source bytes are preserved.

Broadening adds 100 source-graph rows and no retained rows. The retained
pair-sum condition forces the two relaxed counts back to 4 and 5. The
eleven-cycle still has two target edges. Last full paper revision: 146;
next: 156. Historical updates follow.

'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md',
             'handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']:
    p=R/name;p.write_bytes(intro.encode('utf-8')+p.read_bytes())
(H/'MATHEMATICAL_NOTE.md').write_text(intro+'''The 98 accepted modules include the shared clause source, the broader
nine-counter interpretation, all 93 clause checks, their assembly and
coordinate/reversal transport. Their exact source, object, log, dependency
and permitted-axiom receipts were audited. Lean and external mathematics
libraries remain trusted; reused coordinate machinery includes the recorded
historical data object. The only unresolved local-proof step is the complete
contradiction and its composition with the checked implication.

The graph inventory is separate numerical evidence. Under its saved removal
hypotheses the relaxed counts have sum at least 9 and respective upper
bounds 4 and 5, so they equal 4 and 5. The two matching eleven-cycle suffix
edges would each gain one if share 17 is established. Relative to the
universal share-16 profile this changes its total from 5456 to 5458.
The fourteen-cycle remains unchanged. No new potential is certified.

Milestone155 prepares the single 34-module initial-tree pilot and a guarded
full-source generator. The full numerical proof contains 30,305 deductions
and 1,754,767 references. Pilot acceptance does not establish the complete
contradiction. The original exact153 semantic modules are unnecessary
dependencies for this broader interpretation.

The maintained project interval remains 191--235, using the contributor
upper theorem whose complete independent rebuild remains pending. The
conditional234 route retains four other local targets plus reference and
potential obligations. The value196 and the optimum remain unresolved.
''',encoding='utf-8',newline='\n')
p=H/'README.md';text=p.read_text()
text=text.replace('Status: prepared source only. No Lean compiler or solver was launched for this milestone.',
    'Status: all 98 modules passed Lean. The complete contradiction remains pending. Read MATHEMATICAL_NOTE.md and data/semantics-completion.json.')
text=text.replace('1. Check the shared CNF module and all 97 new source modules in Lean.',
    '1. The shared CNF module and all 97 new source modules passed Lean.')
text=text.replace('No prepared theorem is reported as accepted by Lean.',
    'The implication is checked; the share-17 bound under only the stated counts remains pending.')
p.write_text(text,encoding='utf-8',newline='\n')
record=dict(status='PASS_BROADER_SEMANTICS_REPLAY_PENDING_CHECKPOINT',base_commit=base,
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),checked_modules=98,
    axiom_reports=j['axiom_reports'],core_clauses=11869,counters=9,
    complete_contradiction_checked=False,actual_snake_share17_complete=False,new_global_upper_bound=False,
    current_interval=[191,235],conditional234_other_premises_unchanged=True,
    semantics_completion_sha256=sha(H/'data/semantics-completion.json'),
    paper_sha256=sha(R/'paper/snake9_research.tex'),
    pdf_rebuilt=read(H/'data/paper-source-review.json')['pdf_rebuilt'],
    last_full_paper_revision=146,next_full_paper_revision=156,goal_status='ACTIVE',
    protected_unrelated_files_sha256=protected)
target=H/'data/checkpoint.json';assert not target.exists()
target.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record))
