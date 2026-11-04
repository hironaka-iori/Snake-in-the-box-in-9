"""Preserve the completed numerical work and explicitly pending Lean work."""
from pathlib import Path
import datetime, hashlib, json, subprocess, zipfile
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
base=subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()
assert base=='2dcd39bcb6eec4658322b85d354c5b5b73255050'
reviews={
 'pair-query-and-cycle-review.json':'1a28c70810fcb802a255d253e6d86e010ad180af718e2dca4d1caccc7108cda5',
 'critical-certificate-review.json':'8c59096d63ffaea967717b5b6767e3fa6c19847b6838b603cd4454bc63506226',
 'broader-review.json':'55a847c3e5b00f5a1402169f28eca7bf1bd5723dff0a3b046921ff4b87fa6ff9'}
for name,digest in reviews.items():
    path=H/'audit'/name;assert sha(path)==digest
    for p,d in read(path)['source_files_sha256'].items():assert sha(R/p)==d,p
archives=read(H/'data/archives.json');members=0
for item in archives['archives']:
    path=H/item['path'];assert sha(path)==item['sha256']
    with zipfile.ZipFile(path) as z:
        assert set(z.namelist())=={x['path'] for x in item['members']}
        for row in item['members']:
            data=z.read(row['path'])
            assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
            assert sha(H/row['path'])==row['sha256'];members+=1
assert members==46
broader=read(H/'broader/verification.json')
assert broader['status']=='PASS_BROADER_CONDITIONS_NATIVE_RUP_REPLAY'
assert broader['compact_core_identical'] and broader['replay']['final_empty_clause_checked']
assert (broader['core_clauses'],broader['deductions'],broader['hints'])==(11869,30305,1754767)
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert paper.read_bytes()==editor.read_bytes()
assert sha(paper)==read(H/'data/paper-source-review.json')['source_sha256']
protected=read(R/'milestones/152-countfree-share16-completion/data/checkpoint.json')['protected_unrelated_files_sha256']
for p,d in protected.items():assert sha(R/p)==d,p
recovery=read(R/'milestones/152-countfree-share16-completion/data/reboot-recovery-v2-progress.json')
assert recovery['status'] in ['CHECKING_REMAINING_REPLAY','AUDITING_COMPLETE_REPLAY','CHECKING_ACTUAL_SNAKE_CONSEQUENCE','PASS_RECOVERED_ACTUAL_SNAKE_COMPOSITION']
intro='''# Research update: milestone 153

A complete numerical certificate supports the 012032 share-17 target under
counts alpha1=4, alpha2<=4, alpha3=4, alpha4<=5, alpha5=3, with reversal.
Removing two unused lower-bound counters preserves the compact core and
every compact proof step. Lean verification and the actual-snake theorem
remain pending. The exact evidence and remaining work are recorded in
milestones/153-pair-conditioned-share17/MATHEMATICAL_NOTE.md.

The computer restarted after the user pause. The old 151/152/147 processes
are absent. Recovery revalidates 301 accepted universal-share modules and
continues at the first unchecked one. Read the live recovery record at
milestones/152-countfree-share16-completion/data/reboot-recovery-v2-progress.json;
do not launch another replay or rely on the historical RUNNING records.
After it passes, audit the reboot recovery and use
`152-countfree-share16-completion/scripts/update_paper_after153.py`.
The 147 proof retains its accepted files; reschedule it after this check.

No new global bound is established. Last full paper revision: 146; next: 156.
Historical updates below describe their original checkpoints.

'''
names=['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md',
       'handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']
for name in names:
    previous=subprocess.check_output(g+['show',base+':'+name],cwd=R)
    (R/name).write_bytes(intro.encode('utf-8')+previous)
note=H/'MATHEMATICAL_NOTE.md';text=note.read_text(encoding='utf-8')
start=text.index('The ongoing universal 012032 share 16 job remains the immediate priority.')
end=text.index('\n## Consequence and limitations',start)
text=text[:start]+'''The universal 012032 share-16 check remains the immediate priority.
The computer restarted after the user pause, ending all old verification
processes. Recovery now revalidates the 301 accepted modules and continues
from the first unchecked module. Inspect the recovery record in milestone
152 before launching a compiler. The old hold and queued-continuation
records are preserved historical evidence. After the recovered final
composition passes, audit that recovery and use
`152-countfree-share16-completion/scripts/update_paper_after153.py`.
The 147 replay must be scheduled separately after the current compiler
finishes; its accepted files remain available.
'''+text[end:]
note.write_text(text,encoding='utf-8',newline='\n')
record=dict(status='PASS_NUMERICAL_SHARE17_CERTIFICATES_LEAN_PENDING',
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),base_commit=base,
    bounds=broader['bounds'],directions=[0,1,2,0,3,2],target_share=17,resolution=12,
    core_clauses=11869,deductions=30305,propagation_references=1754767,
    compact_core_and_proof_identical=True,removed_lower_counter_registers=693,
    exact_semantic_modules_prepared=97,pilot_modules_prepared=34,
    Lean_modules_checked=0,actual_snake_theorem_complete=False,new_global_upper_bound=False,
    archives=4,archive_members=members,independent_reviews_sha256=reviews,
    current_interval=[191,235],interval_scope='Maintained contributor result; complete independent rebuild pending.',
    conditional234_other_premises_unchanged=True,paper_sha256=sha(paper),pdf_rebuilt=False,
    goal_status='ACTIVE',last_full_paper_revision=146,next_full_paper_revision=156,
    next='Broader nine-counter interpretation of the same compact core; one pilot, one complete contradiction, direct/reverse snake transfer.',
    protected_unrelated_files_sha256=protected)
target=H/'data/checkpoint.json';assert not target.exists()
target.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record))
