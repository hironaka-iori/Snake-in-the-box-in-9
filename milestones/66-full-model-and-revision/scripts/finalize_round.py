"""Record checked evidence and update the collaborator entry points."""
from pathlib import Path
import hashlib,json,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git','-c','core.commitGraph=false',*args],cwd=ROOT).decode('utf-8').strip()
paper=ROOT/'paper/snake9_research.tex';mirror=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert paper.read_bytes()==mirror.read_bytes()
verify=read(HERE/'data/paper-verification.json');audit=read(HERE/'data/lean-audit.json')
assert verify['status']=='PASS' and verify['paper_sha256']==sha(paper)
assert audit['status']=='PASS' and audit['modules']==3 and audit['theorem_audits']==16
compiled=read(HERE/'data/editor-compile.json')
messages=[json.loads(x['text']) for x in compiled['content'] if x.get('type')=='text']
assert any(x.get('kind')=='success' for x in messages)
for name in ['model-verification','pressured-verification']:assert read(HERE/f'data/{name}.json')['status']=='PASS'
ref=git('rev-parse','origin/research/unconditional-241');assert ref.startswith('852209db')
snapshots=[]
for source,dest in [('milestones/25-k7-234/README.md','contributor-234-update.md'),('milestones/25-k7-234/data/cost234_best.json','contributor-234-cost.json')]:
    data=subprocess.check_output(['git','-c','core.commitGraph=false','show',f'{ref}:{source}'],cwd=ROOT)
    (HERE/'data'/dest).write_bytes(data);snapshots.append(dict(source=source,snapshot=dest,sha256=hashlib.sha256(data).hexdigest()))
record=dict(date='2026-10-29',head_before_commit=git('rev-parse','HEAD'),origin_main=git('rev-parse','origin/main'),
    contributor_ref=ref,snapshots=snapshots,paper_sha256=sha(paper),editor_sha256=sha(mirror),
    contributor_assessment='Reduced proposed 234 key set: 11,167 keys, 1.733 billion estimated hints. Solver/Python cost study, no completed Lean proof of 234. Global bound remains 235.',
    literature_checked=['https://arxiv.org/abs/2607.15270','https://oeis.org/A099155'],
    literature_assessment='Current arXiv v3 still reports length 191 in dimension nine; OEIS lists exact values through eight.',
    compile='Desktop editor compiler succeeded after one stale-project response.',visual_inspection='Not performed; no replacement PDF generated.')
(HERE/'data/repository-check.json').write_text(json.dumps(record,indent=2)+'\n')
revision=read(HERE/'data/paper-revision.json');revision.update(verification='PASS',compile='success',visual_inspection=False)
(HERE/'data/paper-revision.json').write_text(json.dumps(revision,indent=2)+'\n')
checkpoint=('Current mathematical checkpoint: [milestone 66](milestones/66-full-model-and-revision/README.md). '
    'The checked terminal-count restriction raises the complete recorded model\'s integer minimum from 9891/20 to **18823/38** (normalized **18823/4560**). '
    'Independent verification covers all 13,173,896 transitions of the final history model. Eight share patterns strengthen 175,293 transitions; three count restrictions exclude 17,161 lifted transitions. '
    'The complete remaining minimum-mean family has **70 states and 99 transitions**. Two new arbitrary-snake count bounds and six arithmetic deductions passed 3 Lean modules and 16 audits. '
    'The conditional integer estimate remains 235, and the contributor-checked global interval remains **191 <= a(9) <= 235**. Inherited numerical premises and the full graph-to-snake assembly remain unfinished. '
    'Contributor revision `852209db` reduces the estimated cost of its proposed 234 proof, but does not complete it.')
manuscript=('Current manuscript revision: [milestone 66](milestones/66-full-model-and-revision/README.md). '
    'The paper now develops forced-absence shares, exhaustive neighbour choices, count saturation, three direct count restrictions, arbitrary-length boundary accounting and complete-model history in logical order. '
    'The earlier zero-credit model is retained in an appendix. All 108 prior mathematical statements are preserved, with one historical referent clarified; eight new statements bring the total to 116. '
    'All thirteen printed snakes pass 118,673 pair checks, and all 164 labels and references resolve. '
    'The existing editor and repository sources are synchronized, with authors and hyperlink settings unchanged. The desktop editor compiler succeeded; rendered-page visual inspection was not performed.')
nextstep=('Next research priority: Derive stronger empty-square share inequalities across the entire 70-state, 99-transition critical family, then test their effect in the complete model. '
    'Recovering the omitted ambiguous share pattern requires additional direction history or a proof valid for both compatible shapes. '
    'Manuscript revision 66 completes the ten-round cycle after revision 56. The next full paper rewrite is scheduled for milestone 76.')
for name in ['README.md','COLLABORATION.md','WORKSPACE.md']:
    p=ROOT/name;parts=p.read_text(encoding='utf-8').split('\n\n')
    for i,paragraph in enumerate(parts):
        if paragraph.startswith('Current mathematical checkpoint:'):parts[i]=checkpoint
        elif paragraph.startswith('Current manuscript revision:'):parts[i]=manuscript
        elif paragraph.startswith('Next research priority:'):parts[i]=nextstep
    p.write_text('\n\n'.join(parts),encoding='utf-8')
ledger=ROOT/'RESEARCH_LEDGER.md';entry='## Milestone 66: complete-model integration and manuscript revision'
assert entry not in ledger.read_text(encoding='utf-8')
with ledger.open('a',encoding='utf-8') as f:
    f.write('\n\n'+entry+'\n\n'+checkpoint.split('). ',1)[1]+'\n\n'+manuscript.split('). ',1)[1]+'\n\n'+nextstep+'\n')
p=HERE/'README.md';s=p.read_text(encoding='utf-8')
a=s.index('**In progress.**');b=s.index('\n\n## Complete-model effect',a)
s=s[:a]+('**Completed research round and manuscript revision.** The existing paper integrates rounds 57–66 and compiles successfully in the desktop editor. '
    'The new local count proofs and arithmetic passed 3 Lean modules and 16 theorem audits. All previous mathematical statements and witnesses are preserved; the paper has 116 statements and 164 labels. '
    'The global optimum remains unresolved, and no new universal upper bound is claimed.')+s[b:]
a=s.index('Before completing this round:')
s=s[:a]+('The manuscript rewrite is complete. Its source and existing editor mirror are identical, with the three authors and hyperlink settings preserved. '
    'The source audit verifies all 108 prior statements, eight additions and all thirteen printed snakes (118,673 pair checks). '
    'The desktop editor compiler succeeded after one stale-project response. Rendered pages have not been visually inspected, and no replacement PDF was generated. '
    'The current source hash is `'+sha(paper)+'`. See `data/paper-verification.json`, `data/editor-compile.json`, `data/lean-audit.json` and `data/repository-check.json`.\n\n'
    'This completes the ten-round cycle after manuscript revision 56. The next scheduled full rewrite is milestone 76. '
    'The next mathematical task is to strengthen shares over the complete remaining critical family, including alternatives to a single displayed cycle.\n')
p.write_text(s,encoding='utf-8');print(json.dumps(record,indent=2))
