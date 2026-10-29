from pathlib import Path
import subprocess,json,hashlib
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
def git(*args):return subprocess.check_output(['git','-c','core.commitGraph=false',*args],cwd=ROOT).decode('utf-8').strip()
ref=git('rev-parse','origin/research/unconditional-241')
paths=['milestones/25-k7-234/lean/README.md','work/spectral/stronger/UpperBound234.lean']
snapshots=[]
for i,path in enumerate(paths):
    data=subprocess.check_output(['git','-c','core.commitGraph=false','show',f'{ref}:{path}'],cwd=ROOT)
    dest=HERE/'data'/('contributor-234-status.md' if i==0 else 'contributor-234-source.txt')
    dest.write_bytes(data);snapshots.append(dict(path=path,snapshot=dest.name,sha256=hashlib.sha256(data).hexdigest()))
paper=ROOT/'paper/snake9_research.tex';mirror=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(paper)==digest(mirror)
record=dict(date='2026-10-29',head_before_checkpoint=git('rev-parse','HEAD'),origin_main=git('rev-parse','origin/main'),
    contributor_ref=ref,snapshots=snapshots,paper_sha256=digest(paper),mirror_sha256=digest(mirror),
    assessment='234 remains conditional: the contributor reports scratch sorry stubs in final composition tests; 36,841 new keys and 792 graph shards remain incomplete. The reused-window glue is checked. No new global bound adopted.')
(HERE/'data/repository-check.json').write_text(json.dumps(record,indent=2)+'\n')
checkpoint=('Current mathematical checkpoint: [milestone 65](milestones/65-count-saturation-share/README.md). '
    'Nine stronger count-conditioned empty-square share bounds and a direct terminal singleton-count restriction passed 17 Lean modules and 104 theorem-dependency audits. '
    'Independent reconstruction checked 479 branch certificates and 217 propagation steps. The share-only restricted minimum is **9961/2400**, up by **1/400**. '
    'The direct count restriction excludes one transition shared by every cycle of the saved critical family; after its removal the 118-state, 217-transition graph has maximum walk length **19**. '
    'This is a restricted-family result, and the contributor-checked interval remains **191 <= a(9) <= 235**. The 109 other candidate exclusions are not certified. '
    'The 29 October contributor update at `838303ae` still uses placeholder proofs in its final 234 composition test; its unfinished certificate and graph checks prevent adoption of 234.')
nextstep=('Next research priority: Integrate the direct terminal-count restriction into the complete direction/count model with sufficient history, recompute its potential, and account for all boundary losses. '
    'The new shares must be combined with inherited shares by taking their maximum on the same centres. '
    'This is research round **9 of 10** after manuscript revision 56; the next full paper rewrite is milestone 66. The paper and existing editor mirror remain unchanged and synchronized.')
for name in ['README.md','COLLABORATION.md','WORKSPACE.md']:
    path=ROOT/name;s=path.read_text(encoding='utf-8');parts=s.split('\n\n')
    for i,p in enumerate(parts):
        if p.startswith('Current mathematical checkpoint:'):parts[i]=checkpoint
        elif p.startswith('Next research priority:'):parts[i]=nextstep
    path.write_text('\n\n'.join(parts),encoding='utf-8')
ledger=ROOT/'RESEARCH_LEDGER.md'
with ledger.open('a',encoding='utf-8') as f:
    f.write('\n\n## Milestone 65: count saturation and empty-square shares\n\n'
        'Nine arbitrary-snake share improvements and a direct terminal count lower bound three passed 17 Lean modules and 104 audits. '
        'All 479 compact branch certificates and 217 deduction steps pass independent reconstruction. '
        'Shares alone give the restricted minimum 9961/2400. The direct exclusion of transition 24 removes every cycle of the saved family, whose longest remaining walk is 19. '
        'No global upper bound follows from this restricted graph. GitHub refresh to contributor 838303ae confirms unfinished certificates and shards in the proposed 234 chain; the recorded upper bound stays 235. '
        'Research round 9 of 10 since revision 56; integrate the restriction into the complete model and rewrite the paper at milestone 66.\n')
print(json.dumps(record,indent=2))
