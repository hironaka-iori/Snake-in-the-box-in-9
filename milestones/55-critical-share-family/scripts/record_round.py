"""Record the checked share theorem and its precisely limited finite-model effect."""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
r=json.loads((HERE/'data/verification.json').read_text());assert r['status']=='PASS'
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT).decode().strip()
      for ref in ['HEAD','origin/main','origin/research/unconditional-241','origin/claude/relaxed-keller-60ks7i']}
(HERE/'data/repository-check.json').write_text(json.dumps(dict(refs=refs,contributor_checked_bound=235,independent_full_rebuild=False),indent=2)+'\n')
paper=ROOT/'paper/snake9_research.tex';mirror=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert paper.read_bytes()==mirror.read_bytes();digest=hashlib.sha256(paper.read_bytes()).hexdigest()
assert digest=='8473cbc3bacec85ad88e84ef67f43ccf79a1ec37f8b8ae86b288199e028d7ab9'
next_step='Examine the replacement minimum-charge family of mean 102/25 and prioritize share inequalities covering that family. Complete the tenth research round, then rewrite the paper with the 235 contributor result, checked local theorems, and unresolved global dependencies distinguished.'
(HERE/'data/checkpoint.json').write_text(json.dumps(dict(status='VERIFIED',lean_modules=r['lean_modules'],lean_audits=r['lean_audits'],
    round_after_revision=9,manuscript_revision_due=56,paper_sha256=digest,previous_round_commit=refs['HEAD'],
    global_bound=235,paper_bound=236,next_research=next_step),indent=2)+'\n')
p=HERE/'README.md';text=p.read_text(encoding='utf-8').replace('Verification in progress.',
    f"Verification complete: {r['lean_modules']} Lean modules and {r['lean_audits']} dependency audits pass; see `data/verification.json`.")
p.write_text(text,encoding='utf-8')
checkpoint=f"Current mathematical checkpoint: [milestone 55](milestones/55-critical-share-family/README.md). Directions (a,b,c,d,a,e) and internal singleton counts (A,B,2,2,C), with 6 <= A,B,C <= 21, force five integer empty-square shares to sum to at least 96. The arbitrary-coordinate and reversed-window statements are Lean checked. A separate rank certificate shows this pattern meets every cycle of the recorded 57-state, 83-edge critical component. All {r['lean_modules']} modules and {r['lean_audits']} audits pass. The exploratory minimum rises from 53/13 to 102/25; its edge estimate still rounds down to 235. The contributor-checked interval remains **191 <= a(9) <= 235**, with its dependency closure not fully rebuilt locally. The paper still records 236. This is research round 9 of 10 after manuscript revision 46."
priority='Next research priority: '+next_step+' Empty-square charging remains the selected route.'
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;parts=p.read_text(encoding='utf-8').split('\n\n')
    for i,t in enumerate(parts):
        if t.startswith('Current mathematical checkpoint:'):parts[i]=checkpoint
        elif t.startswith('Next research priority:'):parts[i]=priority
    p.write_text('\n\n'.join(parts),encoding='utf-8')
