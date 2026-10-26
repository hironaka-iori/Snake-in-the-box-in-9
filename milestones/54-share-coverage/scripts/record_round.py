"""Record the complete coverage experiment and its unchanged global bound."""
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
next_step='Extract all minimum-charge strongly connected components of the strongest exploratory model. Prioritize share patterns covering several components and require ordinary positive controls before spending effort on new share certificates.'
(HERE/'data/checkpoint.json').write_text(json.dumps(dict(status='VERIFIED',lean_modules=2,lean_audits=8,finite_analyses=len(r['models']),
    round_after_revision=8,manuscript_revision_due=56,paper_sha256=digest,previous_round_commit=refs['HEAD'],
    global_bound=235,paper_bound=236,next_research=next_step),indent=2)+'\n')
checkpoint='Current mathematical checkpoint: [milestone 54](milestones/54-share-coverage/README.md). The four checked empty-square rules raise the full all-known numerical model from count mean 65/16 to charge mean 57/14. Eight further numerical share candidates in both orientations, with five ordinary exclusions discovered during controls, reach 53/13. All edge estimates still round down to 235. Twelve finite analyses have complete transition reconstruction, exact integer potentials and attaining cycles; two Lean modules and eight audits check five-window accounting and reversal. No improved global bound is established. The contributor-checked interval remains **191 <= a(9) <= 235**, with its dependency closure not fully rebuilt locally. The paper still records 236. This is research round 8 of 10 after manuscript revision 46.'
priority='Next research priority: '+next_step+' Empty-square charging remains the selected route. The current thirteen-step minimizing cycle has zero credit under every available rule, so increasing those same constants cannot remove it.'
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;parts=p.read_text(encoding='utf-8').split('\n\n')
    for i,t in enumerate(parts):
        if t.startswith('Current mathematical checkpoint:'):parts[i]=checkpoint
        elif t.startswith('Next research priority:'):parts[i]=priority
    p.write_text('\n\n'.join(parts),encoding='utf-8')
