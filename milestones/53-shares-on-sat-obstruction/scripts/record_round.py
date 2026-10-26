"""Record checked local share results without upgrading them to a global bound."""
from pathlib import Path
import hashlib, json, subprocess

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
receipt = json.loads((HERE/'data/verification.json').read_text())
assert receipt['status'] == 'PASS'
refs = {r: subprocess.check_output(['git', '-c', 'core.commitGraph=false', 'rev-parse', r], cwd=ROOT).decode().strip()
        for r in ['HEAD', 'origin/main', 'origin/research/unconditional-241', 'origin/claude/relaxed-keller-60ks7i']}
(HERE/'data/repository-check.json').write_text(json.dumps(dict(refs=refs, contributor_checked_bound=235,
    independent_full_rebuild=False, note='Contributor result is a reviewed baseline; this round adds two local share theorems.'), indent=2)+'\n')
paper = ROOT/'paper/snake9_research.tex'
mirror = Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert paper.read_bytes() == mirror.read_bytes()
digest = hashlib.sha256(paper.read_bytes()).hexdigest()
assert digest == '8473cbc3bacec85ad88e84ef67f43ccf79a1ec37f8b8ae86b288199e028d7ab9'
next_step = 'Insert the two verified share constraints into surviving finite models, use sound overlap accounting, and identify replacement minimum-charge cycles. Complete the run-to-snake bridge before claiming the conditional thirteen-block exclusion for actual snakes.'
(HERE/'data/checkpoint.json').write_text(json.dumps(dict(status='VERIFIED', lean_modules=receipt['lean_modules'],
    lean_audits=receipt['lean_audits'], round_after_revision=7, manuscript_revision_due=56,
    paper_sha256=digest, previous_round_commit=refs['HEAD'], global_bound=235, paper_bound=236,
    next_research=next_step), indent=2)+'\n')
checkpoint = 'Current mathematical checkpoint: [milestone 53](milestones/53-shares-on-sat-obstruction/README.md). Two additional five-centre empty-square share bounds of 96 are checked in Lean, including arbitrary coordinate labels: directions (a,b,c,a,d,e) with counts (A,3,B,3,3), and six distinct directions with counts (4,A,2,3,B), where 6 <= A,B <= 21. All 203 modules and 19 audits pass. On the saved sixteen-step SAT obstruction, disjoint forward occurrences raise its conditional normalized charge from 65/16 to 73/16. A finite-block summation lemma accounts for the boundary loss. No new global upper bound is established. The contributor-checked interval is **191 <= a(9) <= 235**, with its theorem and saved audit reviewed but not fully rebuilt locally. The paper still records 236. This is research round 7 of 10 after manuscript revision 46.'
priority = 'Next research priority: '+next_step+' The focus remains empty-square charging. A share-87 local witness refutes a uniform share96 claim for every window of the saved obstruction, so further bounds must distinguish the patterns.'
for name in ['README.md', 'COLLABORATION.md']:
    path = ROOT/name
    paragraphs = path.read_text(encoding='utf-8').split('\n\n')
    for i, paragraph in enumerate(paragraphs):
        if paragraph.startswith('Current mathematical checkpoint:'):
            paragraphs[i] = checkpoint
        elif paragraph.startswith('Next research priority:'):
            paragraphs[i] = priority
    path.write_text('\n\n'.join(paragraphs), encoding='utf-8')
