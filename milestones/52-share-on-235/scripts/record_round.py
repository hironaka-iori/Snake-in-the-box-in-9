"""Record the completed share theorem and the unchanged global bound."""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
assert json.loads((HERE/'data/verification.json').read_text())['status']=='PASS'
refs={r:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',r],cwd=ROOT).decode().strip() for r in ['HEAD','origin/main','origin/research/unconditional-241','origin/claude/relaxed-keller-60ks7i']}
(HERE/'data/repository-check.json').write_text(json.dumps(dict(refs=refs,contributor_checked_bound=235,independent_full_rebuild=False,note='Fetch completed this round; contributor refs unchanged from milestone51.'),indent=2)+'\n')
paper=ROOT/'paper/snake9_research.tex';mirror=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert paper.read_bytes()==mirror.read_bytes();digest=hashlib.sha256(paper.read_bytes()).hexdigest()
assert digest=='8473cbc3bacec85ad88e84ef67f43ccf79a1ec37f8b8ae86b288199e028d7ab9'
(HERE/'data/checkpoint.json').write_text(json.dumps(dict(status='VERIFIED',lean_modules=59,lean_audits=12,round_after_revision=6,manuscript_revision_due=56,paper_sha256=digest,previous_round_commit=refs['HEAD'],global_bound=235,paper_bound=236,next_research='Prioritize share constraints that cover remaining minimum-charge cycles, using contributor count work as input. The unused-bound generalization is a simplification lead and adds no occurrence to the current critical family.'),indent=2)+'\n')
rows=json.loads((HERE/'data/critical-family.json').read_text())['windows'];hits=[r for r in rows if r['directions']==[0,1,2,3,4,5] and [r['counts'][i] for i in [0,2,3]]==[3,2,3]]
(HERE/'data/generalization-impact.json').write_text(json.dumps(dict(matching_windows=hits,occurrences=sum(r['occurrences'] for r in hits),extra_critical_patterns=0,scope='Removing the second/fifth count restrictions adds no pattern to this recorded critical family. This is a finite-model observation, not a proof of the generalized theorem.'),indent=2)+'\n')
checkpoint='Current mathematical checkpoint: [milestone 52](milestones/52-share-on-235/README.md). For six distinct consecutive directions and internal singleton counts (3,A,2,3,B), with 6 <= A,B <= 21, the five integer empty-square shares sum to at least 96. All 59 Lean modules and 12 dependency audits pass, including arbitrary coordinate labels. The ordinary local model has a positive witness, so the result supplies share information beyond a count exclusion. Four finite-model means remain 4; no new global bound is established. The contributor-checked interval is **191 <= a(9) <= 235**, with its completed theorem and saved audit reviewed but not fully rebuilt locally. The paper still records the previous 236 bound. This is research round 6 of 10 after manuscript revision 46.'
priority='Next research priority: cover the remaining minimum-charge cycles with empty-square constraints, using the contributors\' count results as input. The retained 235 estimate gives 39m + 2s0 <= 9200, so 18 empty squares suffice for 234; Lean checks this implication under the stated hypotheses. A core inspection suggests removing the new theorem\'s second/fifth count restrictions, but this alone adds no occurrence in the current critical family. Occurrence frequency and complete graph-to-snake accounting remain unresolved.'
for name in ['README.md','COLLABORATION.md']:
 p=ROOT/name;paragraphs=p.read_text(encoding='utf-8').split('\n\n')
 for i,t in enumerate(paragraphs):
  if t.startswith('Current mathematical checkpoint:'):paragraphs[i]=checkpoint
  elif t.startswith('Next research priority:'):paragraphs[i]=priority
 p.write_text('\n\n'.join(paragraphs),encoding='utf-8')
