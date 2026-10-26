"""Pin reviewed contributor evidence and refresh the research handoff."""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
def git(*args):return subprocess.check_output(['git','-c','core.commitGraph=false',*args],cwd=ROOT)
refs={r:git('rev-parse',r).decode().strip() for r in ['HEAD','origin/main','origin/research/unconditional-241','origin/claude/relaxed-keller-60ks7i']}
ref=refs['origin/research/unconditional-241'];records=[]
for path in ['work/spectral/stronger/UpperBound235.lean','work/spectral/stronger/AggregateDirection6K235.lean','work/spectral/stronger/AggregateDirection6Conditional.lean','outputs/upper-bound-235-audit-linux.log','outputs/upper-bound-235-replay-linux.log','milestones/25-k7-234/README.md']:
 b=git('show',ref+':'+path);dest=HERE/'data/contributor'/Path(path).name;dest.parent.mkdir(exist_ok=True);dest.write_bytes(b)
 records.append(dict(path=path,snapshot=dest.relative_to(HERE).as_posix(),sha256=hashlib.sha256(b).hexdigest()))
(HERE/'data/repository-check.json').write_text(json.dumps(dict(refs=refs,files=records,latest_235_status='Completed contributor theorem and standard-axiom audit inspected at b20346ee / 74ca83db. Full dependency closure not independently rebuilt locally.',integrated_manuscript_bound=236,contributor_checked_bound=235),indent=2)+'\n')
checkpoint='Current mathematical checkpoint: [milestone 51](milestones/51-exact-bucket-pressure/README.md). The chosen route is empty-square charging. A genuine five-centre share lower bound of 48 now passes 26 Lean modules and 14 dependency audits, including its interpretation for arbitrary coordinate labels. Seventeen numerical share bounds of 96 improve a conditional finite-model mean to 35/9, still insufficient for a new global bound. The contributor branch now has a completed 235 theorem and successful saved Lean audit; those sources and logs were inspected and pinned, without independently rebuilding the full closure. The repository paper still records 191 <= a(9) <= 236; the contributor-checked interval is **191 <= a(9) <= 235**. This is research round 5 of 10 after manuscript revision 46.'
priority='Next research priority: strengthen and cover empty-square share bounds on the surviving critical windows, then include them in a complete charge argument. Compare against the contributor\'s completed 235 baseline and target 234. The count-only sweep has stopped; its completed stages supply the input graph. The local bound 48 is checked; 96 and the exploratory graph exclusions remain numerical premises. A global occurrence or finite-state coverage argument is still required.'
for name in ['README.md','COLLABORATION.md']:
 p=ROOT/name;s=p.read_text(encoding='utf-8');paragraphs=s.split('\n\n')
 for i,t in enumerate(paragraphs):
  if t.startswith('Current mathematical checkpoint:'):paragraphs[i]=checkpoint
  elif t.startswith('Next research priority:'):paragraphs[i]=priority
  elif t.startswith('Latest GitHub refresh (25 October):'):paragraphs[i]='Latest GitHub refresh (26 October): `research/unconditional-241` is at `74ca83db`. The 635 new replay roots and the aggregate theorem for 235 are complete, with a saved standard-axiom audit at `b20346ee`. This replaces the previous unfinished status. The seven-centre framework aimed at 234 remains conditional; no completed 234 theorem was found in the reviewed update. The local review and exact snapshots are in milestone51/data/repository-check.json.'
 s='\n\n'.join(paragraphs).replace('The default five-round revision cadence resumes from this checkpoint.','The current revision cadence is ten research rounds; the next scheduled rewrite is milestone 56.')
 p.write_text(s,encoding='utf-8')
