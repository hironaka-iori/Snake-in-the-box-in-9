"""Measure candidate bound pressure before investing in proof replay.

UNSAT rows here are solver results, so this graph is exploratory.
"""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model,analyze
np=model.np
target=HERE/'screen';(target/'data').mkdir(parents=True,exist_ok=True);(target/'build').mkdir(exist_ok=True)
meta=json.loads((HERE/'data/model.json').read_text());rows=json.loads((HERE/'data/critical-survey.json').read_text())
assert len(rows)==381,'Do not analyse an unfinished survey.'
rules=[r for r in rows if r['status']=='UNSAT']
with np.load(HERE/'build/graph.npz') as z:a={k:z[k].copy() for k in z.files}
extra=np.zeros(len(a['U']),dtype=bool)
for i,ds in enumerate(meta['extensions']):
 mask=a['direction']==i;codes=a['count_code'][mask];bad=np.zeros(len(codes),dtype=bool)
 for start in range(3):
  piece=ds[start:start+6]
  for rev in [False,True]:
   canon=model.canon(piece[::-1] if rev else piece)
   for row in rules:
    if tuple(row['directions'])!=canon:continue
    violation=np.ones(len(codes),dtype=bool)
    for j,cap in enumerate(row['counts'],1):
     if cap==6:continue
     position=start+6-j if rev else start+j
     violation&=(codes//6**(7-position)%6+1)<=cap
    bad|=violation
 extra[mask]=bad
removed=int((extra&~a['excluded']).sum());a['excluded']|=extra
meta.update(newly_excluded_by_screen=removed,screen_rules=rules,excluded_edges=int(a['excluded'].sum()),remaining_edges=int((~a['excluded']).sum()))
meta['arrays_sha256']={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in a.items()}
meta['scope']='Exploratory graph after unverified solver exclusions. This is not a proved bound on snakes.'
(target/'data/model.json').write_text(json.dumps(meta,indent=2)+'\n')
np.savez_compressed(target/'build/graph.npz',**a)
print('Solver exclusions',len(rules),'newly removed edges',removed,flush=True)
analyze.HERE=target;analyze.main()
