"""Apply the singleton rules in both orientations to every represented subsegment."""
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model,analyze
np=model.np
prior=ROOT/'milestones/44-critical-window-generalization'
meta=json.loads((prior/'data/model.json').read_text())
with np.load(prior/'build/graph.npz') as archive:arrays={k:archive[k].copy() for k in archive.files}
original=arrays['excluded'].copy();extra=np.zeros(len(original),dtype=bool)
cases=json.loads((HERE/'data/cases.json').read_text());rules=[]
for i,ds in enumerate(meta['extensions']):
    positions=set()
    for r in cases:
        shape=tuple(r['dirs']);L=len(shape);j=r['position']
        for start in range(9-L):
            piece=ds[start:start+L]
            if model.canon(piece)==shape:positions.add(start+j)
            if model.canon(piece[::-1])==shape:positions.add(start+L-j)
    if not positions:continue
    mask=arrays['direction']==i;codes=arrays['count_code'][mask];bad=np.zeros(len(codes),dtype=bool)
    for j in positions:bad|=((codes//6**(7-j))%6==0)
    extra[mask]=bad;rules.append(dict(directions=ds,positions=sorted(positions)))
arrays['excluded']|=extra
(HERE/'build').mkdir(exist_ok=True);np.savez_compressed(HERE/'build/graph.npz',**arrays)
meta['excluded_edges']=int(arrays['excluded'].sum());meta['remaining_edges']=int((~arrays['excluded']).sum())
meta['newly_excluded_by_singletons']=int((extra&~original).sum());meta['singleton_rules']=rules
meta['arrays_sha256']={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in arrays.items()}
meta['scope']='Milestone 44 graph plus three count-one exclusions on all represented subsegments and orientations. Complete arbitrary-snake Lean graph bridge remains pending.'
(HERE/'data/model.json').write_text(json.dumps(meta,indent=2)+'\n')
print('Newly excluded transitions:',meta['newly_excluded_by_singletons'],flush=True)
analyze.HERE=HERE;analyze.main()
