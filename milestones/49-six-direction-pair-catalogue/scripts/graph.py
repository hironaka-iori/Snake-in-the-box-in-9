"""Apply checked low-count compatibility rules on every subsegment and orientation."""
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model,analyze
np=model.np
prior=ROOT/'milestones/48-low-count-compatibility'
meta=json.loads((prior/'data/model.json').read_text())
with np.load(prior/'build/graph.npz') as z:arrays={k:z[k].copy() for k in z.files}
original=arrays['excluded'].copy();extra=np.zeros(len(original),dtype=bool)
cases=json.loads((HERE/'data/cases.json').read_text());rules=[]
for i,ds in enumerate(meta['extensions']):
    matches=set()
    for r in cases:
        shape=tuple(r['dirs']);L=len(shape)
        for start in range(9-L):
            piece=ds[start:start+L]
            if model.canon(piece)==shape:matches.add((r['number'],tuple(start+j for j in r['positions'])))
            if model.canon(piece[::-1])==shape:matches.add((r['number'],tuple(start+L-j for j in r['positions'])))
    if not matches:continue
    mask=arrays['direction']==i;codes=arrays['count_code'][mask];bad=np.zeros(len(codes),dtype=bool)
    for number,positions in sorted(matches):
        r=next(r for r in cases if r['number']==number)
        values=[(codes//6**(7-j))%6+1 for j in positions]
        if r['kind']=='sum':bad|=(sum(values)<=r['cap'])
        else:bad|=((values[0]<=r['caps'][0])&(values[1]<=r['caps'][1]))
        rules.append(dict(directions=ds,case=number,positions=positions))
    extra[mask]=bad
arrays['excluded']|=extra
np.savez_compressed(HERE/'build/graph.npz',**arrays)
meta['excluded_edges']=int(arrays['excluded'].sum());meta['remaining_edges']=int((~arrays['excluded']).sum())
meta['newly_excluded_by_low_counts']=int((extra&~original).sum());meta['low_count_rules']=rules
meta['arrays_sha256']={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in arrays.items()}
meta['scope']='Milestone 48 graph with the complete low-cap pair catalogue on all represented subsegments and orientations. Complete arbitrary-snake Lean graph bridge pending.'
(HERE/'data/model.json').write_text(json.dumps(meta,indent=2)+'\n')
print('Newly excluded transitions:',meta['newly_excluded_by_low_counts'],flush=True)
analyze.HERE=HERE;analyze.main()
