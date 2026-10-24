"""Measure the effect of the pair inequality on the entire saved state graph."""
from pathlib import Path
import hashlib,importlib.util,json,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
import analyze
np=model.np
prior=ROOT/'milestones/42-six-count-state-model'
meta=json.loads((prior/'data/model.json').read_text())
with np.load(prior/'build/graph.npz') as archive: arrays={k:archive[k].copy() for k in archive.files}
original=arrays['excluded'].copy();extra=np.zeros(len(original),dtype=bool)
shape=(0,1,2,3,4,0,3,1)
for i,ds in enumerate(meta['extensions']):
    if model.canon(ds)!=shape and model.canon(ds[::-1])!=shape:continue
    mask=arrays['direction']==i
    codes=arrays['count_code'][mask]
    second=(codes//6**5)%6+1;sixth=(codes//6)%6+1
    extra[mask]=(second+sixth<7)
arrays['excluded'] |= extra
(HERE/'build').mkdir(exist_ok=True)
np.savez_compressed(HERE/'build/graph.npz',**arrays)
meta['excluded_edges']=int(arrays['excluded'].sum());meta['remaining_edges']=int((~arrays['excluded']).sum())
meta['newly_excluded_by_pair']=int((extra&~original).sum())
meta['arrays_sha256']={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in arrays.items()}
meta['scope']='Milestone 42 saved graph plus the exterior-turn pair inequality. Full arbitrary-snake Lean graph bridge remains pending.'
(HERE/'data/model.json').write_text(json.dumps(meta,indent=2)+'\n')
print('Newly excluded transitions:',meta['newly_excluded_by_pair'],flush=True)
analyze.HERE=HERE
analyze.main()
