"""Measure one numerically supported covering share rule, without extra count cuts."""
from pathlib import Path
import hashlib,importlib.util,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
np=model.np
source=ROOT/'milestones/55-critical-share-family/covered'
meta=json.loads((source/'data/model.json').read_text())
with np.load(source/'build/graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert hashlib.sha256(a[k].tobytes()).hexdigest()==h
rows=json.loads((HERE/'data/windows.json').read_text())
choices=json.loads((HERE/'data/priorities.json').read_text())['single_pattern_cycle_covers']
eligible=[i for i in choices if json.loads((HERE/f'data/screen/w{i:02d}.json').read_text())['status']=='INFEASIBLE']
assert eligible
selected=eligible if '--all' in sys.argv else eligible[:1]
name='combined' if '--all' in sys.argv else 'candidate'
old=a['share_lower'].copy()
codes=a['count_code']
cs=np.stack([codes//6**k%6+1 for k in range(4,-1,-1)],axis=1)
for chosen in selected:
    row=rows[chosen]
    assert json.loads((HERE/f'data/controls/w{chosen:02d}.json').read_text())['status']=='SAT'
    for reverse in [False,True]:
        ds=row['directions'][::-1] if reverse else row['directions']
        counts=row['counts'][::-1] if reverse else row['counts']
        shape=model.canon(ds)
        dis=[i for i,d in enumerate(meta['extensions']) if model.canon(d[-6:])==shape]
        mask=np.isin(a['direction'],dis)&np.all(cs==counts,axis=1)
        a['share_lower'][mask]=np.maximum(a['share_lower'][mask],96)
        meta['share_rules'].append(dict(directions=list(shape),counts=counts,lower=96,milestone=57,status='NUMERICAL_ONLY',source=f'data/screen/w{chosen:02d}.json'))
folder=HERE/name;(folder/'build').mkdir(parents=True,exist_ok=True);(folder/'data').mkdir(exist_ok=True)
np.savez_compressed(folder/'build/graph.npz',**a)
meta['arrays_sha256']={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in a.items()}
meta['source']='milestones/55-critical-share-family/covered'
meta['scope']='Finite relaxation with additional numerical share bounds; no new global theorem.'
(folder/'data/model.json').write_text(json.dumps(meta,indent=2)+'\n')
(HERE/f'data/selected-{name}.json').write_text(json.dumps(dict(selected=selected,eligible=eligible,patterns=[rows[i] for i in selected],strengthened_transitions=int((a['share_lower']>old).sum()),lower=96,scope='Numerical local exclusions with ordinary positive controls. Lean replay pending.'),indent=2)+'\n')
spec=importlib.util.spec_from_file_location('analyze57',ROOT/'milestones/54-share-coverage/scripts/analyze.py')
analyze=importlib.util.module_from_spec(spec);spec.loader.exec_module(analyze);analyze.HERE=HERE
analyze.run(name,True)
