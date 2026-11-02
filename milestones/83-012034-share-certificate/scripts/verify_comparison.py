"""Verify the single-target model independently of policy iteration."""
from pathlib import Path
from fractions import Fraction
import gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rawsha=lambda b:hashlib.sha256(b).hexdigest()
CAT=ROOT/'milestones/73-countfree-share-catalogue'
old_path=CAT/'data/proved-model.json';new_path=HERE/'data/assumed-012034x20-model.json'
old=read(old_path);new=read(new_path)
assert old['additional_share_assumptions']==[]
assert new['additional_share_assumptions']==[dict(shape=[0,1,2,0,3,4],share=20)]
assert new['audited_local_sources']==old['audited_local_sources']
for path,digest in old['audited_local_sources'].items():assert sha(ROOT/path)==digest
extension_path=ROOT/'milestones/59-extended-share-window/extended/data/model.json'
extensions=read(extension_path)['extensions']
source=ROOT/'milestones/72-four-count-proof-closure/critical-current/build/source-graph.npz'
with np.load(source) as z:a={k:z[k] for k in z.files}
for key,digest in old['source_arrays_sha256'].items():assert rawsha(a[key].tobytes())==digest
assert new['source_arrays_sha256']==old['source_arrays_sha256']
def canon(word):
    d={};return tuple(d.setdefault(x,len(d)) for x in word)
def weights(floors):
    lookup={tuple(r['shape']):r['share'] for r in floors}
    floor_by_direction=np.array([lookup.get(min(canon(ds[-6:]),canon(ds[-6:][::-1])),0) for ds in extensions],dtype=np.int64)
    return np.maximum(a['weight'].astype(np.int64),120*(a['count_code']%6+1)+floor_by_direction[a['direction']])
base=weights(old['countfree_floors']);W=weights(new['countfree_floors'])
assert rawsha(base.tobytes())==old['weight_sha256']
assert rawsha(W.tobytes())==new['weight_sha256'] and np.all(W>=base)
assert {tuple(r['shape']):r['share'] for r in new['countfree_floors']}=={
    **{tuple(r['shape']):r['share'] for r in old['countfree_floors']},(0,1,2,0,3,4):20}
potential_path=HERE/'data/assumed-012034x20-potential.i64.gz'
raw=gzip.decompress(potential_path.read_bytes());assert rawsha(raw)==new['potential_sha256']
pi=np.frombuffer(raw,dtype='<i8');mu=Fraction(new['mean']);p,d=mu.numerator,mu.denominator
assert mu==Fraction(9259,19) and len(pi)==new['states']
assert int(pi.max()-pi.min())==new['potential_range']==11301
assert np.all(p+pi[a['V']]<=d*W+pi[a['U']])
cycle=new['cycle']
for i,row in enumerate(cycle):
    e=row['edge'];assert (row['u'],row['v'],row['weight'])==(int(a['U'][e]),int(a['V'][e]),int(W[e]))
    assert row['v']==cycle[(i+1)%len(cycle)]['u']
assert Fraction(sum(r['weight'] for r in cycle),len(cycle))==mu
bound=Fraction(1098960*d+8*p+11301,p+4200*d)
assert str(bound)==new['conditional_bound']=='20965613/89059' and 235<bound<236
out=dict(status='PASS_EXACT_SINGLE_TARGET_COMPARISON',mean=str(mu),scaled_potential_range=11301,
    potential_denominator=d,edges=len(W),edges_improved_over_completed_model=int(np.sum(W>base)),
    baseline_mean=old['mean'],conditional_bound=str(bound),conditional_integer_bound=235,
    mean_threshold_deficit=111960*d-227*p,
    inputs={path.relative_to(ROOT).as_posix():sha(path) for path in
      [Path(__file__),HERE/'scripts/compare_target.py',old_path,new_path,potential_path,extension_path]},
    scope='Exact finite graph with one additional unproved local share premise: 012034 >=20. Graph interpretation and Lean potential replay remain separate.')
(HERE/'data/comparison-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],out['mean'],'newly raised edges',out['edges_improved_over_completed_model'])
