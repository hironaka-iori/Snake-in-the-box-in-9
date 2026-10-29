from pathlib import Path
import collections,gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
SOURCE=ROOT/'milestones/59-extended-share-window/extended';sm=read(SOURCE/'data/model.json')
with np.load(SOURCE/'build/graph.npz') as z:s={k:z[k] for k in z.files}
for k,h in sm['arrays_sha256'].items():assert sha(s[k].tobytes())==h
PREV=ROOT/'milestones/67-critical-family-charge';meta=read(PREV/'data/full-model.json')
with np.load(PREV/'build/full-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==h
rules=read(ROOT/'milestones/57-replacement-share-family/combined/data/model.json')['share_rules']
checked=[r for r in rules if r.get('status')!='NUMERICAL_ONLY'];pending=[r for r in rules if r.get('status')=='NUMERICAL_ONLY']
geo=read(ROOT/'milestones/59-extended-share-window/data/geometry.json')['patterns']
assert [r['directions'] for r in geo]==sm['extensions']
credit=np.array([r['share_lower'] for r in geo],dtype=np.int16)[s['direction']]
def canon(w):
    names=list(dict.fromkeys(w));return tuple(names.index(x) for x in w)
for di,ds in enumerate(sm['extensions']):
    ix=np.flatnonzero(s['direction']==di);codes=s['count_code'][ix]
    for r in checked:
        if canon(ds[-6:])==tuple(r['directions']):
            hit=np.ones(len(ix),dtype=bool)
            for j,c in enumerate(r['counts']):hit&=(codes//6**(4-j))%6+1==c
            credit[ix[hit]]=np.maximum(credit[ix[hit]],r['lower'])
assert np.all(credit<=s['share_lower'])
base_loss=int(np.count_nonzero(credit<s['share_lower']))
full=credit[a['source_edge']].copy()
for q in range(len(meta['prefixes'])):
    ix=np.flatnonzero(a['history']==q);src=a['source_edge'][ix];prefix=tuple(meta['prefixes'][q])
    for p in meta['patterns']:
        if p['mode']!='share' or len(prefix)!=2 or prefix!=tuple(p['signature'][:2]):continue
        hit=s['direction'][src]==p['signature'][2];pos=ix[hit];codes=s['count_code'][src[hit]]
        full[pos]=np.maximum(full[pos],p['geometric_lower']);qual=np.ones(len(pos),dtype=bool)
        for k,cap in p['caps'].items():qual&=codes//6**(5-int(k))%6+1<=cap
        full[pos[qual]]=np.maximum(full[pos[qual]],p['lower'])
new=120*s['count'][a['source_edge']].astype(np.int64)+full
assert np.all(new<=a['weight']);loss=a['weight']-new
analysis=read(PREV/'data/full-analysis.json');pi=np.frombuffer(gzip.decompress((PREV/'data/full-potential.i64.gz').read_bytes()),dtype='<i8')
slack=5*new+pi[a['U']]-pi[a['V']]-2482
changed=np.flatnonzero(loss);violated=np.flatnonzero(slack<0)
report=dict(checked_oriented_share_rules=len(checked),removed_oriented_share_rules=len(pending),removed_rules=pending,source_edges_losing_credit=base_loss,full_edges_losing_credit=len(changed),old_potential_violations=len(violated),maximum_weight_loss=int(max(loss)),minimum_old_potential_slack=int(min(slack)),remaining_count_keys=28623,scope='Removes every numerical-only inherited share rule, while retaining numerical count exclusions. New exact potential is computed separately.')
(HERE/'data/share-ablation.json').write_text(json.dumps(report,indent=2)+'\n')
a['weight']=new.astype(np.int16);meta['arrays_sha256']={k:sha(v.tobytes()) for k,v in a.items()};meta['share_rule_status']='Only checked share rules and geometry; count exclusions remain mixed.'
np.savez_compressed(HERE/'build/share-clean-graph.npz',**a)
(HERE/'data/share-clean-model.json').write_text(json.dumps(meta,indent=2)+'\n')
src=(PREV/'scripts/analyze_full.py').read_text().replace("else 'full'","else 'share-clean'").replace("['full']","['share-clean']").replace('1099680*d','1098960*d')
src=src.replace("share_lower=int(sa['share_lower'][s])","source_share_before_ablation=int(sa['share_lower'][s]), effective_share=int(W[e]-120*(int(sa['count_code'][s])%6+1))")
(HERE/'scripts/analyze.py').write_text(src)
print({k:v for k,v in report.items() if k!='removed_rules'},flush=True)
