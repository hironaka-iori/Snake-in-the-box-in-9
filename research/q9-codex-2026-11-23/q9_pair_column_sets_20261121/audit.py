import json,gzip
from pathlib import Path
from collections import Counter
D=Path(__file__).resolve().parent
bank=[list(map(int,l.split())) for l in gzip.open(D.parent/'q9_port_followup_public191.txt.gz','rt')]
def proj(p,d):return {v&~(1<<d) for v in p}
def path(v):
    assert all(0<=x<512 for x in v) and len(set(v))==len(v)
    assert all(((x^v[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(v) for j in range(i+1,len(v)))
def rows(n):return [json.loads(l) for l in (D/(n+'.jsonl')).read_text().splitlines()]
def tab(x):return dict(Counter(z['status'] for z in x))
def merge(files):
    by={r['id']:r for r in rows(files[0])};assert len(by)==len(rows(files[0]))
    for f in files[1:]:
        prior=[r['id'] for r in by.values() if r['status']=='UNKNOWN']
        got=rows(f);assert sorted(prior)==sorted(r['id'] for r in got)
        for r in got:by[r['id']]={**by[r['id']],**r}
    return list(by.values())
for p in bank:path(p)
assert len(bank)==131
s={}
for name,files in [('four_masks',['first','retry','strong_local']),('all_vertices',['positive_only','strong_free']),('all_pairs',['allpairs','allpairs_retry'])]:
    v=merge(files);s[name]=dict(jobs=len(v),results=tab(v),by_run={f:tab(rows(f)) for f in files},axis_pairs=len({tuple(sorted(r['axes'])) for r in v}))
    if name=='four_masks':s[name]['by_mode']={str(i):tab([r for r in v if r['mode']==i]) for i in range(4)}
    else:
        assert all(r['fixed']==0 and r['pool']==512 for r in v)
        if name=='all_vertices':s[name]['by_source_relation']={k:tab([r for r in v if (r['source']==r['donor'])==h]) for k,h in [('same',True),('different',False)]}
        else:s[name]['by_source']={str(k):tab([r for r in v if r['source']==k]) for k in sorted({r['source'] for r in v})}
for f in ('control','control_free'):
    r=json.loads((D/(f+'.json')).read_text());w=r['witness'];path(w);assert len(w)==192
    p=bank[r.get('source',r.get('ref'))];ds=[len(proj(w,a)^proj(p,a)) for a in r['axes']];assert ds==[2,2]
    if f=='control':
        for a,u in zip(r['axes'],r['released']):assert proj(w,a)-set(u)==proj(p,a)-set(u)
    else:
        for a,b in zip(r['axes'],r['mandatory']):assert set(b)<=proj(w,a)
    s[f]=dict(edges=len(w)-1,pairs=len(w)*(len(w)-1)//2,projection_differences=ds,derived_fixed=r['fixed'],eligible=r['pool'],outside_hint=r['outside_hint'])
s['small']=json.loads((D/'small_verify.json').read_text())
print(json.dumps(s,indent=2))
