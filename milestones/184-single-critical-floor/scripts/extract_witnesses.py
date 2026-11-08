"""Extract range-forcing walks and a mean-forcing cycle from exact potentials."""
from pathlib import Path
import os,sys,json,gzip,hashlib
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
H=Path(__file__).resolve().parents[1];R=H.parents[1];sys.path.insert(0,str(R/'work/solver_packages'))
import numpy as np
D=H/'data';C=D/'source-columns';B=32768;N=1601856;K=4661572
u=np.load(C/'U.npy',mmap_mode='r');v=np.load(C/'V.npy',mmap_mode='r');ids=np.load(C/'ids.npy',mmap_mode='r')
def rows(edges,w):return [{'source_edge':int(ids[e]),'u':int(u[e]),'v':int(v[e]),'weight':int(w[e])} for e in edges]
results=[]
for profile in ['critical15','critical15-refined']:
    j=json.loads((D/(profile+'.json')).read_text());mean=j['scaled_mean'];w=np.load(C/('critical15'+'.npy'),mmap_mode='r')
    raw=gzip.decompress((D/j['potential_file']).read_bytes());assert hashlib.sha256(raw).hexdigest()==j['potential_sha256']
    pot=np.frombuffer(raw,dtype='<i8');roots=pot==int(pot.max());seen=roots.copy();parent=np.full(N,-1,dtype=np.int32)
    target=int(np.argmin(pot))
    for iteration in range(1,100):
        nxt=seen.copy()
        for lo in range(0,K,B):
            hi=min(lo+B,K);uu=u[lo:hi];vv=v[lo:hi]
            eligible=seen[uu]&(~seen[vv])&(9*w[lo:hi]+pot[uu]-pot[vv]==mean)
            edge=np.flatnonzero(eligible)+lo
            parent[v[edge]]=edge;nxt[v[edge]]=True
        seen=nxt
        if seen[target]:break
    assert seen[target]
    edges=[];node=target
    while not roots[node]:
        e=int(parent[node]);assert e>=0 and int(v[e])==node
        edges.append(e);node=int(u[e]);assert len(edges)<100
    edges.reverse();walk=rows(edges,w)
    assert mean*len(walk)-9*sum(x['weight'] for x in walk)==j['scaled_range']
    results.append({'profile':profile,'walk':walk,'walk_length':len(walk),'walk_weight':sum(x['weight'] for x in walk),'forced_scaled_range':j['scaled_range']})
    print(profile,'walk length',len(walk),'weight',sum(x['weight'] for x in walk),flush=True)

obs=json.loads((R/'milestones/176-boundary-retuning/data/scalar-obstructions.json').read_text())
c=next(x['cycle'] for x in obs['rows'] if x['floor']==15)
w=np.load(C/'critical15.npy',mmap_mode='r')
for x in c:
    e=int(np.searchsorted(ids,x['source_edge']))
    assert int(ids[e])==x['source_edge']
    assert int(u[e])==x['u'] and int(v[e])==x['v'] and int(w[e])==x['weight']
assert c[0]['u']==c[-1]['v'] and all(x['v']==y['u'] for x,y in zip(c,c[1:]))
assert sum(x['weight'] for x in c)==4454 and len(c)==9
out={'status':'PASS_CONCRETE_WALK_AND_CYCLE_IDENTITIES','range_witnesses':results,'cycle':c,'cycle_length':len(c),'cycle_weight':sum(x['weight'] for x in c),'scope':'Finite retained graph under profile (15,14,14,14); cycle bounds the mean at 4454/9.'}
(D/'witnesses.json').write_text(json.dumps(out,indent=2)+'\n')
print('common critical cycle',len(c),sum(x['weight'] for x in c),flush=True)