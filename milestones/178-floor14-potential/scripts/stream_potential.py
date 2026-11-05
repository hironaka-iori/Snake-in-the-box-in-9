"""Construct exact potentials using bounded batches and disk-backed graph columns.

The retained mask and its unresolved geometric premises are inherited.
This computation proves only inequalities on that finite retained graph.
"""
from pathlib import Path
import os,sys,json,hashlib,gzip,time
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
import numpy as np
N=1601856; E=4947008; K=4661572; B=32768
out=H/'data'; cache=out/'source-columns';cache.mkdir()
pins={}
def digest(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def read(rel):
    p=R/rel;pins[rel]=digest(p);return json.loads(p.read_text(encoding='utf-8-sig'))
def save(name,j):(out/name).write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
def canon(w):
    d={};return ''.join(str(d.setdefault(x,len(d))) for x in w)
def shape(w):return min(canon(w),canon(w[::-1]))
def ah(a):
    h=hashlib.sha256()
    for i in range(0,len(a),B):h.update(np.ascontiguousarray(a[i:i+B]).tobytes())
    return h.hexdigest()

meta=read('milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json')
cols=R/'milestones/176-boundary-retuning/data/graph-final/source-columns'
a={k:np.load(cols/(k+'.npy'),mmap_mode='r',allow_pickle=False) for k in ['U','V','weight','direction','count_code']}
for k,x in a.items():
    assert len(x)==E and ah(x)==meta['arrays_sha256'][k],k
    pins[str((cols/(k+'.npy')).relative_to(R))]=digest(cols/(k+'.npy'))
ds=read('milestones/59-extended-share-window/extended/data/model.json')['extensions']
rules=read('milestones/120-nine-transition-window/data/full-rules.json')
removed=read('milestones/144-countfree-share18/data/share18-impact/removed-indices.json')
mask=np.ones(E,dtype=bool);mask[removed]=False
assert len(removed)==E-K and int(mask.sum())==K
del removed
accepted=read('milestones/164-loss-corrected-potential/data/scaled-floor17/result.json')
fixed=read('milestones/176-boundary-retuning/data/graph-final/floor15.json')
joint=read('milestones/176-boundary-retuning/data/graph-joint15/floor15.json')
floor={'012031':16,'012032':16,'012034':15,'012301':16,'012304':16,'012310':12,'012314':16,'012340':16,'012345':16}
pending={'012034','012301','012340','012345'}
weights={key:np.lib.format.open_memmap(cache/(key+'.npy'),mode='w+',dtype='<i8',shape=(K,)) for key in ['fixed14','joint14']}
u=np.lib.format.open_memmap(cache/'U.npy',mode='w+',dtype='<i4',shape=(K,))
v=np.lib.format.open_memmap(cache/'V.npy',mode='w+',dtype='<i4',shape=(K,))
ids=np.lib.format.open_memmap(cache/'ids.npy',mode='w+',dtype='<i8',shape=(K,))
hashes={k:hashlib.sha256() for k in ['fixed15','joint15','baseline17']}
offset=0;matched_all=0;matched_kept=0
for index,word in enumerate(ds):
    begin,end=np.searchsorted(a['direction'],[index,index+1])
    suffix=word[-6:];sh=shape(suffix)
    matching=[r for r in rules if shape(r['directions'])==sh]
    for lo in range(int(begin),int(end),B):
        hi=min(lo+B,int(end));codes=a['count_code'][lo:hi].astype(np.int64)
        counts=np.column_stack([codes//6**j%6+1 for j in range(5,-1,-1)]).astype(np.int16)
        five=counts[:,1:];aligned=five if canon(suffix)==sh else five[:,::-1]
        bonus=np.zeros(hi-lo,dtype=np.int64)
        for rule in matching:
            low=np.array([x[0] for x in rule['bounds']]);high=np.array([x[1] for x in rule['bounds']])
            applies=np.all((aligned>=low)&(np.where(aligned==6,21,aligned)<=high),axis=1)
            bonus=np.maximum(bonus,np.where(applies,24*np.maximum(0,rule['lower']-aligned[:,rule['positions']].sum(axis=1)),0))
        if sh=='012032':bonus=np.maximum(bonus,24*np.maximum(0,9-counts[:,2]-counts[:,4]))
        if shape(word[2:])==shape([0,1,2,3,1,0,4]):
            bonus=np.maximum(bonus,np.where(counts[:,0]<6,24*np.maximum(0,25-counts.sum(axis=1)),0))
        matched=np.zeros(hi-lo,dtype=bool)
        for reverse in [False,True]:
            if canon(suffix[::-1] if reverse else suffix)!='012032':continue
            ff=five[:,::-1] if reverse else five
            matched|=np.all((ff>=np.array([4,0,4,0,3]))&(ff<=np.array([4,4,4,5,3])),axis=1)
        keep=mask[lo:hi];size=int(keep.sum());matched_all+=int(matched.sum());matched_kept+=int(matched[keep].sum())
        for profile in ['baseline17','fixed15','joint15','fixed14','joint14']:
            f=floor[sh]
            if profile=='baseline17' and sh=='012034':f=17
            if profile=='joint15' and sh in pending:f=15
            if profile=='fixed14' and sh=='012034':f=14
            if profile=='joint14' and sh in pending:f=14
            w=(np.maximum(a['weight'][lo:hi],120*counts[:,-1].astype(np.int64)+np.maximum(f,np.where(matched,17,0)))+bonus)[keep].astype('<i8')
            if profile in hashes:hashes[profile].update(w.tobytes())
            else:weights[profile][offset:offset+size]=w
        u[offset:offset+size]=a['U'][lo:hi][keep];v[offset:offset+size]=a['V'][lo:hi][keep]
        ids[offset:offset+size]=np.arange(lo,hi,dtype='<i8')[keep]
        offset+=size
assert offset==K and matched_all==156 and matched_kept==91
assert ah(ids)==accepted['graph']['retained_row_ids_sha256']
assert hashes['baseline17'].hexdigest()==accepted['graph']['weight_sha256']
assert hashes['fixed15'].hexdigest()==fixed['weight_sha256']
assert hashes['joint15'].hexdigest()==joint['weight_sha256']
for x in [u,v,ids,*weights.values()]:x.flush()
save('reconstruction.json',{'status':'PASS_THREE_ARCHIVED_WEIGHT_HASHES','hashes':{k:x.hexdigest() for k,x in hashes.items()},'retained_ids_sha256':ah(ids),'input_pins':pins})
del a,mask
results=[]
for profile,mean in [('fixed14',4448),('joint14',4447)]:
    w=weights[profile];dist=np.zeros(N,dtype=np.int64);start=time.monotonic();status='UNRESOLVED'
    for iteration in range(1,601):
        nxt=dist.copy()
        for lo in range(0,K,B):
            hi=min(K,lo+B)
            np.minimum.at(nxt,v[lo:hi],dist[u[lo:hi]]+9*w[lo:hi]-mean)
        if np.array_equal(nxt,dist):status='PASS_POTENTIAL';break
        dist=nxt
        save('progress.json',{'profile':profile,'iteration':iteration,'range':-int(dist.min()),'seconds':time.monotonic()-start})
        if -int(dist.min())>12000 or time.monotonic()-start>180:break
    rng=-int(dist.min());pot=dist+rng;minimum=10**9;violations=0
    for lo in range(0,K,B):
        hi=min(K,lo+B);slack=9*w[lo:hi]+pot[u[lo:hi]]-pot[v[lo:hi]]-mean
        minimum=min(minimum,int(slack.min()));violations+=int((slack<0).sum())
    record={'profile':profile,'status':status,'scaled_mean':mean,'scale':9,'scaled_range':rng,'iterations':iteration,'seconds':time.monotonic()-start,'weight_sha256':ah(w),'scan':{'edges':K,'minimum_slack':minimum,'violations':violations},'minimum_integer_loss':max(0,(9*1098600+8*mean+rng-235*(37800+mean))//45+1)}
    if status=='PASS_POTENTIAL':
        assert minimum>=0 and violations==0
        raw=pot.astype('<i8').tobytes();path=out/(profile+'-potential.i64.gz');path.write_bytes(gzip.compress(raw,mtime=0))
        record.update(potential_sha256=hashlib.sha256(raw).hexdigest(),potential_archive_sha256=digest(path),potential_file=path.name)
    save(profile+'.json',record);results.append(record)
    print(profile,status,'mean',mean,'range',rng,'loss',record['minimum_integer_loss'],flush=True)
for rel,d in pins.items():assert digest(R/rel)==d
save('results.json',{'status':'FINISHED','profiles':results,'new_unconditional_bound':False,'complete_Lean_graph_certificate':False})
