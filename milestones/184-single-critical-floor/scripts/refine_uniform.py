from pathlib import Path
import os,sys,json,hashlib,gzip,time
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
H=Path(__file__).resolve().parents[1];R=H.parents[1];sys.path.insert(0,str(R/'work/solver_packages'))
import numpy as np
D=H/'data';C=D/'source-columns';B=32768;N=1601856;K=4661572
u=np.load(C/'U.npy',mmap_mode='r');v=np.load(C/'V.npy',mmap_mode='r');w=np.load(C/'critical15.npy',mmap_mode='r')
j=json.loads((D/'critical15.json').read_text());hh=hashlib.sha256()
for lo in range(0,K,B):hh.update(w[lo:lo+B].tobytes())
assert hh.hexdigest()==j['weight_sha256']
mean=4454;dist=np.zeros(N,dtype=np.int64);start=time.monotonic();status='UNRESOLVED'
for iteration in range(1,151):
    nxt=dist.copy()
    for lo in range(0,K,B):
        hi=min(K,lo+B);np.minimum.at(nxt,v[lo:hi],dist[u[lo:hi]]+9*w[lo:hi]-mean)
    if np.array_equal(nxt,dist):status='PASS_POTENTIAL';break
    dist=nxt
rng=-int(dist.min());pot=dist+rng;minimum=10**9;violations=0
for lo in range(0,K,B):
    hi=min(K,lo+B);s=9*w[lo:hi]+pot[u[lo:hi]]-pot[v[lo:hi]]-mean
    minimum=min(minimum,int(s.min()));violations+=int((s<0).sum())
record={'profile':'critical15-refined','status':status,'scaled_mean':mean,'scale':9,'scaled_range':rng,'weight_sha256':j['weight_sha256'],'iterations':iteration,'seconds':time.monotonic()-start,'scan':{'edges':K,'minimum_slack':minimum,'violations':violations},'minimum_integer_loss':max(0,(9*1098600+8*mean+rng-235*(37800+mean))//45+1)}
if status=='PASS_POTENTIAL':
    assert violations==0
    raw=pot.astype('<i8').tobytes();p=D/'critical15-refined-potential.i64.gz';p.write_bytes(gzip.compress(raw,mtime=0))
    record.update(potential_file=p.name,potential_sha256=hashlib.sha256(raw).hexdigest(),potential_archive_sha256=hashlib.sha256(p.read_bytes()).hexdigest())
(D/'critical15-refined.json').write_text(json.dumps(record,indent=2)+'\n')
print(status,'mean',mean,'range',rng,'loss',record['minimum_integer_loss'])
