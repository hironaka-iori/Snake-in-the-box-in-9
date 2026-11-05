"""Reweight the exact retained graph; no claim of coverage by arbitrary snakes."""
from pathlib import Path
import sys,os,json,gzip,hashlib,time
from fractions import Fraction
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path.insert(0,str(R/'work/solver_packages'))
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np
from reconstruct_mapped import reconstruct,shape,canon,digest
run=H/'data/graph';run.mkdir(exist_ok=True)
def save(name,j):(run/name).write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
def ah(a):return hashlib.sha256(memoryview(np.ascontiguousarray(a)).cast('B')).hexdigest()
def read(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
accepted_path=R/'milestones/164-loss-corrected-potential/data/scaled-floor17/result.json'
accepted=read(accepted_path);assert accepted['status']=='PASS_MINIMUM_SCALED_RANGE_AT_MEAN4462'
pins={str(accepted_path):digest(accepted_path)}
data=reconstruct(np,run);arrays=data['arrays'];mask=data['mask'];shared=data['shared'];digits=data['digits'];ds=data['ds']
pins.update({str(R/k):v for k,v in data['pins'].items()})
shapes=[shape(word[-6:]) for word in ds];directions=arrays['direction'];last=digits[:,-1].astype(np.int64);source=arrays['weight'].astype(np.int64)
floors={'012031':16,'012032':16,'012034':17,'012301':16,'012304':16,'012310':12,'012314':16,'012340':16,'012345':16}
base=np.array([floors[s] for s in shapes],dtype=np.int64)[directions]
matched=np.zeros(len(mask),dtype=bool)
for index,word in enumerate(ds):
 lo,hi=np.searchsorted(directions,[index,index+1]);five=digits[lo:hi,1:6]
 for reverse in [False,True]:
  selected=word[-6:][::-1] if reverse else word[-6:]
  if canon(selected)!='012032':continue
  counts=five[:,::-1] if reverse else five
  matched[lo:hi]|=np.all((counts>=np.array([4,0,4,0,3]))&(counts<=np.array([4,4,4,5,3])),axis=1)
assert int(matched.sum())==156 and int(matched[mask].sum())==91
u=arrays['U'][mask];v=arrays['V'][mask];ids=np.flatnonzero(mask);n=1601856
assert len(u)==4661572 and ah(ids)==accepted['graph']['retained_row_ids_sha256']
def weight_profile(floor,joint=False):
 f=base.copy();target=np.array([s=='012034' for s in shapes],dtype=bool)[directions];f[target]=floor
 if joint:
  target_other=np.array([s in ['012301','012340','012345'] for s in shapes],dtype=bool)[directions];f[target_other]-=1
 return (np.maximum(source,120*last+np.maximum(f,np.where(matched,17,0)))+shared)[mask]
w17=weight_profile(17);assert ah(w17)==accepted['graph']['weight_sha256']
archive=accepted_path.parent/'potential.i64.gz';pins[str(archive)]=digest(archive);assert digest(archive)==accepted['potential_archive_sha256']
raw=gzip.decompress(archive.read_bytes());assert hashlib.sha256(raw).hexdigest()==accepted['potential_sha256']
potential=np.frombuffer(raw,dtype='<i8');assert len(potential)==n and int(potential.min())==0 and int(potential.max())==5411
block=200000

def scan(w,pot,mean):
 minimum=None;violations=0
 for lo in range(0,len(w),block):
  hi=min(lo+block,len(w));s=9*w[lo:hi]+pot[u[lo:hi]]-pot[v[lo:hi]]-mean
  minimum=int(s.min()) if minimum is None else min(minimum,int(s.min()));violations+=int(np.count_nonzero(s<0))
 return {'minimum_slack':minimum,'violations':violations,'edges':len(w)}
assert scan(w17,potential,4462)=={'minimum_slack':0,'violations':0,'edges':4661572}
results=[]
for label,floor,joint in [('floor16',16,False),('joint-one-unit',16,True)]:
 w=weight_profile(floor,joint);diff=w17-w;assert int(diff.min())>=0 and int(diff.max())<=1
 check=scan(w,potential,4453);assert check['violations']==0
 results.append({'profile':label,'floor012034':floor,'other_pending_floors':15 if joint else 16,'status':'PASS_REUSED_POTENTIAL','scaled_mean':4453,'scale':9,'range':5411,'changed_edges':int(np.count_nonzero(diff)),'maximum_decrease':int(diff.max()),'weight_sha256':ah(w),'scan':check,'comparison':str(Fraction(9*1098600+8*4453+5411,37800+4453))})
 save('progress.json',{'phase':'SCANNED_ONE_UNIT','results':results})
# Retuning only the 012034 floor. All other conditions and floors remain unchanged.
for floor,mean in [(12,4452),(11,4450),(10,4448)]:
 w=weight_profile(floor);dist=np.zeros(n,dtype=np.int64);cap=227*mean-9*111600-1
 started=time.monotonic();status='UNRESOLVED';layers=[];journal=run/('journal-floor'+str(floor));journal.mkdir();totalbytes=0
 for iteration in range(1,301):
  if time.monotonic()-started>150:status='UNRESOLVED_TIME_LIMIT';break
  nxt=dist.copy()
  for lo in range(0,len(w),block):
   hi=min(lo+block,len(w));np.minimum.at(nxt,v[lo:hi],dist[u[lo:hi]]+9*w[lo:hi]-mean)
  if np.array_equal(nxt,dist):status='PASS_POTENTIAL';break
  changed=np.flatnonzero(nxt<dist);pred=np.full(n,-1,dtype=np.int64)
  for lo in range(0,len(w),block):
   hi=min(lo+block,len(w));cand=dist[u[lo:hi]]+9*w[lo:hi]-mean
   eligible=np.flatnonzero((cand==nxt[v[lo:hi]])&(nxt[v[lo:hi]]<dist[v[lo:hi]]))
   np.maximum.at(pred,v[lo:hi][eligible],eligible+lo)
  assert np.all(pred[changed]>=0)
  pairs=np.column_stack([changed,pred[changed]]).astype('<u4');fp=journal/(str(iteration)+'.u32');pairs.tofile(fp);totalbytes+=fp.stat().st_size
  assert totalbytes<512*1024**2
  layers.append((fp,len(changed),digest(fp)));dist=nxt
  save('progress.json',{'phase':'RETUNING','floor':floor,'mean':mean,'iteration':iteration,'range_lower_bound':-int(dist.min()),'maximum_acceptable_range':cap})
  if -int(dist.min())>cap:status='FIXED_MEAN_OBSTRUCTION';break
 endpoint=int(np.argmin(dist));vertex=endpoint;walk=[]
 for fp,rows,d in reversed(layers):
  assert digest(fp)==d;pairs=np.memmap(fp,dtype='<u4',mode='r',shape=(rows,2));i=int(np.searchsorted(pairs[:,0],vertex))
  if i<rows and int(pairs[i,0])==vertex:
   edge=int(pairs[i,1]);assert int(v[edge])==vertex;walk.append(edge);vertex=int(u[edge])
  del pairs
 walk.reverse();assert all(int(v[a])==int(u[b]) for a,b in zip(walk,walk[1:]))
 deficit=mean*len(walk)-9*sum(int(w[e]) for e in walk);assert deficit==-int(dist[endpoint])
 result={'profile':'floor'+str(floor),'floor012034':floor,'other_pending_floors':16,'status':status,'scaled_mean':mean,'scale':9,'range_lower_bound':deficit,'maximum_acceptable_range':cap,'weight_sha256':ah(w),'iterations':iteration,'seconds':time.monotonic()-started,'walk':[{'source_edge':int(ids[e]),'u':int(u[e]),'v':int(v[e]),'weight':int(w[e])} for e in walk]}
 if status=='PASS_POTENTIAL':
  rng=-int(dist.min());pot=dist+rng;check=scan(w,pot,mean);assert check['violations']==0 and rng<=cap
  raw=pot.astype('<i8').tobytes();out=run/('potential-floor'+str(floor)+'.i64.gz');out.write_bytes(gzip.compress(raw,mtime=0))
  result.update(range=rng,scan=check,potential_file=out.name,potential_sha256=hashlib.sha256(raw).hexdigest(),potential_archive_sha256=digest(out),comparison=str(Fraction(9*1098600+8*mean+rng,37800+mean)))
 results.append(result);save('floor'+str(floor)+'.json',result)
for p,d in pins.items():assert digest(Path(p))==d,p
save('results.json',{'status':'PASS_REWEIGHTING_AND_BOUNDED_RETUNING','profiles':results,'input_pins':pins,'inherited_assumptions':accepted['inherited_assumptions'],'new_global_bound':False,'complete_Lean_graph_certificate':False,'baseline_weight_sha256':ah(w17),'retained_edges':len(w17)})
save('progress.json',{'phase':'FINISHED'});print([(x['profile'],x['status'],x.get('range'),x.get('comparison')) for x in results],flush=True)
