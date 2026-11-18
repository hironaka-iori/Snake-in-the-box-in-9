"""Exact four-position Q9 audit by coordinate columns and integer adjugates."""
from pathlib import Path
import itertools,json,hashlib,time,datetime,ctypes,os
from native_resources import snapshot,kernel,psapi,PROCESS_MEMORY_COUNTERS_EX
H=Path(__file__).resolve().parents[1];start=time.monotonic();started=datetime.datetime.now(datetime.timezone.utc).isoformat()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3
peak=0
def guard():
 global peak
 q=snapshot();assert not q['errors'] and not q['processes'] and q['free_bytes']>=768*1024**2
 handle=kernel.OpenProcess(0x1000,False,os.getpid());assert handle
 m=PROCESS_MEMORY_COUNTERS_EX();m.cb=ctypes.sizeof(m)
 try:assert psapi.GetProcessMemoryInfo(handle,ctypes.byref(m),m.cb)
 finally:kernel.CloseHandle(handle)
 peak=max(peak,int(m.PrivateUsage));assert peak<=256*1024**2 and time.monotonic()-start<180
edges=list(itertools.combinations(range(4),2));perms=list(itertools.permutations(range(4)))
def compositions(n,k):
 if k==1:yield (n,);return
 for x in range(n+1):
  for tail in compositions(n-x,k-1):yield (x,)+tail
def vertices(hist):
 v=[0,0,0,0];pos=0
 for pat,n in enumerate(hist):
  for _ in range(n):
   for j in range(3):v[j+1]|=((pat>>j)&1)<<pos
   pos+=1
 return v
def distances(v):return tuple((v[i]^v[j]).bit_count() for i,j in edges)
def canonical(d):
 M=[[0]*4 for _ in range(4)]
 for (i,j),a in zip(edges,d):M[i][j]=M[j][i]=a
 return min(tuple(M[p[i]][p[j]] for i,j in edges) for p in perms)
maps=[]
for p in perms:
 maps.append([sum((((0 if p[j+1]==0 else (pat>>(p[j+1]-1))&1)^(0 if p[0]==0 else (pat>>(p[0]-1))&1))<<j) for j in range(3)) for pat in range(8)])
def canon_hist(hist):
 out=[]
 for mapping in maps:
  h=[0]*8
  for i,n in enumerate(hist):h[mapping[i]]+=n
  out.append(tuple(h))
 return min(out)
classes={};orbits=set();total=valid=0
for hist in compositions(9,8):
 total+=1
 if total%256==0:guard()
 v=vertices(hist)
 if len(set(v))!=4 or any(x.bit_count()%2 for x in v):continue
 valid+=1;orbits.add(canon_hist(hist));key=canonical(distances(v))
 if key not in classes:classes[key]=dict(distances=list(key),representative=v,column_counts=hist,ordered_column_descriptions=0)
 classes[key]['ordered_column_descriptions']+=1
assert total==11440
def determinant(M):
 if len(M)==1:return M[0][0]
 return sum(((-1)**j)*v*determinant([row[:j]+row[j+1:] for row in M[1:]]) for j,v in enumerate(M[0]))
def adjugate(M):
 return [[(-1)**(i+j)*determinant([row[:i]+row[i+1:] for k,row in enumerate(M) if k!=j]) for j in range(4)] for i in range(4)]
coeff={2:-16,4:8,6:-10,8:35};survivors=[];rhs_count=0;rows=[]
for index,(key,row) in enumerate(sorted(classes.items())):
 guard();M=[[128 if i==j else 0 for j in range(4)] for i in range(4)]
 for (i,j),d in zip(edges,key):M[i][j]=M[j][i]=coeff[d]
 D=determinant(M);adj=adjugate(M);assert D>0
 assert all(sum(M[i][k]*adj[k][j] for k in range(4))==(D if i==j else 0) for i in range(4) for j in range(4))
 local=[]
 for s in itertools.product([-1,0,1],repeat=4):
  rhs_count+=1;nums=[315*sum(a*b for a,b in zip(r,s)) for r in adj]
  if any(n%D for n in nums):continue
  w=[n//D for n in nums]
  assert all(sum(M[i][j]*w[j] for j in range(4))==315*s[i] for i in range(4))
  if any(w):local.append(dict(s=s,w=w))
 row.update(index=index,matrix=M,determinant=D,adjugate=adj,nonzero_integer_solutions=local)
 if local:survivors.append(row)
 rows.append(row)
guard()
result=dict(status='PASS_NO_NONZERO_INTEGER_SOLUTIONS' if not survivors else 'SURVIVORS_REQUIRE_FULL_CUBE_RECONSTRUCTION',started_utc=started,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 column_compositions=total,valid_ordered_column_compositions=valid,point_set_orbits=len(orbits),metric_class_count=len(rows),rhs_cases=rhs_count,
 metric_classes=rows,survivors=survivors,arithmetic='Exact integer determinant and adjugate; no bound on exceptional integers imposed',
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),guard_sha256=hashlib.sha256(Path(__file__).with_name('native_resources.py').read_bytes()).hexdigest(),
 runtime_seconds=time.monotonic()-start,peak_private_bytes=peak,startup_snapshot=gate,
 scope='All four distinct positions of one parity by coordinate-column enumeration. Mixed parity reduces to the checked three-erasure theorem. Enumeration and geometric reduction are not Lean proofs.')
(H/'data').mkdir(exist_ok=True);(H/'data/four-count-audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(result['status'],'compositions',total,'valid',valid,'orbits',len(orbits),'metrics',len(rows),'rhs',rhs_count,'seconds',result['runtime_seconds'])
