"""Five erased counts: exact symmetry cover, integer systems and full-cube replay."""
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
 peak=max(peak,int(m.PrivateUsage));assert peak<=256*1024**2 and time.monotonic()-start<300
edges=list(itertools.combinations(range(5),2));perms=list(itertools.permutations(range(5)))
def compositions(n,k):
 if k==1:yield(n,);return
 for x in range(n+1):
  for tail in compositions(n-x,k-1):yield(x,)+tail
def vertices(hist):
 v=[0,255,0,0,0];pos=0
 for pat,n in enumerate(hist):
  for _ in range(n):
   for j in range(3):v[j+2]|=((pat>>j)&1)<<pos
   pos+=1
 for j in range(2,5):v[j]|=(v[j].bit_count()%2)<<8
 return v
def canonical(v):
 M=[[(a^b).bit_count() for b in v] for a in v]
 key,p=min((tuple(M[p[i]][p[j]] for i,j in edges),p) for p in perms)
 return key,[v[i] for i in p],p
classes={};total=valid=0
for hist in compositions(8,8):
 total+=1
 if total%128==0:guard()
 v=vertices(hist);assert all(x.bit_count()%2==0 for x in v)
 if len(set(v))!=5:continue
 valid+=1;key,representative,p=canonical(v)
 if key not in classes:classes[key]=dict(distances=list(key),representative=representative,normalized_vertices=v,column_counts=hist,canonical_permutation=p,description_count=0)
 classes[key]['description_count']+=1
assert total==6435
def determinant(M):
 if len(M)==1:return M[0][0]
 return sum((-1)**j*v*determinant([row[:j]+row[j+1:] for row in M[1:]]) for j,v in enumerate(M[0]))
def adjugate(M):
 return [[(-1)**(i+j)*determinant([row[:i]+row[i+1:] for k,row in enumerate(M) if k!=j]) for j in range(5)] for i in range(5)]
coeff={2:-16,4:8,6:-10,8:35};weights={1:35,3:-10,5:8,7:-16,9:128}
survivors=[];singular=[];rhs_count=0;rows=[];counterexamples=[]
for index,(key,row) in enumerate(sorted(classes.items())):
 guard();M=[[128 if i==j else 0 for j in range(5)] for i in range(5)]
 for (i,j),d in zip(edges,key):M[i][j]=M[j][i]=coeff[d]
 assert tuple((row['representative'][i]^row['representative'][j]).bit_count() for i,j in edges)==key
 D=determinant(M);adj=adjugate(M)
 assert all(sum(M[i][k]*adj[k][j] for k in range(5))==(D if i==j else 0) for i in range(5) for j in range(5))
 row.update(index=index,matrix=M,determinant=D,adjugate=adj)
 if not D:singular.append(index);rows.append(row);continue
 local=[]
 for s in itertools.product([-1,0,1],repeat=5):
  rhs_count+=1;nums=[315*sum(a*b for a,b in zip(r,s)) for r in adj]
  if any(n%D for n in nums):continue
  w=[n//D for n in nums]
  assert all(sum(M[i][j]*w[j] for j in range(5))==315*s[i] for i in range(5))
  if not any(w):continue
  item=dict(s=s,w=w,within_automatic_bound=max(map(abs,w))<=9)
  if item['within_automatic_bound']:
   E=row['representative'];nums=[sum(wi*weights.get((x^p).bit_count(),0) for wi,p in zip(w,E)) for x in range(512)]
   good=all(n%315==0 and -315<=n<=315 for n in nums);item['full_inverse_ternary']=good
   if good:
    z=[n//315 for n in nums];profile=[sum(z[x^(1<<i)] for i in range(9)) for x in range(512)]
    expected=[w[E.index(x)] if x in E else 0 for x in range(512)];assert profile==expected
    item['positive_vertices']=[x for x in range(512) if z[x]==1];item['negative_vertices']=[x for x in range(512) if z[x]==-1]
    counterexamples.append(dict(matrix_index=index,**item))
  local.append(item)
 row['nonzero_integer_solutions']=local
 if local:survivors.append(index)
 rows.append(row)
guard()
status='COUNTEREXAMPLE' if counterexamples else 'SINGULAR_CASES_UNRESOLVED' if singular else 'PASS_NO_NONZERO_INTEGER_SOLUTIONS' if not survivors else 'ANTIPODAL_SURVIVORS_REQUIRE_FURTHER_PROOF'
result=dict(status=status,started_utc=started,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),column_descriptions=total,valid_descriptions=valid,metric_class_count=len(rows),rhs_cases=rhs_count,metric_classes=rows,
 singular_indices=singular,surviving_matrix_indices=survivors,counterexamples=counterexamples,
 source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),guard_sha256=hashlib.sha256(Path(__file__).with_name('native_resources.py').read_bytes()).hexdigest(),runtime_seconds=time.monotonic()-start,peak_private_bytes=peak,startup_snapshot=gate,
 scope='Five distinct same-parity positions containing a distance8 pair, covered by normalizing that pair to0,255. Mixed parity reduces to four-erasure recovery; no-distance8 cases reduce to the conditional eight-erasure theorem. Geometry remains written/native.')
(H/'data/five-count-audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(status,'descriptions',total,'valid',valid,'metrics',len(rows),'rhs',rhs_count,'singular',len(singular),'surviving matrices',len(survivors),'counterexamples',len(counterexamples),'seconds',result['runtime_seconds'])
