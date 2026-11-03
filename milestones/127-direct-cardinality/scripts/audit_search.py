"""Check terminal outcomes, reduced inputs, and bounded proof-ID transport."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def cnf(p):
 lines=p.read_text().splitlines();_,kind,nv,nc=lines[0].split();assert kind=='cnf'
 rows=[list(map(int,line.split())) for line in lines[1:]]
 assert len(rows)==int(nc) and all(c[-1]==0 and all(0<abs(x)<=int(nv) for x in c[:-1]) for c in rows)
 return int(nv),[c[:-1] for c in rows]
nv,original=cnf(H/'work/original.cnf');N=len(original);assert (nv,N)==(7277,106348)
prelude=read(H/'data/direct-clauses.json')['rows'];red=read(H/'data/reduced.json')
_,reduced=cnf(H/'work/reduced.cnf');_,aug=cnf(H/'work/augmented.cnf')
assert aug==original+[r['clause'] for r in prelude]
db={i:c for i,c in enumerate(original,1)}
def rup(clause,hints,db):
 assigned={-x for x in clause};conflict=any(-x in assigned for x in assigned)
 for h in hints:
  assert h in db
  if conflict:continue
  c=db[h]
  if any(x in assigned for x in c):continue
  rest=set(c)-{-x for x in assigned};assert len(rest)<=1
  if not rest:conflict=True
  else:assigned.add(next(iter(rest)))
 assert conflict
for row in prelude:
 assert row['id']>max(row['hints']);rup(row['clause'],row['hints'],db);db[row['id']]=row['clause']
assert len(reduced)==101666 and [db[i] for i in red['input_id_map']]==reduced
assert set(red['removed_clauses'])==set(range(1,N+1))-set(red['input_id_map'][:101431])
assert len(red['removed_clauses'])==4917 and len(red['removed_auxiliary_variables'])==2457
assert not {abs(x) for c in reduced for x in c}&set(red['removed_auxiliary_variables'])
results=[]
for name,rname,formula in [('augmented','search.json',aug),('reduced','search-reduced.json',reduced)]:
 rec=read(H/'data'/rname);assert rec['status']!='RUNNING'
 assert sha(H/'work'/(name+'.cnf'))==rec['cnf_sha256']
 for key,path in [('raw',H/'work'/(name+'.raw.lrat')),('stdout',H/'logs'/('search'+('-reduced' if name=='reduced' else '')+'.stdout.txt')),('stderr',H/'logs'/('search'+('-reduced' if name=='reduced' else '')+'.stderr.txt'))]:
  assert sha(path)==rec[key+'_sha256']
 assert sha(Path(rec['command'][0]))==rec['solver_sha256']
 assert rec['command'][1:5]==['-q','--lrat','--no-binary','--seed=1']
 if rec['status']=='TIMEOUT':
  assert rec['seconds']>=rec['timeout_seconds'] and rec['exit_code'] not in [10,20]
 else:assert rec['status'].startswith('NATIVE_'),rec['status']
 M=len(formula);mapping=red['input_id_map'] if name=='reduced' else list(range(1,M+1))
 def remap(x):return mapping[x-1] if x<=M else N+len(prelude)+x-M
 workdb=dict(db);last=N+len(prelude);checked=hints=deletions=0;empty=False
 with (H/'work'/(name+'.raw.lrat')).open() as f:
  for line in f:
   parts=line.split()
   if len(parts)>1 and parts[1]=='d':deletions+=1;continue
   row=list(map(int,parts));z=row.index(0,1);cid=row[0];c=row[1:z];hs=row[z+1:-1]
   assert row[-1]==0 and cid>M and all(0<h<cid for h in hs)
   newcid=remap(cid);newhs=[remap(h) for h in hs]
   assert newcid>last and all(h<newcid for h in newhs)
   rup(c,newhs,workdb);workdb[newcid]=c;last=newcid;checked+=1;hints+=len(hs);empty|=not c
   if checked==1000:break
 assert checked==1000 and not empty
 results.append(dict(name=name,status=rec['status'],wall_seconds=rec['seconds'],input_clauses=M,initial_native_deductions_replayed=checked,initial_hints_replayed=hints,deletions_omitted=deletions,transport_to_original_verified_on_prefix=True,full_native_proof_replayed=False,final_empty_clause_verified=False))
pins={p.relative_to(H).as_posix():sha(p) for p in [H/'data/prelude.json',H/'data/prelude-review.json',H/'data/reduced.json',H/'data/search.json',H/'data/search-reduced.json',H/'work/original.cnf',H/'work/augmented.cnf',H/'work/reduced.cnf',H/'work/prelude.lrat']}
out=dict(status='PASS_REDUCED_INPUTS_AND_BOUNDED_TRACE_TRANSPORT',attempts=results,pins=pins,script_sha256=sha(Path(__file__)),scope='Exact input checks and first1000 native RUP deductions per encoding transported to original inputs. Neither entire native trace nor a final contradiction is verified. No new count floor.')
p=H/'data/search-audit.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
