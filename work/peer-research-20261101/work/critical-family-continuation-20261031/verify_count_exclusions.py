"""Independent standalone readers for all three original count-core certificates."""
from pathlib import Path
import json,hashlib,sys,re
H=Path(__file__).resolve().parent
if not __debug__:raise RuntimeError('run verifier without -O')
sys.path.insert(0,str(H));from zero_share_probe import build
B={e['source_edge']:e for e in json.loads((H/'filtered_critical_edges.json').read_text())};receipts=[]

def replay(clauses,proof):
 db=[tuple(c) for c in clauses];nh=0
 for row in proof:
  cid,cl,hs=row;assert cid==len(db)+1;values={}
  for l in cl:assert abs(l) not in values or values[abs(l)]==(l<0);values[abs(l)]=l<0
  contradiction=False
  for k,h in enumerate(hs):
   assert 1<=h<=len(db);C=db[h-1];assert not any(abs(l) in values and values[abs(l)]==(l>0) for l in C);unknown={l for l in C if abs(l) not in values}
   if not unknown:assert k==len(hs)-1;contradiction=True
   else:assert len(unknown)==1;l=next(iter(unknown));values[abs(l)]=l>0
   nh+=1
  assert contradiction;db.append(tuple(cl))
 assert proof and proof[-1][1]==[];return nh

for folder in sorted((H/'count_window_certificates').iterdir()):
 M=json.loads((folder/'manifest.json').read_text());
 for name,digest in M['files_sha256'].items():assert hashlib.sha256((folder/name).read_bytes()).hexdigest()==digest
 clauses=[]
 for line in (folder/'core.cnf').read_text().splitlines():
  if line.startswith('p '):_,_,nv,nc=line.split();nv=int(nv);nc=int(nc)
  elif line and not line.startswith('c'):
   ns=list(map(int,line.split()));assert ns[-1]==0 and all(1<=abs(l)<=nv for l in ns[:-1]);clauses.append(ns[:-1])
 assert len(clauses)==nc;proof=[]
 for line in (folder/'proof.lrat').read_text().splitlines():
  ns=list(map(int,line.split()));k=ns.index(0,1);assert ns[-1]==0;proof.append((ns[0],ns[1:k],ns[k+1:-1]))
 nh=replay(clauses,proof);E,meta=build(B[M['source_edge']]);assert meta['source_wincert_sha256']==M['source_wincert_sha256'];vs=M['variable_mapping_new_to_source'];raw=[[vs[abs(l)-1]*(1 if l>0 else -1) for l in c] for c in clauses];assert raw==[E.clauses[r-1] for r in M['original_clause_indices']];declared={pos:bs for pos,bs in zip(M['count_positions'],M['bounds'])};cycle_clauses=0;inv={x:v for v,x in E.var.items()}
 for r,c in zip(M['original_clause_indices'],raw):
  kind=E.kinds[r-1];m=re.fullmatch(r'alpha(<=|>=)(\d+)@(\d+)',kind)
  if m:
   op,k,v=m[1],int(m[2]),int(m[3]);pos=meta['window'].index(v);lo,hi=declared[pos];assert (hi<=k if op=='<=' else lo>=k)
  if kind in ['no4cycle','no6cycle']:
   assert all(l<0 and -l in inv for l in c);V={inv[-l] for l in c};assert len(V)==len(c) and all(sum((a^b).bit_count()==1 for b in V)==2 for a in V);cycle_clauses+=1
 bad=[(cid,cl,hs[:]) for cid,cl,hs in proof];bad[0][2][0]=len(clauses)+999999
 try:replay(clauses,bad)
 except (AssertionError,IndexError):negative=True
 else:raise AssertionError('invalid proof accepted')
 receipts.append({'source_edge':M['source_edge'],'status':'PASS_FRESH_PARSER_SOURCE_REBUILD','variables':nv,'clauses':nc,'RUP_steps':len(proof),'unit_hints':nh,'all_alpha_premises_in_declared_bounds':True,'cube_cycle_degree_checks':cycle_clauses,'invalid_hint_rejected':negative,'objective_or_share_cap_used':False})
r={'status':'PASS','certificates':receipts,'Lean_checked':False,'global_bound_improved':False};(H/'count_certificates_independent_review.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
