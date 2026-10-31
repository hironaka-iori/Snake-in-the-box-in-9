"""Recover ordinary count exclusions when auxiliary objectives are not dependencies."""
from pathlib import Path
from collections import Counter
import json,gzip,sys,hashlib,re
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H));from zero_share_probe import build
sys.path.insert(0,str(H.parent/'branch241-review'));from rup_check import check
B={e['source_edge']:e for e in json.loads((H/'filtered_critical_edges.json').read_text())};registry=[]
for tag,eid in [('cap15',1657683),('offset4_cap15',1816745),('offset7_cap15',3557277)]:
 D=json.loads(gzip.decompress((H/f'weighted_face_probes/{tag}.json.gz').read_bytes()));n=len(D['clauses']);nb=D['meta']['base_clauses'];P=D['proof'];need={n+len(P)};original=set()
 for j in range(len(P)-1,-1,-1):
  if n+j+1 not in need:continue
  for x in P[j]['hints']:
   if x<=n:original.add(x)
   else:need.add(x)
 if not original or max(original)>nb:raise ValueError('not a pure original-count core: '+tag)
 rows=sorted(original);derived=[j for j in range(len(P)) if n+j+1 in need];rename={r:i+1 for i,r in enumerate(rows)};rename.update({n+j+1:len(rows)+i+1 for i,j in enumerate(derived)});cs=[D['clauses'][r-1] for r in rows];ps=[{'clause':P[j]['clause'],'hints':[rename[x] for x in P[j]['hints']]} for j in derived];vs=sorted({abs(l) for c in cs+[p['clause'] for p in ps] for l in c});vmap={v:i+1 for i,v in enumerate(vs)};L=lambda l:vmap[abs(l)]*(1 if l>0 else -1);cs=[[L(l) for l in c] for c in cs];ps=[{'clause':[L(l) for l in p['clause']],'hints':p['hints']} for p in ps];check_result=check(cs,ps)
 E,meta=build(B[eid]);assert E.clauses[:nb]==D['clauses'][:nb];bounds={};kinds=Counter(E.kinds[r-1] for r in rows)
 for kind in kinds:
  m=re.fullmatch(r'alpha(<=|>=)(\d+)@(\d+)',kind)
  if not m:continue
  op,k,v=m[1],int(m[2]),int(m[3]);position=meta['window'].index(v);bounds.setdefault(position,[0,21])
  if op=='<=':bounds[position][1]=min(bounds[position][1],k)
  else:bounds[position][0]=max(bounds[position][0],k)
 O=H/'count_window_certificates'/f'edge{eid}';O.mkdir(parents=True,exist_ok=True)
 with (O/'core.cnf').open('w') as f:
  f.write(f'p cnf {len(vs)} {len(cs)}\n')
  for c in cs:f.write(' '.join(map(str,c))+' 0\n')
 with (O/'proof.lrat').open('w') as f:
  for j,p in enumerate(ps):f.write(str(len(cs)+j+1)+' '+' '.join(map(str,p['clause']))+' 0 '+' '.join(map(str,p['hints']))+' 0\n')
 M={'status':'PURE_ORIGINAL_COUNT_CORE_UNSAT_CHECKED','source_edge':eid,'directions':B[eid]['directions'],'count_positions':sorted(bounds),'bounds':[bounds[i] for i in sorted(bounds)],'all_other_internal_counts_unconstrained':True,'variables':len(vs),'original_clauses':len(cs),'proof_check':check_result,'original_clause_indices':rows,'variable_mapping_new_to_source':vs,'source_wincert_sha256':meta['source_wincert_sha256'],'input_clause_kinds':dict(kinds),'uses_share_or_objective_assumption':False,'Lean_checked':False,'new_global_bound':None,'files_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [O/'core.cnf',O/'proof.lrat']}};(O/'manifest.json').write_text(json.dumps(M,indent=2)+'\n');registry.append({k:M[k] for k in ['source_edge','directions','count_positions','bounds','variables','original_clauses','proof_check']});print(json.dumps(registry[-1]),flush=True)
(H/'count_rule_registry.json').write_text(json.dumps(registry,indent=2)+'\n')
