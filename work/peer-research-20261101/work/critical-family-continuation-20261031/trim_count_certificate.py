"""Extract a pure original-geometric count-window refutation from an auxiliary run.
Verify no objective/gate premise is used; retain exact original-row provenance.
"""
from pathlib import Path
import json,gzip,sys,collections,hashlib
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H.parent/'branch241-review'));from rup_check import check
D=json.loads(gzip.decompress((H/'weighted_face_probes/cap15.json.gz').read_bytes()));n=len(D['clauses']);nb=D['meta']['base_clauses'];P=D['proof'];wanted={n+len(P)};original=set()
for j in range(len(P)-1,-1,-1):
 if n+j+1 not in wanted:continue
 for h in P[j]['hints']:
  if h<=n:original.add(h)
  else:wanted.add(h)
assert max(original)<=nb
rows=sorted(original);derived=[j for j in range(len(P)) if n+j+1 in wanted];cid={old:k+1 for k,old in enumerate(rows)};cid.update({n+j+1:len(rows)+k+1 for k,j in enumerate(derived)})
clauses=[D['clauses'][i-1] for i in rows];proof=[{'clause':P[j]['clause'],'hints':[cid[h] for h in P[j]['hints']]} for j in derived]
variables=sorted({abs(l) for c in clauses+[p['clause'] for p in proof] for l in c});vid={v:k+1 for k,v in enumerate(variables)};lit=lambda l:vid[abs(l)]*(1 if l>0 else -1)
clauses=[[lit(l) for l in c] for c in clauses];proof=[{'clause':[lit(l) for l in p['clause']],'hints':p['hints']} for p in proof];receipt=check(clauses,proof)
sys.path.insert(0,str(H));from zero_share_probe import build
byid={e['source_edge']:e for e in json.loads((H/'filtered_critical_edges.json').read_text())};E,meta=build(byid[1657683]);assert E.clauses[:nb]==D['clauses'][:nb]
kinds=collections.Counter(E.kinds[i-1] for i in rows);O=H/'count_window_certificate';O.mkdir(exist_ok=True)
with (O/'core.cnf').open('w') as f:
 f.write(f'p cnf {len(variables)} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
with (O/'proof.lrat').open('w') as f:
 for i,p in enumerate(proof):f.write(str(len(clauses)+i+1)+' '+' '.join(map(str,p['clause']))+' 0 '+' '.join(map(str,p['hints']))+' 0\n')
info={'status':'PURE_GEOMETRIC_COUNT_CORE_UNSAT_RUP_CHECKED','variables':len(variables),'original_clauses':len(clauses),'proof_check':receipt,'directions':byid[1657683]['directions'],'count_positions':[3,4,5,7],'bounds':[[3,3],[0,5],[0,3],[0,5]],'all_other_internal_counts_unconstrained':True,'source_wincert_sha256':meta['source_wincert_sha256'],'source_base_clauses':nb,'original_clause_indices':rows,'variable_mapping_new_to_source':variables,'input_clause_kinds':dict(kinds),'share_cap_used':False,'face_definition_clauses_used':False,'global_bound_improved':False,'Lean_checked':False}
info['files_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [O/'core.cnf',O/'proof.lrat']};(O/'manifest.json').write_text(json.dumps(info,indent=2)+'\n')
print(json.dumps({k:v for k,v in info.items() if k not in ['original_clause_indices','variable_mapping_new_to_source']},indent=2))
