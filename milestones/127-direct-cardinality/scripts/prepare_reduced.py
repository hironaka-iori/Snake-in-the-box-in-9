"""Replace six lower-bound counter families by their proved direct clauses."""
from pathlib import Path
import hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sys.dont_write_bytecode=True
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/solver_packages')]
from gen_lean_sat import TaggedEncoding
case=read(R/'milestones/125-critical-six-count/data/probes/0120324-total22-positive.json')
enc=TaggedEncoding(case['window'],case['bounds'],radius=9)
corners=read(H/'data/direct-clauses.json')['corner_lists']
enc.atmost(sorted(-enc.var[v] for cs in corners for v in cs),22,('unproved_sum',))
for cut in case['cycle_cuts']:enc.add([-enc.var[v] for v in cut],('cut',))
original=(f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode()
assert original==(H/'work/original.cnf').read_bytes()
lower={i for i,(_,_,kind) in enumerate(enc.ctrs) if kind[0]=='lo'};assert len(lower)==6
aux={v for v,m in enc.meaning.items() if m[0]=='r' and m[1] in lower};assert len(aux)==2457
families={'first','zero','mono','step','over'}
removed=[];kept=[];mapping=[]
for cid,(clause,tag) in enumerate(zip(enc.clauses,enc.tags),1):
 if tag[0] in families and tag[1] in lower:removed.append(cid)
 else:
  assert not any(abs(x) in aux for x in clause)
  kept.append(clause);mapping.append(cid)
assert len(removed)==4917 and len(kept)==101431
rows=read(H/'data/direct-clauses.json')['rows']
kept.extend(x['clause'] for x in rows);mapping.extend(x['id'] for x in rows)
assert len(kept)==len(mapping)==101666 and len(set(mapping))==len(mapping)
path=H/'work/reduced.cnf';assert not path.exists()
path.write_bytes((f'p cnf {enc.nv} {len(kept)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in kept)).encode())
out=dict(status='PREPARED_REDUCED_COUNTER_ENCODING',original_clauses=106348,prelude_clauses=235,reduced_clauses=len(kept),declared_variables=enc.nv,occurring_variables=len({abs(x) for c in kept for x in c}),removed_clauses=removed,removed_auxiliary_variables=sorted(aux),input_id_map=mapping,original_sha256=sha(H/'work/original.cnf'),prelude_sha256=sha(H/'work/prelude.lrat'),reduced_sha256=sha(path),script_sha256=sha(Path(__file__)),proof_id_rule='For native ID x <=101666 use input_id_map[x-1]; otherwise use106583+x-101666. Map clauses, hints and deletions; prepend235 original-input derivations and replay against106348 original clauses.',scope='Every reduced input is an original clause or one of the proved direct clauses. A contradiction can be transported to the original formula. No native search or complete contradiction is asserted by this record.')
(H/'data/reduced.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['removed_clauses','removed_auxiliary_variables','input_id_map']},indent=2))
