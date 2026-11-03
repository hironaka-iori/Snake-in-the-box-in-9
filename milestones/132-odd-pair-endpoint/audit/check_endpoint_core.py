"""Independent original-clause, native RUP and endpoint-geometry review."""
from pathlib import Path
from collections import Counter
from itertools import combinations
import ast,datetime,hashlib,json,time

H=Path(__file__).resolve().parents[1];R=H.parents[1];W=H/'work/certificate';pins={}
def sha(p):
 p=Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 value=h.hexdigest();pins[p.relative_to(R).as_posix()]=value;return value
def read(p):sha(p);return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def formula(p):
 sha(p);lines=Path(p).read_text().splitlines();head=lines[0].split()
 assert head[:2]==['p','cnf'];nv,nc=map(int,head[2:]);clauses=[]
 for line in lines[1:]:
  xs=list(map(int,line.split()));assert xs[-1]==0 and all(0<abs(x)<=nv for x in xs[:-1]);clauses.append(xs[:-1])
 assert len(clauses)==nc;return nv,clauses
def extract_class(p,name):
 sha(p);tree=ast.parse(Path(p).read_text());cls=next(n for n in tree.body if isinstance(n,ast.ClassDef) and n.name==name)
 scope={'combinations':combinations};exec(compile(ast.Module(body=[cls],type_ignores=[]),str(p),'exec'),scope)
 return scope[name]
def main():
 start=time.monotonic();sha(Path(__file__))
 metadata=read(H/'data/encoding.json');native=read(H/'data/native-certificate.json')
 assert native['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY'
 for name,digest in native['preserved_files_sha256'].items():assert sha(W/name)==digest
 for rel,digest in native['source_files_sha256'].items():assert sha(R/rel)==digest
 nv,clauses=formula(H/'work/base.cnf');assert (nv,clauses)==formula(W/'input.cnf')
 assert sha(H/'work/base.cnf')==metadata['cnf_sha256']
 T=extract_class(R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py','TaggedEncoding')
 E=extract_class(R/'milestones/10-window-aggregate/scripts/wincert.py','Encoding')
 window=[0,1,3,7,6,14,10];bounds=[[0,21]]*5
 enc=T(window,bounds,radius=9);plain=E(window,[tuple(b) for b in bounds],radius=9)
 assert enc.clauses==plain.clauses and enc.nv==plain.nv
 assert enc.ball==list(range(512)) and enc.nv==metadata['base_variables']
 assert len(enc.clauses)==metadata['base_clauses']
 assert metadata['window']==window and metadata['directions']==[0,1,2,0,3,2]
 assert metadata['bounds']==bounds and metadata['radius']==9
 corners=[]
 for i in [2,4]:
  used={(window[i]^window[i-1]).bit_length()-1,(window[i]^window[i+1]).bit_length()-1}
  row=[window[i]^(1<<a)^(1<<b) for a,b in combinations(range(9),2) if a not in used and b not in used]
  assert len(row)==len(set(row))==21;corners.append(row)
 literals=[-(v+1) for row in corners for v in row]
 assert corners==metadata['corner_lists'] and literals==metadata['pair_literals']
 assert len(literals)==42 and len(set(literals))==37
 repeated={-x-1:n for x,n in Counter(literals).items() if n>1}
 assert repeated=={18:2,34:2,66:2,130:2,258:2}
 pair_start=len(enc.clauses);enc.atmost(literals,9,('pair_counterexample_cap',));pair_end=len(enc.clauses)
 assert [pair_start,pair_end]==metadata['pair_clause_interval_zero_based']
 # Independently rebuild the pair sequential counter's exact literal occurrences.
 first_var=metadata['base_variables']+1
 reg=lambda i,j:first_var+9*i+j
 rebuilt=[[-literals[0],reg(0,0)]]+[[-reg(0,j)] for j in range(1,9)]
 for i in range(1,42):
  rebuilt.extend([[-literals[i],reg(i,0)],[-reg(i-1,0),reg(i,0)]])
  for j in range(1,9):rebuilt.extend([[-literals[i],-reg(i-1,j-1),reg(i,j)],[-reg(i-1,j),reg(i,j)]])
  rebuilt.append([-literals[i],-reg(i-1,8)])
 assert rebuilt==enc.clauses[pair_start:pair_end]
 for parity in [0,1]:
  row=[513+v for v in range(512) if v.bit_count()%2==parity]
  assert row==metadata[['even_endpoint_clause','odd_endpoint_clause'][parity]]
  enc.add(row,(['one_even_endpoint','one_odd_endpoint'][parity],))
 common=[v for v in range(512) if (v^3).bit_count()==(v^6).bit_count()==2]
 assert common==metadata['forbidden_common_sphere'] and len(common)==14
 for v in common:enc.add([-(513+v)],('endpoint_not_common_two',v))
 assert enc.nv==nv==2426 and len(enc.clauses)==96552 and enc.clauses==clauses
 assert json.loads(json.dumps(enc.meaning))==metadata['variable_meaning']
 assert json.loads(json.dumps(enc.ctrs))==metadata['counters']
 ids=read(W/'core-ids.json');assert ids==sorted(set(ids)) and len(ids)==683
 cv,core=formula(W/'core.cnf');assert cv==nv and core==[clauses[i-1] for i in ids]
 tags=[enc.tags[i-1] for i in ids];tagcounts=dict(Counter(t[0] for t in tags))
 assert tagcounts==dict(window=7,deg2=192,lowEnd=32,cut=10,first=13,mono=219,step=189,over=14,endpoint_not_common_two=7)
 assert all(t[1]==1 for t in tags if t[0] in ['first','zero','mono','step','over'])
 cuts=[]
 for cid,t,c in zip(ids,tags,core):
  if t[0]!='cut':continue
  vertices=[-x-1 for x in c];assert len(vertices)==len(set(vertices))==6
  degrees=[sum((v^u).bit_count()==1 for u in vertices) for v in vertices]
  assert degrees==[2]*6;cuts.append(dict(original_clause_id=cid,vertices=vertices))
 used=[t[1] for t in tags if t[0]=='endpoint_not_common_two']
 assert used==[0,10,18,34,66,130,258]
 unused=[v for v in common if v not in used]
 assert unused==[5,15,23,39,71,135,263]
 assert all(v not in window and (v^7).bit_count()==1 for v in unused)
 assert (7^3).bit_count()==(7^6).bit_count()==1 and 3!=6
 assert not any(pair_end+offset in ids for offset in [1,2])
 # Independent signed-literal propagation replay from only the selected original clauses.
 proof=W/'trimmed.lrat';sha(proof);db={i:clauses[i-1] for i in ids}
 seen=set();last=len(clauses);deductions=hints=0;final=None
 with proof.open() as f:
  for line in f:
   xs=list(map(int,line.split()));z=xs.index(0,1)
   cid=xs[0];claim=xs[1:z];reasons=xs[z+1:-1]
   assert xs[-1]==0 and cid>last and cid not in db
   assert all(0<abs(x)<=nv for x in claim)
   truth={-x for x in claim};conflict=any(-x in truth for x in truth)
   for reason in reasons:
    assert 0<reason<cid and reason in db
    if reason<=len(clauses):seen.add(reason)
    if conflict:continue
    clause=db[reason]
    assert not any(x in truth for x in clause)
    pending={x for x in clause if -x not in truth}
    assert len(pending)<=1
    if pending:truth.update(pending)
    else:conflict=True
   assert conflict
   db[cid]=claim;last=cid;final=claim;deductions+=1;hints+=len(reasons)
 assert final==[] and deductions==13299 and hints==554859 and seen==set(ids)
 # Exhaustive local truth checks of the sequential-counter schemas, including repeated inputs.
 schema_cases=0
 for old_count in range(42):
  for bit in [0,1]:
   new_count=old_count+bit
   assert not bit or new_count>=1
   for j in range(1,10):
    assert old_count<j or new_count>=j
    if j<9:assert not(bit and old_count>=j) or new_count>=j+1
   if new_count<=9:assert not(bit and old_count>=9)
   schema_cases+=1
 out=dict(status='PASS_ORIGINAL_CORE_NATIVE_REPLAY_AND_GEOMETRY_REVIEW',
  original_variables=nv,original_clauses=len(clauses),core_clauses=len(ids),
  core_original_ids=ids,core_clause_tags=[dict(original_id=i,clause=c,tag=t) for i,c,t in zip(ids,core,tags)],
  tag_counts=tagcounts,pair_counter_clauses=435,base_clauses=241,endpoint_units=7,
  original_clause_order_and_multiplicity_preserved=True,full_tagged_and_plain_encoding_equal=True,
  pair_occurrences=42,pair_unique_vertices=37,repeated_corner_multiplicities=repeated,
  pair_counter_schema_cases=schema_cases,core_counters_used=[1],
  positive_parity_clauses_used=False,endpoint_budget_counter_used=False,
  used_endpoint_vertices=used,unused_common_vertices=unused,
  unused_vertex_obstruction='Each is a third selected neighbour of internal window vertex7, whose path neighbours3 and6 are already selected.',
  six_cycle_cuts=cuts,native_rup=dict(deductions=deductions,hints=hints,all683_original_premises_used=True,final_empty=True),
  geometric_conclusion='For an actual fitting canonical012032 window of any snake length, pair count at most9 forces one of the two actual endpoints to be at Hamming distance2 from both internal centres.',
  remaining_obligations=['Kernel-check the exact exported refutation, with any variable renaming checked as a bijection.',
   'Interpret selected clauses under actual path selection and actual endpoint flags, including the10 six-cycle exclusions.',
   'Identify each centre count with the21 allowed absent corners, retaining all42 occurrences across the pair.',
   'Give every sequential register its prefix-occurrence meaning and derive the selected pair-counter clauses from pair<=9.',
   'Derive the seven negative endpoint units from negation of the claimed same-endpoint conclusion.',
   'Transport the normalized window and both endpoint distances through a cube automorphism.',
   'Combine the semantic assignment with the refutation and expose the actual-snake theorem with no external UNSAT premise.'],
  limitations=['The native replay certifies a finite CNF contradiction; Lean and actual-snake assembly are separate obligations.',
   'Absence of parity and endpoint-budget premises in this certificate does not assert minimality of the core.',
   'No global snake bound or endpoint-occurrence budget is proved by this review.'],
  completed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-start,source_files_sha256=pins)
 destination=H/'data/endpoint-core-review.json';assert not destination.exists()
 destination.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
 print(json.dumps({k:v for k,v in out.items() if k not in ['core_original_ids','core_clause_tags','six_cycle_cuts','source_files_sha256']},indent=2))
if __name__=='__main__':main()
