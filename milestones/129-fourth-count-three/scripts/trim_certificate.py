"""Transport the native proof to tagged inputs, prepend proved direct clauses, and trim."""
from pathlib import Path
import hashlib,importlib.util,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def formula(p):
 ls=p.read_text().splitlines();nv,nc=map(int,ls[0].split()[2:])
 cs=[[int(x) for x in s.split()[:-1]] for s in ls[1:]];assert len(cs)==nc
 return nv,cs
search=read(H/'data/search.json');assert search['status']=='NATIVE_UNSAT_COMPLETE_REPLAY_PENDING'
raw=H/'work/three.raw.lrat';assert sha(raw)==search['raw_sha256']
old=R/'milestones/127-direct-cardinality';pair=R/'milestones/128-coupled-pair'
oldnv,original=formula(old/'work/original.cnf');nv,native=formula(H/'work/three.cnf')
pairclauses=read(pair/'data/pair-counter.json')['clauses']
branches=read(H/'data/branch-counters.json')['families'];extra=[c for f in branches for c in f['clauses']]
trusted=original+pairclauses+extra
assert (oldnv,nv,len(original),len(trusted),len(native))==(7277,10175,106348,112225,107543)
mapping=read(old/'data/reduced.json')['input_id_map'];prelude=read(old/'data/direct-clauses.json')['rows']
assert len(mapping)==101666 and len(prelude)==235
assert native==[original[i-1] if i<=106348 else prelude[i-106349]['clause'] for i in mapping]+pairclauses+extra
def remap(i):
 if i<=101666:
  oldid=mapping[i-1]
  return oldid if oldid<=106348 else 112225+oldid-106348
 if i<=107543:return 106348+i-101666
 return 112460+i-107543
full=H/'work/expanded.cnf';mapped=H/'work/expanded.raw.lrat';trim=H/'work/expanded.trim.lrat';core=H/'work/core.cnf'
assert not any(p.exists() for p in [full,mapped,trim,core])
full.write_bytes((f'p cnf {nv} {len(trusted)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in trusted)).encode())
steps=hints=deletions=0;last=len(native);empty=False;t=time.monotonic()
with mapped.open('x',encoding='ascii',newline='\n') as out:
 for row in prelude:
  cid=112225+row['id']-106348
  assert cid>112225 and all(0<h<=106348 for h in row['hints'])
  out.write(' '.join(map(str,[cid,*row['clause'],0,*row['hints'],0]))+'\n')
 with raw.open() as stream:
  for line in stream:
   p=line.split()
   if len(p)>1 and p[1]=='d':deletions+=1;continue
   ns=list(map(int,p));z=ns.index(0,1);cid=ns[0];cl=ns[1:z];hs=ns[z+1:-1]
   assert ns[-1]==0 and cid>last and all(0<h<cid for h in hs)
   last=cid;steps+=1;hints+=len(hs);empty=not cl
   out.write(' '.join(map(str,[remap(cid),*cl,0,*[remap(h) for h in hs],0]))+'\n')
assert empty
sys.dont_write_bytecode=True
generator=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
sp=importlib.util.spec_from_file_location('trim129',generator);g=importlib.util.module_from_spec(sp);sp.loader.exec_module(g)
nl,nh,ids=g.trim_lrat(str(mapped),str(trim),len(trusted))
core.write_bytes((f'p cnf {nv} {len(ids)}\n'+''.join(' '.join(map(str,trusted[i-1]))+' 0\n' for i in ids)).encode())
active={abs(x) for i in ids for x in trusted[i-1]}
maxcl=max(len(trusted[i-1]) for i in ids);maxh=0
for line in trim.open():
 ns=list(map(int,line.split()));z=ns.index(0,1);active.update(abs(x) for x in ns[1:z]);maxcl=max(maxcl,z-1);maxh=max(maxh,len(ns)-z-2)
out=dict(status='TRANSPORTED_AND_TRIMMED_REPLAY_PENDING',native_inputs=len(native),tagged_inputs=len(trusted),
 prepended_direct_clauses=235,native_deductions=steps,native_hints=hints,omitted_deletion_records=deletions,
 core_ids=ids,core_clauses=len(ids),lemmas=nl,hints=nh,active_variables=len(active),max_clause_length=maxcl,max_step_hints=maxh,
 active_variable_ids=sorted(active),seconds=time.monotonic()-t,script_sha256=sha(Path(__file__)),trimming_generator_sha256=sha(generator),
 source_pins={p.relative_to(R).as_posix():sha(p) for p in [old/'work/original.cnf',old/'data/reduced.json',old/'data/direct-clauses.json',pair/'data/pair-counter.json',H/'data/branch-counters.json',H/'data/search.json',raw,H/'work/three.cnf']},
 cnf_sha256=sha(full),mapped_sha256=sha(mapped),trim_sha256=sha(trim),core_sha256=sha(core),
 scope='Expanded trusted input is the old106348 clauses plus the proved-geometric pair and new branch counters. The235 direct clauses are prepended as original-input RUP derivations. No new geometric counter is claimed to follow from the old input alone. Complete replay and Lean interpretation remain necessary.')
p=H/'data/trimmed-certificate.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['core_ids','active_variable_ids','source_pins']},indent=2))
