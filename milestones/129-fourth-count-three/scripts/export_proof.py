"""Export the independently replayed smaller core with an audited 13-bit checker."""
from pathlib import Path
import hashlib,importlib.util,json,re,sys,time
from collections import Counter
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.dont_write_bytecode=True
sys.path.insert(0,str(H/'scripts'))
from encoding import build
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def write(p,data):
 p.parent.mkdir(parents=True,exist_ok=True)
 if isinstance(data,str):data=data.encode('utf-8')
 with p.open('xb') as f:f.write(data)
meta=read(H/'data/core2-search.json');review=read(H/'data/transport-review.json')
assert meta['status']=='CORE_PROOF_TRIMMED_REPLAY_PENDING'
assert sha(H/'work/core2-unsat.mapped.lrat')==meta['mapped_sha256']
for name,d in review['source_files_sha256'].items():assert sha(R/name)==d,name
enc=build();ids=meta['core_ids'];active=set(meta['active_variable_ids'])
assert len(active)==1695 and meta['hints']==2628221 and len(ids)==3500
order=sorted(active)+sorted(set(range(1,enc.nv+1))-active)
rename={v:i+1 for i,v in enumerate(order)}
def lit(x):return rename[abs(x)]*(1 if x>0 else -1)
full=[[lit(x) for x in c] for c in enc.clauses]
tags=[enc.tags[i-1] for i in ids]
used={t[1] for t in tags if t[0] in ['first','zero','mono','step','over']}
assert used=={0,4,11,12}
needed=active|set(range(1,1025))
meaning={rename[v]:enc.meaning[v] for v in sorted(needed)}
ctrs=[]
for i,(ls,k,kind) in enumerate(enc.ctrs):
 if i in used:
  assert {abs(x) for x in ls}<=needed
  ctrs.append(dict(index=i,literals=[lit(x) for x in ls],upper=k,kind=kind))
 else:ctrs.append(dict(index=i,dummy=True))
proofdir=H/'work/export';proofdir.mkdir(exist_ok=True)
write(proofdir/'triple129.cnf',f'p cnf {enc.nv} {len(full)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in full))
source=H/'work/core2-unsat.mapped.lrat';target=proofdir/'triple129.lrat'
with source.open() as src,target.open('x',encoding='ascii',newline='\n') as out:
 for line in src:
  ns=list(map(int,line.split()));z=ns.index(0,1)
  assert all(abs(x) in active for x in ns[1:z])
  out.write(' '.join(map(str,[ns[0],*[lit(x) for x in ns[1:z]],0,*ns[z+1:]]))+'\n')
metadata=proofdir/'meta';metadata.mkdir()
write(metadata/'triple129.json',json.dumps(dict(module='LocalWindowCnf.Triple129',core_ids=ids),indent=2)+'\n')
cnf='''import LocalWindowDirModel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.Triple129
noncomputable def window : List Nat := winOf [0,1,2,0,3,2,4]
noncomputable def bounds : List (Nat × Nat) := [(0,21),(0,21),(0,21),(3,3),(0,21),(0,21)]
noncomputable def raw : List (List Nat) := [
'''+',\n'.join('  '+str([2*abs(x)+(x<0) for x in full[i-1]]) for i in ids)+'''
]
noncomputable def cnf : List (List Int) := raw.map (·.map decodeLit)
end Snake9.LocalWindow.Triple129
'''
cnfpath=H/'lean/Recovered129G/LocalWindowCnf/Triple129.lean';write(cnfpath,cnf)
semantic=dict(status='SELECTED_CORE_DATA_ACTUAL_SEMANTICS_PENDING',namespace='Snake9.LocalWindow.Triple129',
 cnf_module='Recovered129G.LocalWindowCnf.Triple129',old_to_new=rename,meaning=meaning,counters=ctrs,
 tags=tags,raw=[[2*abs(x)+(x<0) for x in full[i-1]] for i in ids],core_ids=ids,
 window=[0,1,3,7,6,14,10,26],bounds=[[0,21],[0,21],[0,21],[3,3],[0,21],[0,21]],
 used_counter_indices=sorted(used),proof_active_variables=len(active),semantic_variable_meanings=len(meaning),
 max_semantic_variable=max(meaning),counter_tag_counts=dict(Counter(t[1] for t in tags if t[0] in ['first','zero','mono','step','over'])),
 cnf_source_sha256=sha(cnfpath),selection_sha256=sha(H/'data/core2-search.json'),script_sha256=sha(Path(__file__)),
 scope='Retains every primary and endpoint input meaning needed by the four counters. All other counters are dummy. Only proof-active variables must be below the literal offset; unused geometric hypotheses are not assumed.')
write(H/'data/selected-core-semantics.json',json.dumps(semantic,indent=2)+'\n')
generator=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py'
sp=importlib.util.spec_from_file_location('export129lrat',generator);lr=importlib.util.module_from_spec(sp);sp.loader.exec_module(lr)
lemmas=lr.read_lrat(str(target));plan=lr.plan(ids,lemmas);slots=plan[3]
assert slots==6902 and slots<=8191 and len(active)<2400
assert max(len(row[1]) for row in lemmas)<255 and max(len(row[2]) for row in lemmas)<4095
receipt=R/'milestones/112-critical-sum-refinement/data/Refined112.LocalWindowUnsat.Sum3142.Data0-audit.json'
audit=read(receipt);matches=[(R/name,d) for name,d in audit['dependencies'].items() if name.endswith('/LratFast.olean')]
assert len(matches)==1 and audit['exit_code']==0
checker,d=matches[0];assert sha(checker)==d
lr.set_width(13,fast=True,off=2400);lr.DATA_DEF='noncomputable def';lr.GROUPED=True
lr.read_lrat=lambda p:lemmas
lr.plan=lambda c,l:plan
generated=H/'generated';generated.mkdir()
t=time.monotonic()
stats=lr.export('triple129',str(proofdir),6000,4,4,True,str(generated),str(metadata))
assert stats['simulated'] and (stats['lemmas'],stats['hints'],stats['slots'])==(50082,2628221,6902)
files=[]
for p in generated.rglob('*.lean'):
 s=p.read_text(encoding='utf-8')
 s=re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.Triple129(?:\.[A-Za-z0-9]+)?)$',r'import Recovered129G.\1',s,flags=re.M)
 if p.name=='Triple129.lean':s+='\n#print axioms Snake9.LocalWindow.Triple129.unsat\n'
 q=H/'lean/Recovered129G'/p.relative_to(generated);write(q,s);files.append(q)
files.append(cnfpath)
names={p.relative_to(H/'lean').as_posix()[:-5].replace('/','.'):p for p in files}
order=[];remaining=set(names)
while remaining:
 ready=sorted(n for n in remaining if not set(re.findall(r'^import ([\w.]+)$',names[n].read_text(),re.M))&remaining)
 assert ready
 order.extend(ready);remaining-=set(ready)
out=dict(status='EXPORTED_AND_SIMULATED_LEAN_REPLAY_PENDING',stats=stats,seconds=time.monotonic()-t,
 module_order=order,artifacts=[dict(path=p.relative_to(H).as_posix(),sha256=sha(p)) for p in files],
 checker_module='LratFast',checker_object=str(checker),checker_object_sha256=d,checker_receipt=str(receipt),checker_receipt_sha256=sha(receipt),
 exporter_sha256=sha(Path(__file__)),generator_sha256=sha(generator),encoding_sha256=sha(H/'scripts/encoding.py'),
 selected_certificate_sha256=sha(H/'data/core2-search.json'),transport_review_sha256=sha(H/'data/transport-review.json'),
 semantic_data_sha256=sha(H/'data/selected-core-semantics.json'),
 scope='Complete Python simulation of the packed selected proof. Every Lean replay module and the actual-snake semantic interpretation still must pass; no actual triple lower bound is claimed by this export.')
write(H/'data/proof-plan.json',json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['module_order','artifacts']},indent=2))
