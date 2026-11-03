"""Rebuild share semantics and export the saved RUP proof; no solver or Lean run."""
from pathlib import Path
import hashlib,importlib.util,json,re,sys,time
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,s):
 p.parent.mkdir(parents=True,exist_ok=True)
 assert not p.exists(),p
 p.write_text(s,encoding='utf-8',newline='\n')
def js(p,j):write(p,json.dumps(j,indent=2)+'\n')
def replace(s,a,b):
 assert a in s,a
 return s.replace(a,b)
def load(p,name):
 spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
assert not (H/'data/proof-plan-base.json').exists()
start=time.monotonic();cert=H/'work/certificate-base';native=read(H/'data/native-base.json')
assert native['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY'
for p,d in native['source_files_sha256'].items():assert sha(R/p)==d
for p,d in native['preserved_files_sha256'].items():assert sha(cert/p)==d
template=R/'milestones/72-four-count-proof-closure/critical-current/scripts/prepare_lean.py'
lrpath=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py'
lr=load(lrpath,'lrat143');lemmas=lr.read_lrat(str(cert/'trimmed.lrat'))
assert len(lemmas)==native['lemmas'] and sum(len(h) for _,_,h in lemmas)==native['hints']
meta=dict(status='NATIVE_RUP_VERIFIED',directions=[0,1,2,0,3,4],bounds=[[0,21]]*5,cap=12,cnf_sha256=sha(cert/'input.cnf'),core_sha256=sha(cert/'core.cnf'))
js(H/'data/native-reference.json',meta)
proofvars=sorted({abs(x) for _,c,_ in lemmas for x in c})
js(H/'data/proof-variables.json',proofvars)
s=template.read_text(encoding='utf-8')
s=replace(s,"ROOT=HERE.parents[2];OUT=HERE/'share-proof'","ROOT=HERE.parents[1];OUT=HERE")
s=replace(s,"HERE/'data/general8-cap11-certificate.json'","HERE/'data/native-reference.json'")
s=replace(s,"'NATIVE_DRAT_VERIFIED'","'NATIVE_RUP_VERIFIED'")
s=replace(s,"HERE/'build/general8-cap11.cnf'","HERE/'work/certificate-base/input.cnf'")
s=replace(s,"HERE/'build/general8-cap11.core.cnf'","HERE/'work/certificate-base/core.cnf'")
s=replace(s,"meta['bounds'],11)","meta['bounds'],12)")
s=replace(s,'cap : Nat := 11','cap : Nat := 12')
s=replace(s,'active={abs(x) for c in core for x in c};needed=set(active)',"active={abs(x) for c in core for x in c} | set(read(HERE/'data/proof-variables.json'));needed=set(active)")
s=s.replace('ShareWindow12','ShareWindow143').replace('Share12','Share143').replace('share12','share143')
generator=H/'scripts/generated_prepare.py';write(generator,s)
exec(compile(s,str(generator),'exec'),{'__file__':str(generator),'__name__':'share143_semantics'})
sem=read(H/'data/share143.json');rename={int(k):v for k,v in sem['original_to_new'].items()}
ids=read(cert/'core-ids.json');assert sem['source_original_clause_ids']==ids
imap={old:new for new,old in enumerate(ids,1)}
def lit(x):return rename[abs(x)]*(1 if x>0 else -1)
newlemmas=[(i,[lit(x) for x in c],[imap[h] if h<=native['original_clauses'] else h for h in hs]) for i,c,hs in lemmas]
proof=H/'certificates/share143.lrat'
write(proof,''.join(' '.join(map(str,[i,*c,0,*hs,0]))+'\n' for i,c,hs in newlemmas))
assert all(h in imap for _,_,hs in lemmas for h in hs if h<=native['original_clauses'])
allocation=lr.plan(sem['core_ids'],newlemmas)
off=1<<sem['active_variables'].bit_length();bits=max(13,allocation[3].bit_length(),(off+sem['active_variables']+1).bit_length())
assert bits<=15,(off,bits,allocation[3])
variants=R/'milestones/10-window-aggregate/scripts/gen_checker_variants.py';v=load(variants,'variants143')
base=R/'work/final_lean/LratCheck.lean';fast=R/'work/final_lean/LratFast.lean'
s=v.variant(base.read_text(),13,off,'Lrat143','LratFast','LocalWindowModel')
s+='\n#print axioms Snake9.Lrat143.rawMask_true\n#print axioms Snake9.Lrat143.start_true\n'
write(H/'lean/LratCheck143.lean',s)
s=v.variant(fast.read_text(),bits,off,'Lrat143','LratFast143','LratCheck143')
s+='\n#print axioms Snake9.LratFast143.cp_true\n#print axioms Snake9.LratFast143.final_false\n'
write(H/'lean/LratFast143.lean',s)
lr.set_width(bits,True,4000);lr.OFF=off;lr.BASE_NS='Snake9.Lrat143'
lr.CHECKER_IMPORT='import LratFast143';lr.CHECKER_OPEN='open Snake9.LratFast143\nopen Snake9.Lrat143 (Tree TreeTrue andB)'
lr.DATA_DEF='noncomputable def';lr.GROUPED=True
lr.read_lrat=lambda _:newlemmas;lr.plan=lambda _i,_l:allocation
stats=lr.export('share143',str(H/'certificates'),6000,4,4,True,str(H/'lean'),str(H/'data'))
assert stats['simulated'] and stats['hints']==native['hints']
p=H/'lean/LocalWindowUnsat/ShareWindow143.lean'
p.write_text(p.read_text()+ '\n#print axioms Snake9.LocalWindow.ShareWindow143.unsat\n',encoding='utf-8')
old=R/'milestones/73-countfree-share-catalogue/cases/case7302'
for name in ['Compose','Refuted','Geometry']:
 s=(old/f'lean/Share7302/{name}.lean').read_text().replace('Share7302','Share143').replace('ShareWindow7302','ShareWindow143').replace('true7302','true143')
 if name=='Geometry':s=replace(s,'20 ≤','13 ≤')
 write(H/f'lean/Share143/{name}.lean',s)
assemble=R/'milestones/72-four-count-proof-closure/critical-current/scripts/assemble_countfree.py'
s=replace(assemble.read_text(),"OUT=HERE/'share-proof'","OUT=HERE").replace('ShareWindow12','ShareWindow143').replace('Share12','Share143').replace('share12','share143').replace('true12','true143')
ap=H/'scripts/generated_assemble.py';write(ap,s);exec(compile(s,str(ap),'exec'),{'__file__':str(ap),'__name__':'share143_assembly'})
revtemplate=R/'milestones/73-countfree-share-catalogue/cases/case7304/lean/Share7304/Reversal.lean'
s=revtemplate.read_text().replace('Share7304','Share143').replace('ShareWindow7304','ShareWindow143')
# Generate the reversed word for the target from the actual canonical7302 geometry.
gen=R/'milestones/73-countfree-share-catalogue/scripts/add_reversal.py'
s=gen.read_text();s=replace(s,"HERE=Path(__file__).resolve().parents[1]\nOUT=HERE/'cases'/f'case{int(sys.argv[1])}'","OUT=Path(__file__).resolve().parents[1]")
case=dict(selected=dict(directions=[0,1,2,0,3,4],required_share=13),prefix='Share143',namespace='ShareWindow143',case_number=143)
js(H/'data/case.json',case);rp=H/'scripts/generated_reversal.py';write(rp,s);exec(compile(s,str(rp),'exec'),{'__file__':str(rp),'__name__':'share143_reversal'})
files=sorted((H/'lean').rglob('*.lean'));names={p.relative_to(H/'lean').as_posix()[:-5].replace('/','.'):p for p in files}
pending=set(names);sequence=[]
while pending:
 ready=sorted(n for n in pending if not set(re.findall(r'^import ([\w.]+)$',names[n].read_text(),re.M))&pending)
 assert ready;sequence.extend(ready);pending-=set(ready)
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b','\n'.join(p.read_text() for p in files))
pinned=[Path(__file__),template,lrpath,variants,base,fast,assemble,gen,old/'lean/Share7302/Geometry.lean',H/'data/native-base.json',H/'data/preparation.json',cert/'input.cnf',cert/'trimmed.lrat',cert/'core-ids.json']
plan=dict(status='EXPORTED_AND_SIMULATED_LEAN_PENDING',stats=stats,module_order=sequence,final_module='Share143.Reversal',cnf_module='LocalWindowCnf.ShareWindow143',final_theorem='Snake9.LocalWindow.ShareWindow143.share_bound_rev',refuted_theorem='Snake9.LocalWindow.ShareWindow143.refuted',word_bits=bits,checker_offset=off,active_variables=sem['active_variables'],artifacts=[dict(path=p.relative_to(H).as_posix(),sha256=sha(p)) for p in files],source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in pinned},seconds=time.monotonic()-start,scope='Generated and simulated proof only. Lean, actual-window interpretation and reversal remain pending. No global bound.')
js(H/'data/proof-plan-base.json',plan)
print(json.dumps(dict(status=plan['status'],modules=len(files),active_variables=sem['active_variables'],offset=off,bits=bits,segments=stats['segments'],slots=stats['slots'],lean_bytes=stats['lean_bytes'])))
