"""Reconstruct the verified012301 input and prepare its exact core interpretation."""
from pathlib import Path
import hashlib,json,sys,time
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/145-countfree-012301'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
    d=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):d.update(b)
    return d.hexdigest()
def write(p,s):
    p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists(),p
    p.write_text(s,encoding='utf-8',newline='\n')
def replace(s,a,b):
    assert a in s,a
    return s.replace(a,b)
start=time.monotonic();replay=read(P/'data/direct-replay.json')
assert replay['status']=='PASS_COMPLETE_DIRECT_RUP_REPLAY'
for p,d in replay['source_files_sha256'].items():
    p=Path(p);assert sha(p if p.is_absolute() else R/p)==d
native=R/'milestones/72-four-count-proof-closure/critical-current/data/pysat3-cap15-certificate.json'
meta=read(native);assert meta['status']=='NATIVE_DRAT_VERIFIED' and meta['cap']==15
assert meta['directions']==[0,1,2,3,0,1] and meta['bounds']==[[0,21]]*5 and len(meta['cycle_cuts'])==16
original=R/'milestones/72-four-count-proof-closure/critical-current/build/pysat3-cap15.cnf'
core=P/'work/conversion-long/core.cnf';ids=P/'work/conversion-long/core-ids.json';proof=P/'work/conversion-long/trimmed.lrat'
assert sha(original)==meta['cnf_sha256']
meta['core_sha256']=sha(core)
write(H/'data/native-reference.json',json.dumps(meta,indent=2)+'\n')
variables=set();deductions=0
with proof.open(encoding='ascii') as f:
    for line in f:
        head,tail=line.split(' 0 ',1)
        values=list(map(int,head.split()))
        variables.update(abs(v) for v in values[1:]);deductions+=1
assert deductions==285541
write(H/'data/proof-variables.json',json.dumps(sorted(variables))+'\n')
template=R/'milestones/72-four-count-proof-closure/critical-current/scripts/prepare_lean.py'
s=template.read_text()
s=replace(s,"ROOT=HERE.parents[2];OUT=HERE/'share-proof'","ROOT=HERE.parents[1];OUT=HERE")
s=replace(s,"HERE/'data/general8-cap11-certificate.json'","HERE/'data/native-reference.json'")
s=replace(s,"HERE/'build/general8-cap11.cnf'","ROOT/'milestones/72-four-count-proof-closure/critical-current/build/pysat3-cap15.cnf'")
s=replace(s,"HERE/'build/general8-cap11.core.cnf'","ROOT/'milestones/145-countfree-012301/work/conversion-long/core.cnf'")
s=replace(s,"meta['bounds'],11)","meta['bounds'],15)")
s=replace(s,'cap : Nat := 11','cap : Nat := 15')
s=replace(s,"prior={'cycle_cuts':[]}","prior={'cycle_cuts':meta['cycle_cuts']}")
s=replace(s,'indices=[lookup[tuple(sorted(c))] for c in core];tags=[e.tags[i] for i in indices]',
    "indices=[i-1 for i in read(ROOT/'milestones/145-countfree-012301/work/conversion-long/core-ids.json')]\nassert len(indices)==len(core) and all(e.clauses[i]==c for i,c in zip(indices,core))\ntags=[e.tags[i] for i in indices]")
s=replace(s,'active={abs(x) for c in core for x in c};needed=set(active)',
    "active={abs(x) for c in core for x in c} | set(read(HERE/'data/proof-variables.json'));needed=set(active)")
s=s.replace('ShareWindow12','ShareWindow146').replace('Share12','Share146').replace('share12','share146')
# Import the exact checked combined catalogue to provide the existing generic models.
# Its receipt pins the supporting definitions; no imported local floor is assumed by the generated CNF.
s=replace(s,"body='import LocalWindowShareModel\\n'","body='import Port98CombinedCatalogue\\n'")
s=replace(s,'import LocalWindowTagsPacked\\nimport LocalWindowTagsSharePacked\\n','import Port98CombinedCatalogue\\n')
generator=H/'scripts/generated_prepare_012301.py';write(generator,s)
exec(compile(s,str(generator),'exec'),{'__file__':str(generator),'__name__':'prepare146'})
sem=read(H/'data/share146.json');assert sem['source_original_clause_ids']==read(ids)
assert sem['clauses']==12977 and sem['shards']==102
files=[H/'lean/LocalWindowCnf/ShareWindow146.lean',*sorted((H/'lean/Share146').glob('*.lean'))]
assert len(files)==105
j=dict(status='PREPARED_EXACT_012301_CORE_INTERPRETATION_LEAN_PENDING',directions=meta['directions'],cap=15,target=16,
    full_input_clauses=92656,core_clauses=12977,original_cycle_cuts=16,retained_cycle_cuts=6,
    proof_variables=len(variables),active_variables=sem['active_variables'],semantic_variables=sem['semantic_variables'],
    preserved_original_clause_ids=True,variables_from_entire_proof_included=True,
    module_order=['LocalWindowCnf.ShareWindow146','Share146.Data','Share146.Structure']+[f'Share146.Shard{i:02d}' for i in range(102)],
    artifacts=[dict(path=p.relative_to(H).as_posix(),sha256=sha(p)) for p in files],
    source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in [Path(__file__),template,generator,native,original,core,ids,proof,P/'data/direct-replay.json',H/'data/proof-variables.json']},
    seconds=time.monotonic()-start,
    scope='Exact tagged clause interpretation prepared from the verified full input/core; compilation, full contradiction replay and actual-snake theorem remain separate obligations.')
write(H/'data/semantic-plan.json',json.dumps(j,indent=2)+'\n');print(json.dumps({k:j[k] for k in ['status','core_clauses','active_variables','semantic_variables','seconds']}))
