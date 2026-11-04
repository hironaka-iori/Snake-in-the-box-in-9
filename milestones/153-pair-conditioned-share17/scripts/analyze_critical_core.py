"""Locate the exact count and share premises retained by the critical proof."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=H/'critical/work/critical17'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def cnf(p):
    rows=[];header=None
    for line in p.read_text(encoding='ascii').splitlines():
        if line.startswith('p '):header=list(map(int,line.split()[2:]));continue
        if not line or line.startswith('c'):continue
        values=list(map(int,line.split()));assert values[-1]==0 and 0 not in values[:-1];rows.append(values[:-1])
    assert header is not None and header[1]==len(rows)
    return header[0],rows
enc=read(P/'encoding.json');replay=read(P/'native-replay.json')
assert replay['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY'
for name,key in [('core.cnf','core_sha256'),('core-ids.json','core_ids_sha256'),('trimmed.lrat','trimmed_sha256'),('raw.lrat','raw_sha256')]:assert sha(P/name)==replay[key]
assert sha(P/'input.cnf')==enc['cnf_sha256'] and sha(P/'meanings.json.gz')==enc['meanings_sha256']
nv,clauses=cnf(P/'input.cnf');_,core=cnf(P/'core.cnf');ids=read(P/'core-ids.json')
assert ids==sorted(set(ids)) and core==[clauses[i-1] for i in ids]
meta=json.loads(gzip.decompress((P/'meanings.json.gz').read_bytes()))
assert len(meta['tags'])==len(clauses)
families=Counter();counter_overflows=Counter();share_families=Counter()
for index in ids:
    tag=meta['tags'][index-1]
    if tag[0]=='old':
        family=tag[1][0];families[family]+=1
        if family=='over':counter_overflows[tag[1][1]]+=1
    else:share_families[tag[0]]+=1
retained=[]
for ci,amount in sorted(counter_overflows.items()):
    lits,cap,kind=meta['ctrs'][ci]
    retained.append(dict(counter=ci,kind=kind,threshold=cap,overflow_clauses=amount,inputs=len(lits)))
usedvars={abs(x) for row in core for x in row};derived=set();deductions=0;last=None
with (P/'trimmed.lrat').open(encoding='ascii') as f:
    for line in f:
        prefix=line.split(' 0 ',1)[0];numbers=list(map(int,prefix.split()));deductions+=1
        derived.update(abs(x) for x in numbers[1:]);last=line
assert deductions==replay['deductions']==30305 and replay['hints']==1754767
assert all(1<=v<=nv for v in usedvars|derived)
out=dict(status='PASS_CRITICAL_CORE_INPUT_AND_PREMISE_AUDIT',core_clauses=len(core),deductions=deductions,
    propagation_references=replay['hints'],original_variables=nv,core_variables=len(usedvars),derived_variables=len(derived),
    old_clause_families=dict(families),share_clause_families=dict(share_families),retained_counter_overflows=retained,
    count_bounds=enc['bounds'],share_cap=16,extra_cycle_cuts=[],
    native_replay_complete=True,Lean_replay_complete=False,actual_snake_theorem_complete=False,new_global_upper_bound=False,
    source_files_sha256={str(p.relative_to(R)):sha(p) for p in [Path(__file__),P/'input.cnf',P/'core.cnf',P/'core-ids.json',
        P/'trimmed.lrat',P/'native-replay.json',P/'meanings.json.gz',P/'encoding.json']},
    scope='The retained core is an exact subset of the specified critical-context input. Overflow tags identify count assumptions used; no automatic weakening or completed actual-snake theorem is asserted.')
target=H/'data/critical-core-analysis.json';assert not target.exists()
target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='source_files_sha256'}))
