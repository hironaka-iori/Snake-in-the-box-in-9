"""Independent plain-formula reconstruction and native proof replay."""
from pathlib import Path
import hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/share_packages')]
from wincert import Encoding
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=read(H/'data/meta/outer3333.json');plan=read(H/'data/outer3333-plan.json')
enc=Encoding(m['window'],[tuple(b) for b in m['bounds']],radius=3)
raw=(f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode()
assert hashlib.sha256(raw).hexdigest()==plan['cnf_sha256']==sha(H/'work/outer3333/outer3333.cnf')

def replay(path,ids,mapper):
    db={i:enc.clauses[i-1] for i in ids};last=len(enc.clauses);steps=hints=0;start=time.monotonic()
    for line in path.open():
        row=list(map(int,line.split()));z=row.index(0,1);cid=mapper(row[0]);clause=row[1:z];hs=[mapper(i) for i in row[z+1:-1]]
        assert row[-1]==0 and cid>last and all(0<i<cid and i in db for i in hs)
        assigned={};conflict=False
        for lit in clause:
            if abs(lit) in assigned and assigned[abs(lit)]!=(lit<0):conflict=True
            assigned[abs(lit)]=lit<0
        for i in hs:
            if conflict:break
            premise=db[i]
            if any(abs(lit) in assigned and assigned[abs(lit)]==(lit>0) for lit in premise):continue
            live=set(lit for lit in premise if abs(lit) not in assigned);assert len(live)<=1
            if not live:conflict=True
            else:
                lit=next(iter(live));assigned[abs(lit)]=lit>0
        assert conflict;db[cid]=clause;last=cid;steps+=1;hints+=len(hs)
    assert db[last]==[]
    return dict(deductions=steps,hints=hints,seconds=time.monotonic()-start,sha256=sha(path))
original=replay(H/'work/outer3333/outer3333.lrat',m['core_ids'],lambda i:i)
assert original['deductions']==plan['lemmas'] and original['hints']==plan['hints'] and original['sha256']==plan['lrat_sha256']
f=read(H/'data/refine-core0.json');ids=f['input_ids'];n=len(enc.clauses);k=len(ids)
refined=replay(H/f['trim'],f['used_original_ids'],lambda i:ids[i-1] if i<=k else n+i-k)
assert (refined['deductions'],refined['hints'])==(f['lemmas'],f['hints'])
out=dict(status='PASS_PLAIN_ENCODING_AND_BOTH_NATIVE_REPLAYS',variables=enc.nv,clauses=len(enc.clauses),input_core_clauses=len(m['core_ids']),radius=3,cycle_cuts=0,original=original,refinement=refined,selected_for_lean='original',reason='Original has fewer deductions and hints.',cnf_sha256=plan['cnf_sha256'],metadata_sha256=sha(H/'data/meta/outer3333.json'),plan_sha256=sha(H/'data/outer3333-plan.json'),refinement_metadata_sha256=sha(H/'data/refine-core0.json'),plain_encoder_sha256=sha(R/'milestones/10-window-aggregate/scripts/wincert.py'),script_sha256=sha(Path(__file__)))
p=H/'data/native-audit.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'],original['deductions'],original['hints'],'original;',refined['deductions'],refined['hints'],'refined')
