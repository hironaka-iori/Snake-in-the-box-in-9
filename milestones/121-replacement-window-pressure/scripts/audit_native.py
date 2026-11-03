"""Rebuild plain encodings and independently replay the four saved proofs."""
from pathlib import Path
import hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/share_packages')]
from wincert import Encoding
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
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
rows=[]
for name in ['lower032','pairmin032','pair25032','pair34032']:
    m=read(H/f'data/meta/{name}.json');plan=read(H/f'data/{name}-plan.json')
    assert plan['cycle_cuts']==[]
    enc=Encoding(m['window'],[tuple(b) for b in m['bounds']],radius=3)
    raw=(f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode()
    assert hashlib.sha256(raw).hexdigest()==plan['cnf_sha256']==sha(H/f'work/{name}/{name}.cnf')
    a=replay(H/f'work/{name}/{name}.lrat',m['core_ids'],lambda i:i)
    assert (a['deductions'],a['hints'],a['sha256'])==(plan['lemmas'],plan['hints'],plan['lrat_sha256'])
    rows.append(dict(name=name,variables=enc.nv,clauses=len(enc.clauses),core_clauses=len(m['core_ids']),radius=3,cycle_cuts=0,replay=a,plan_sha256=sha(H/f'data/{name}-plan.json'),metadata_sha256=sha(H/f'data/meta/{name}.json'),selected_for_lean=name!='lower032'))
    print(name,a['deductions'],a['hints'],flush=True)
p=H/'data/native-audit.json';assert not p.exists()
p.write_text(json.dumps(dict(status='PASS_PLAIN_ENCODINGS_AND_FOUR_NATIVE_REPLAYS',proofs=rows,plain_encoder_sha256=sha(R/'milestones/10-window-aggregate/scripts/wincert.py'),script_sha256=sha(Path(__file__)),scope='Exact encoding reconstruction and independent RUP replay. Three pair certificates selected; earlier four-outer proof retained but uncompiled. Lean receipts remain separate.'),indent=2)+'\n',encoding='utf-8')
