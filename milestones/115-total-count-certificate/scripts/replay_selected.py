"""Replay a selected reduced proof against original full-formula clause identifiers."""
from pathlib import Path
import argparse,datetime,hashlib,json,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
OLD=ROOT/'milestones/114-total-count-pressure'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
p=argparse.ArgumentParser();p.add_argument('choice');args=p.parse_args()
record=HERE/'data'/('replay-'+args.choice+'.json');assert not record.exists()
source=HERE/'data'/('refine-'+args.choice+'.json');r=read(source)
assert r['status']=='UNSAT_TRIMMED_NOT_REPLAYED'
fullpath=OLD/'work/012310-total18/full.cnf';assert sha(fullpath)==r['full_cnf_sha256']
full=[[int(x) for x in l.split()[:-1]] for l in fullpath.read_text().splitlines() if l and not l.startswith(('c','p'))]
corepath=HERE/r['cnf'];trim=HERE/r['trim']
assert sha(corepath)==r['cnf_sha256'] and sha(trim)==r['trim_sha256']
core=[[int(x) for x in l.split()[:-1]] for l in corepath.read_text().splitlines() if l and not l.startswith(('c','p'))]
ids=r['input_ids'];assert core==[full[i-1] for i in ids] and len(ids)==len(set(ids))
def mapped(i):return ids[i-1] if 1<=i<=len(ids) else len(full)+i-len(ids)
db={i:full[i-1] for i in ids};last=len(full);steps=hints=0;start=time.monotonic()
for line in trim.open(encoding='ascii'):
    row=list(map(int,line.split()));z=row.index(0,1)
    assert row[-1]==0 and row[0]>len(ids)
    cid=mapped(row[0]);clause=row[1:z];hs=row[z+1:-1]
    assert cid>last and all(0<abs(x)<=r['variables'] for x in clause)
    assert all(0<h<row[0] for h in hs)
    truth={-x for x in clause};conflict=any(-x in truth for x in truth)
    for h in hs:
        premise=db[mapped(h)]
        if conflict or any(x in truth for x in premise):continue
        unknown={x for x in premise if -x not in truth}
        assert len(unknown)<=1,('Nonunit hint',cid,h)
        if unknown:truth.add(next(iter(unknown)))
        else:conflict=True
    assert conflict,('No contradiction',cid)
    db[cid]=clause;last=cid;steps+=1;hints+=len(hs)
assert db[last]==[] and steps==r['lemmas'] and hints==r['hints']
out=dict(status='NATIVE_REFINED_CONTRADICTION_REPLAYED_LEAN_PENDING',choice=args.choice,
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-start,
    steps=steps,hints=hints,input_clauses=len(ids),used_input_clauses=r['used_core'],final_mapped_id=last,
    refinement_sha256=sha(source),full_cnf_sha256=sha(fullpath),core_cnf_sha256=sha(corepath),trim_sha256=sha(trim),
    checker_sha256=sha(Path(__file__)),scope='All retained RUP deductions checked against mapped original input IDs; concrete Lean semantics and Lean proof replay remain separate.')
record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(out['status'],steps,hints,round(out['seconds'],3),flush=True)
