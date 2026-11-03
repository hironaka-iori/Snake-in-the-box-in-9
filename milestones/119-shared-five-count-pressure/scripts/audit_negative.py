"""Rebuild full-Q9 formulas with the plain encoder and replay saved positive-hint proofs."""
from pathlib import Path
from itertools import combinations
import hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/solver_packages'),str(R/'work/share_packages')]
from wincert import Encoding
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
rows=[]
for name in ['012304-completed-b-total22-full','012304-conditional-a-total22-full']:
    start=time.monotonic();p=H/'data/full-probes'/(name+'.json');d=read(p);m=read(H/'data'/(name+'-certificate.json'));w=H/'work'/name
    assert d['status']=='UNSAT_UNCERTIFIED' and d['radius']==9
    enc=Encoding(m['window'],[tuple(b) for b in d['bounds']],radius=9)
    assert set(enc.ball)==set(range(512))
    lits=[]
    for j in d['positions']:
        i=j+1;c=enc.window[i];used={c^enc.window[i-1],c^enc.window[i+1]}
        lits.extend(-enc.var[c^(1<<a)^(1<<b)] for a,b in combinations(range(9),2) if (1<<a) not in used and (1<<b) not in used)
    lits.sort();assert len(lits)==105
    enc.atmost(lits,d['cap'],'sum')
    assert len(enc.clauses)==d['clauses'] and enc.nv==d['variables']
    for cut in d['cycle_cuts']:enc.add_cycle_cut(cut)
    raw=(f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode()
    assert hashlib.sha256(raw).hexdigest()==sha(w/'full.cnf')==m['cnf_sha256']
    assert sha(w/'full.trim.lrat')==m['lrat_sha256']
    ids=m['core_ids'];db={i:enc.clauses[i-1] for i in ids};last=len(enc.clauses);steps=hints=0
    for line in (w/'full.trim.lrat').open():
        row=list(map(int,line.split()));z=row.index(0,1);cid=row[0];clause=row[1:z];hs=row[z+1:-1]
        assert row[-1]==0 and cid>last and all(0<i<cid and i in db for i in hs)
        assigned={};conflict=False
        for lit in clause:
            if abs(lit) in assigned and assigned[abs(lit)]!=(lit<0):conflict=True
            assigned[abs(lit)]=lit<0
        for i in hs:
            if conflict:break
            premise=db[i]
            if any(abs(lit) in assigned and assigned[abs(lit)]==(lit>0) for lit in premise):continue
            live=set(lit for lit in premise if abs(lit) not in assigned)
            assert len(live)<=1
            if not live:conflict=True
            else:
                lit=next(iter(live));assigned[abs(lit)]=lit>0
        assert conflict
        db[cid]=clause;last=cid;steps+=1;hints+=len(hs)
    assert db[last]==[] and steps==m['lemmas'] and hints==m['hints']
    rows.append(dict(case=name,full_ball_vertices=len(enc.ball),variables=enc.nv,clauses=len(enc.clauses),literal_occurrences=len(lits),distinct_literals=len(set(lits)),used_clauses=len(ids),deductions=steps,hints=hints,seconds=time.monotonic()-start,probe_sha256=sha(p),certificate_sha256=sha(H/'data'/(name+'-certificate.json')),cnf_sha256=sha(w/'full.cnf'),lrat_sha256=sha(w/'full.trim.lrat')))
    print('PASS_PLAIN_ENCODING_AND_RUP',name,steps,hints,flush=True)
out=dict(status='PASS_PLAIN_FULL_Q9_ENCODINGS_AND_NATIVE_RUP',cases=rows,script_sha256=sha(Path(__file__)),plain_encoder_sha256=sha(R/'milestones/10-window-aggregate/scripts/wincert.py'),scope='Independent plain-CNF rebuild and positive-hint unit-propagation replay of exact native contradictions. Concrete Lean count semantics, contradiction replay and actual-snake transfer remain pending.')
p=H/'data/negative-audit.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
