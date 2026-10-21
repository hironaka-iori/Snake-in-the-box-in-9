"""Independent, deliberately RUP-only ASCII LRAT replay. Rejects RAT steps.

This executable check is not a Lean proof. It supports initial clauses, clause
deletions, positive unit-propagation hints, and tautological learned clauses.
"""
import hashlib
from pathlib import Path
if not __debug__:
    raise RuntimeError('Verification must run without Python -O')

def digest(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
    return h.hexdigest()

def check(cnf, proof):
    db={}; pending=[]; nvars=nclauses=None
    with open(cnf,encoding='ascii') as f:
        for line in f:
            if not line.strip() or line.startswith('c'): continue
            if line.startswith('p'):
                _,fmt,nv,nc=line.split(); assert fmt=='cnf'
                nvars,nclauses=int(nv),int(nc); continue
            for x in map(int,line.split()):
                if x==0: db[len(db)+1]=pending; pending=[]
                else:
                    assert nvars is not None and abs(x)<=nvars
                    pending.append(x)
    assert not pending and len(db)==nclauses
    last=nclauses; additions=deletions=0; empty=False
    with open(proof,encoding='ascii') as f:
        for line_no,line in enumerate(f,1):
            if not line.strip() or line.startswith('c'):continue
            parts=line.split(); idx=int(parts[0])
            if len(parts)>1 and parts[1]=='d':
                assert parts[-1]=='0'
                for x in map(int,parts[2:-1]): db.pop(x,None); deletions+=1
                continue
            nums=list(map(int,parts[1:])); z=nums.index(0)
            clause,hints=nums[:z],nums[z+1:]
            assert hints and hints[-1]==0 and 0 not in hints[:-1], ('terminator',line_no)
            hints=hints[:-1]
            assert idx>last and idx not in db, ('id',line_no,idx,last)
            assert all(h>0 and h<idx for h in hints), ('unsupported RAT or invalid hint',line_no)
            assignment={}; conflict=False
            for lit in clause:
                assert abs(lit)<=nvars
                var=abs(lit); value=lit<0
                if var in assignment and assignment[var]!=value: conflict=True
                assignment[var]=value
            if not conflict:
                for h in hints:
                    assert h in db, ('missing clause',line_no,h)
                    unset=set(); satisfied=False
                    for lit in db[h]:
                        v=assignment.get(abs(lit))
                        if v is None: unset.add(lit)
                        elif v==(lit>0): satisfied=True; break
                    assert not satisfied, ('satisfied hint',line_no,h)
                    if not unset: conflict=True; break
                    assert len(unset)==1, ('nonunit hint',line_no,h)
                    lit=next(iter(unset)); assignment[abs(lit)]=lit>0
            assert conflict, ('no conflict',line_no)
            db[idx]=clause; last=idx; additions+=1
            if not clause: empty=True
    assert empty, 'No derived empty clause'
    return dict(status='independent_RUP_replay_passed',additions=additions,deletions=deletions,
                cnf_sha256=digest(cnf),proof_sha256=digest(proof),checker_sha256=digest(__file__),
                evidence_level='independent executable replay; NOT Lean')
