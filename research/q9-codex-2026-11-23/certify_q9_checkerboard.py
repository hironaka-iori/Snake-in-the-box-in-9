"""Replay the 191-record checkerboard bound with a separate vertex-level CNF."""
from certify_q9_projection_bound import certificate,replay
from pathlib import Path
from collections import Counter
from itertools import combinations
from pysat.formula import IDPool
from pysat.card import CardEnc,EncType
from verify_q9_center_avoidance import verify
import argparse,tempfile,gzip,json

def mask(p,d,c):
    out=0
    for x in p:
        v=(x% (1<<d))+((x>>(d+1))<<d)
        if v.bit_count()%2==c:out|=1<<(v+256*((x>>d)&1))
    return out

def formula(A,c):
    # Over a free column, a chosen copy can have only one or two neighbors.
    free=set();cap=0
    for v in range(256):
        if v.bit_count()%2==c:continue
        possibilities=[set()]
        for state in (1,2,3):
            V={v+256*i for i in range(2) if state>>i&1}
            if all(1<=sum((x^(1<<j)) in A for j in range(8))+(len(V)==2)<=2 for x in V):
                possibilities.append(V);free.update(V)
        cap+=max(map(len,possibilities))
    if len(A)+cap<=192:return None
    variables=IDPool(start_from=2000);clauses=[];ends=[]
    def atmost(lits,k):
        clauses.extend(CardEnc.atmost(lits,k,vpool=variables,encoding=EncType.seqcounter).clauses)
    U=A|free
    for x in range(512):
        if x in A:clauses.append([x+1])
        elif x not in free:clauses.append([-x-1])
    atmost([-x-1 for x in sorted(free)],len(U)-193)
    for x in sorted(U):
        ns=[w+1 for d in range(9) if (w:=x^(1<<d)) in U]
        e=x+513;ends.append(e)
        clauses.append([-x-1,*ns])
        for bad in combinations(ns,3):clauses.append([-x-1,*(-v for v in bad)])
        for j in range(len(ns)):clauses.append([-x-1,e,*ns[:j],*ns[j+1:]])
    atmost(ends,2)
    return clauses

def main():
    ap=argparse.ArgumentParser();ap.add_argument('binary');ap.add_argument('bundle');ap.add_argument('--replay',action='store_true');args=ap.parse_args()
    bank=[list(map(int,l.split())) for l in gzip.open('q9_port_followup_public191.txt.gz','rt')]
    assert len(bank)==131
    for p in bank:verify(p);assert len(p)==192
    cases=sorted({(c,mask(p,d,c)) for p in bank for d in range(9) for c in (0,1)})
    full=set(range(256));cnt=Counter()
    with tempfile.TemporaryDirectory() as td,gzip.open(args.bundle,'rt' if args.replay else 'wt') as f:
        for c,k in cases:
            A={v for v in range(512) if k>>v&1};cnf=formula(A,c)
            if cnf is None:cnt['size']+=1;continue
            if args.replay:
                col,h,cuts,proof=json.loads(next(f));assert (col,int(h,16))==(c,k)
            else:cuts,proof=certificate(full,cnf)
            replay(full,cnf,cuts,proof,args.binary,td)
            if not args.replay:print(json.dumps([c,format(k,'x'),cuts,proof],separators=(',',':')),file=f)
            cnt['drat']+=1;cnt['cycle_cuts']+=len(cuts)
        if args.replay:assert not f.read().strip()
    print(json.dumps(dict(cases=len(cases),**cnt)))
if __name__=='__main__':main()
