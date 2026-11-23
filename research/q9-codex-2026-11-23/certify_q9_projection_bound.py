"""Generate and replay ordinary DRAT certificates for fixed unordered Q8 projections."""
import argparse
import gzip
import json
import subprocess
import tempfile
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Glucose4
from verify_q9_center_avoidance import verify

def enc(S,minimum=192):
    pool=IDPool(start_from=2000)
    clauses=[]
    selectable=sorted([x+256*b for x in S for b in (0,1)])
    adjacency={x:[y for d in range(9) if (y:=x^(1<<d))%256 in S] for x in selectable}
    def atmost(xs,k):
        clauses.extend(CardEnc.atmost(xs,k,vpool=pool,encoding=EncType.seqcounter).clauses)
    twos=[]
    for v in sorted(S):
        a,b=v+1,v+257
        clauses.append([a,b])
        if len(adjacency[v])>3:
            clauses.append([-a,-b]);continue
        t=v+513
        clauses.extend([[-t,a],[-t,b],[-a,-b,t]])
        twos.append(t)
    loss=len(S)+len(twos)-1-minimum
    if loss<0:return None
    atmost([-v for v in twos],loss)
    # Every nontrivial induced path has maximum degree two and exactly two
    # vertices of degree one. Relax connectivity so UNSAT remains sufficient.
    endpoints=[]
    for x in selectable:
        neighbors=[y+1 for y in adjacency[x]]
        a=x+1;e=x+769;endpoints.append(e)
        clauses.append([-a,*neighbors]);clauses.append([-e,a])
        for i in range(len(neighbors)):
            clauses.append([-a,e,*neighbors[:i],*neighbors[i+1:]])
        for y,z in combinations(neighbors,2):clauses.append([-e,-y,-z])
        for y,z,w in combinations(neighbors,3):clauses.append([-a,-y,-z,-w])
    atmost(endpoints,2)
    return clauses

def projected_set(p,d):
    return frozenset((v & ((1<<d)-1)) + ((v>>(d+1))<<d) for v in p)

def certificate(S,clauses):
    cuts=[]
    while True:
        with Glucose4(bootstrap_with=clauses+cuts,with_proof=True) as solver:
            if not solver.solve():
                return cuts,solver.get_proof()
            m=set(solver.get_model())
        chosen={x for v in S for x in (v,v+256) if x+1 in m}
        rest=set(chosen);found=False
        while rest:
            todo=[rest.pop()]
            for x in todo:
                ns={x^(1<<d) for d in range(9)} & rest;todo.extend(ns);rest-=ns
            if all(sum((x^(1<<d)) in chosen for d in range(9))==2 for x in todo):
                cuts.append(sorted(-x-1 for x in todo));found=True
        if not found:raise RuntimeError('Relaxation unexpectedly reached a path forest; inspect model')

def replay(S,clauses,cuts,proof,binary,folder):
    for c in cuts:
        cyc={-lit-1 for lit in c}
        assert all(lit<0 and (-lit-1)%256 in S for lit in c) and len(cyc)>=4
        assert all(sum((v^(1<<d)) in cyc for d in range(9))==2 for v in cyc)
    cnf=Path(folder)/'instance.cnf';drat=Path(folder)/'proof.drat'
    CNF(from_clauses=clauses+cuts).to_file(str(cnf))
    drat.write_text('\n'.join(proof)+'\n')
    r=subprocess.run([binary,str(cnf),str(drat)],capture_output=True)
    assert b's VERIFIED' in r.stdout,(r.returncode,r.stdout[-1000:])

def run():
    arg=argparse.ArgumentParser();arg.add_argument('binary');arg.add_argument('bundle');arg.add_argument('--replay',action='store_true');a=arg.parse_args()
    paths=[list(map(int,row.split())) for row in gzip.open('q9_port_followup_public191.txt.gz','rt')]
    assert len(paths)==131
    for p in paths:verify(p);assert len(p)==192
    cases=sorted({tuple(sorted(projected_set(p,d))) for p in paths for d in range(9)})
    assert len(cases)==1043
    count=0;size=0
    with tempfile.TemporaryDirectory() as folder,gzip.open(a.bundle,'rt' if a.replay else 'wt') as stream:
        for idx,case in enumerate(cases):
            S=set(case);cnf=enc(S)
            if cnf is None:size+=1;continue
            if a.replay:
                i,cuts,proof=json.loads(next(stream));assert i==idx
            else:cuts,proof=certificate(S,cnf)
            replay(S,cnf,cuts,proof,a.binary,folder);count+=1
            if not a.replay:print(json.dumps([idx,cuts,proof],separators=(',',':')),file=stream)
        if a.replay:assert not stream.read().strip()
    print(json.dumps(dict(projected_sets=len(cases),size_bound=size,drat_verified=count)))
if __name__=='__main__':run()
