"""Separate the possible runs and terminal returns, then solve for the opposite face."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import monotonic
from middles import BASE, HERE, check, read, rebuild, save, shape
from interval import N, walk
sys.path.insert(0,str(BASE))
from local_faces import add as face_four
G=rebuild.geometry


def cases(record,old,maj):
    for i,pat in enumerate(record['patterns']):
        run=pat['run']
        returns=pat['terminal_returns']
        ends=(run[0],run[-1])
        for mask in (1,2,3):
            departures=[v for j,v in enumerate(ends) if mask & (1<<j)]
            tips=sorted(set(ends)-set(departures) | set(returns))
            rule=None
            if len(returns)>len(departures):
                rule='more returns than departing tails'
            elif any((v.bit_count()&1)!=maj for v in tips):
                rule='wrong parity at forced endpoint'
            elif len(departures)==2 and not returns and shape(run) in old:
                rule='Round 278 two-crossing middle'
            yield str(i)+'-'+str(mask)+'-'+str(maj),run,returns,departures,tips,rule


def lower_formula(run,returns,departures,tips,maj,cycles):
    upper=set(run)|set(returns)
    vertical=set(returns)|set(departures)
    f=G.Formula()
    chosen={v:f.variable() for v in range(256) if v not in upper or v in vertical}
    for v in sorted(vertical):
        f.clauses.append([chosen[v]])
    parity=lambda v:v.bit_count()&1
    for q in (0,1):
        lower_count=96+int(q==maj)-sum(parity(v)==q for v in upper)
        f.exactly([x for v,x in chosen.items() if parity(v)!=q],lower_count)
    endpoint={v:f.variable() for v in chosen if parity(v)!=maj}
    f.exactly(list(endpoint.values()),2-len(tips))
    for v,x in chosen.items():
        prior=int(v in vertical)
        ns=[chosen[w] for w in N[v][:8] if w in chosen]
        if v in endpoint:
            t=endpoint[v]
            f.clauses.append([-t,x])
            G.bounds(f,ns,1-prior,2-prior,[-x])
            G.bounds(f,ns,0,1-prior,[-t])
            G.bounds(f,ns,2-prior,len(ns),[-x,t])
        else:
            G.bounds(f,ns,2-prior,2-prior,[-x])
    G.face_bounds(f,chosen)
    face_four(f,chosen,upper)
    for cycle in cycles:
        ring=set(cycle)
        assert len(ring)==len(cycle) and all(len(set(N[v])&ring)==2 for v in ring)
        assert all(v in upper if v<256 else v-256 in chosen for v in ring)
        f.clauses.append([-chosen[v-256] for v in sorted(ring) if v>=256])
    return f,chosen


def decide(run,returns,departures,tips,maj,scratch,tools,seconds,pins=(),initial_cycles=()):
    cycles=list(initial_cycles)
    stop=monotonic()+seconds
    while True:
        f,x=lower_formula(run,returns,departures,tips,maj,cycles)
        for v,selected in pins:
            f.clauses.append([x[v] if selected else -x[v]])
        cnf=scratch/'face.cnf'
        trace=scratch/'face.lrat'
        trace.unlink(missing_ok=True)
        h=f.save(cnf)
        r=dict(cnf_sha256=h,clauses=len(f.clauses),cycles=cycles)
        try:
            proc=subprocess.run([str(G.SOLVER),'-q','--seed=1','--lrat','--no-binary',str(cnf),str(trace)],
                                capture_output=True,timeout=max(.02,stop-monotonic()))
        except subprocess.TimeoutExpired:
            return dict(**r,status='open')
        if proc.returncode==20:
            assert b's UNSATISFIABLE' in proc.stdout
            proof=HERE/'return-proofs'/(h+'.lrat.gz')
            proof.parent.mkdir(exist_ok=True)
            spool=scratch/'hints.bin'
            raw=scratch/'trim.lrat'
            untrimmed=scratch/'untrimmed.lrat.gz'
            rebuild.masks.p.joins.archive(trace,untrimmed)
            subprocess.run([str(tools[1]),str(len(f.clauses)),str(untrimmed),str(spool),str(raw)],
                           check=True,capture_output=True,timeout=100)
            spool.unlink()
            digest=rebuild.masks.p.joins.archive(raw,proof)
            receipt=rebuild.masks.p.check_proof(cnf,proof,tools[0])
            return dict(**r,status='excluded',proof=proof.name,raw_sha256=digest,replay=receipt)
        assert proc.returncode==10 and b's SATISFIABLE' in proc.stdout
        values={int(t) for l in proc.stdout.splitlines() if l.startswith(b'v ') for t in l.split()[1:]}
        sites=set(run)|set(returns)|{v+256 for v,j in x.items() if j in values}
        assert len(sites)==193
        path,extra=walk(sites)
        if extra:
            cycles.extend(extra)
            continue
        check(path)
        assert len(path)==193 and any(path[i:i+len(run)] in (run,run[::-1]) for i in range(len(path)-len(run)+1))
        return dict(**r,status='witness',path=path)


def old_shapes(geo):
    previous=read(BASE/'all-middle-port-coverage.json')
    rows=previous['rows']
    return {shape(v['middle']):k for k,v in geo.items() if rows[k]['excluded_192']}


def main():
    ap=ArgumentParser()
    ap.add_argument('--seconds',type=int,default=5)
    ap.add_argument('--limit',type=int,default=300)
    ap.add_argument('--first',type=int,default=22)
    a=ap.parse_args()
    geo=read(HERE/'geometry.json')
    direct=read(HERE/'full-192.json')
    old=old_shapes(geo)
    assert len(old)==22
    out=HERE/'returns.json'
    ledger=read(out) if out.exists() else {}
    used=0
    with TemporaryDirectory() as tmp:
        scratch=Path(tmp)
        tools=rebuild.masks.compilers(scratch)
        for k,r in sorted(geo.items(),key=lambda e:(-e[1]['archived_191_count'],len(e[1]['patterns']),e[0]))[:a.first]:
            row=ledger.setdefault(k,{})
            for maj in (0,1):
                if direct[k][str(maj)]['status']=='excluded':
                    continue
                for tag,run,t,dep,tips,rule in cases(r,old,maj):
                    if rule or row.get(tag,{}).get('status') in ('excluded','witness'):
                        continue
                    case=decide(run,t,dep,tips,maj,scratch,tools,a.seconds)
                    row[tag]=case
                    save(out,ledger)
                    used+=1
                    print(r['archived_source'],tag,case['status'],flush=True)
                    if case['status']=='witness' or used>=a.limit:
                        return
    print('Completed run and return branches',used,flush=True)


if __name__=='__main__':
    main()
