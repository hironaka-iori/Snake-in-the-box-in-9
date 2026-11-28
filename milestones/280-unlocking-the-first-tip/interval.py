"""Select a connected induced path through a fixed Q9 interval at a specified length."""
from argparse import ArgumentParser
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import monotonic

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(next(HERE.parent.glob('279-*'))))
from prefix import BANK, check
sys.path.insert(0, str(next(HERE.parent.glob('266-*'))))
import rebuild
G = rebuild.geometry
N = [tuple(v ^ (1 << j) for j in range(9)) for v in range(512)]


def free_graph(core):
    occupied = set(core)
    ends = {core[0],core[-1]}
    candidates = {v for v in range(512) if v not in occupied and
                  not (set(N[v]) & occupied) - ends and len(set(N[v]) & ends) <= 1}
    reachable = set(ends)
    queue = list(ends)
    for v in queue:
        for w in N[v]:
            if w in candidates and w not in reachable:
                reachable.add(w)
                queue.append(w)
    return sorted(reachable)


def faces():
    for dim,limit in ((2,3),(3,5)):
        for bits in combinations(range(9),dim):
            offsets = [0]
            for b in bits:
                offsets += [x | (1<<b) for x in offsets]
            for v in range(512):
                if not v & offsets[-1]:
                    yield tuple(v | w for w in offsets),limit


def encode(core, target, majority, cycles, required=(), forbidden=()):
    ends = {core[0],core[-1]}
    frozen = set(core[1:-1])
    cnf = G.Formula()
    chosen = {v:cnf.variable() for v in free_graph(core)}
    parity = lambda v: v.bit_count() % 2
    for v in sorted(ends):
        cnf.clauses.append([chosen[v]])
    for v in required:
        if v not in frozen:
            cnf.clauses.append([chosen[v]] if v in chosen else [])
    for v in forbidden:
        if v in frozen:
            cnf.clauses.append([])
        elif v in chosen:
            cnf.clauses.append([-chosen[v]])
    for q in (0,1):
        n = (target+1)//2 + int(target%2 == 0 and majority == q)
        cnf.exactly([x for v,x in chosen.items() if parity(v)==q], n-sum(parity(v)==q for v in frozen))
    tip = {v:cnf.variable() for v in chosen if target%2 or majority==parity(v)}
    for q in (0,1):
        cnf.exactly([t for v,t in tip.items() if parity(v)==q],1 if target%2 else 2*int(q==majority))
    for v,x in chosen.items():
        near = [chosen[w] for w in N[v] if w in chosen]
        prev = int(v in ends)
        if v in tip:
            t = tip[v]
            cnf.clauses.append([-t,x])
            G.bounds(cnf,near,1-prev,2-prev,[-x])
            G.bounds(cnf,near,0,1-prev,[-t])
            G.bounds(cnf,near,2-prev,len(near),[-x,t])
        else:
            G.bounds(cnf,near,2-prev,2-prev,[-x])
    for face,cap in faces():
        remaining = cap-sum(v in frozen for v in face)
        xs = [chosen[v] for v in face if v in chosen]
        assert remaining>=0
        for selection in combinations(xs,remaining+1):
            cnf.clauses.append([-x for x in selection])
    for cycle in cycles:
        ring = set(cycle)
        assert len(ring) == len(cycle) and all(len(ring.intersection(N[v]))==2 for v in ring)
        assert ring <= (frozen | chosen.keys())
        cnf.clauses.append([-chosen[v] for v in sorted(ring) if v not in frozen])
    return cnf,chosen


def walk(sites):
    adj = {v:sorted(set(N[v]) & sites) for v in sites}
    tips = sorted(v for v,nb in adj.items() if len(nb)==1)
    assert len(tips)==2 and all(len(nb) in (1,2) for nb in adj.values())
    path = [tips[0]]
    seen = set(path)
    for v in path:
        for w in adj[v]:
            if w not in seen:
                seen.add(w)
                path.append(w)
    cycles = []
    while sites-seen:
        cycle = [min(sites-seen)]
        seen.add(cycle[0])
        for v in cycle:
            for w in adj[v]:
                if w not in seen:
                    seen.add(w)
                    cycle.append(w)
        cycles.append(sorted(cycle))
    return path,cycles


def solve(core, target, maj, folder, scratch, verifier, seconds, required=(), forbidden=()):
    check(core)
    stop = monotonic()+seconds
    cycles = []
    while True:
        cnf,x = encode(core,target,maj,cycles,required,forbidden)
        formula = scratch/'case.cnf'
        proof = scratch/'case.lrat'
        proof.unlink(missing_ok=True)
        h = cnf.save(formula)
        row = dict(target=target,majority=maj,required=list(required),forbidden=list(forbidden),cycles=cycles,
                   variables=cnf.count,clauses=len(cnf.clauses),sites=len(x),cnf_sha256=h)
        try:
            result = subprocess.run([str(G.SOLVER),'-q','--lrat','--no-binary',str(formula),str(proof)],
                                    capture_output=True,timeout=max(.01,stop-monotonic()))
        except subprocess.TimeoutExpired:
            return dict(**row,status='open')
        if result.returncode == 20:
            assert b's UNSATISFIABLE' in result.stdout
            archive = folder/'proofs'/(h+'.lrat.gz')
            archive.parent.mkdir(exist_ok=True)
            raw = rebuild.masks.p.joins.archive(proof,archive)
            receipt = rebuild.masks.p.check_proof(formula,archive,verifier)
            return dict(**row,status='excluded',raw_sha256=raw,proof=archive.name,replay=receipt)
        assert result.returncode==10 and b's SATISFIABLE' in result.stdout,(result.returncode,result.stderr[-400:])
        values = {int(a) for line in result.stdout.splitlines() if line.startswith(b'v ') for a in line.split()[1:]}
        selected = set(core[1:-1]) | {v for v,k in x.items() if k in values}
        assert len(selected)==target+1
        path,extra = walk(selected)
        if extra:
            cycles.extend(extra)
            continue
        check(path)
        assert any(path[i:i+len(core)] in (core,core[::-1]) for i in range(len(path)-len(core)+1))
        return dict(**row,status='witness',path=path)


def main():
    ap=ArgumentParser()
    ap.add_argument('lengths',type=int,nargs='+')
    ap.add_argument('--seconds',type=int,default=18)
    args=ap.parse_args()
    donor=json.loads(BANK.read_bytes())[0]['vertex_sequence']
    check(donor)
    output=HERE/'decisions.json'
    ledger=json.loads(output.read_bytes()) if output.exists() else {}
    with TemporaryDirectory() as tmp:
        scratch=Path(tmp)
        verifier,_=rebuild.masks.compilers(scratch)
        for n in args.lengths:
            core=donor[:n+1]
            row=ledger.setdefault(str(n),dict(core=core,cases={}))
            for maj in (0,1):
                k=str(maj)
                if row['cases'].get(k,{}).get('status') in ('excluded','witness'):
                    continue
                result=solve(core,192,maj,HERE,scratch,verifier,args.seconds)
                row['cases'][k]=result
                output.write_text(json.dumps(ledger,separators=(',',':'))+'\n')
                print(n,maj,result['status'],result['sites'],len(result['cycles']),flush=True)
                if result['status']=='witness':
                    return


if __name__=='__main__':
    main()
