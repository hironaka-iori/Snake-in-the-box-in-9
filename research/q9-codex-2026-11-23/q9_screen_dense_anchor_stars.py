"""Use the exact dense/dense port catalogue in local stars of the 9,9,10 branch."""
import argparse
from collections import defaultdict
import gzip
import json
from pathlib import Path

from pysat.solvers import Cadical195

from q6_star_interfaces import check, formula
from q9_three_tight_star_refine import anchor_list, excludes, proposals


def read_ports(path):
    ports = defaultdict(list)
    for line in path.read_text().splitlines():
        row = json.loads(line)
        a,q = (int(row[name],16) for name in ('anchor','ports'))
        r = row['crossings']
        assert q&a==q and q.bit_count()==r
        ports[a,row['other_components'],r].append(q)
    return ports


def constrained(mask,leaves,ports):
    exact_ports = [(i,ports[mask,c,r]) for i,(e,c,r) in enumerate(leaves)
                   if e==25 and c is not None]
    if any(not bank for _,bank in exact_ports):
        return None
    f = formula(mask,leaves)
    for i,bank in exact_ports:
        first = f.nv+1
        selectors = list(range(first,first+len(bank)))
        for key,matched in zip(selectors,bank):
            f.extend([[-key,64*i+v+1] for v in range(64) if matched>>v&1])
        f.append(selectors)
    return f


def trial(key,ports,checker,budget):
    e,c,leaves = key
    assert e==25
    cases = []
    for mask in anchor_list(c):
        f = constrained(mask,leaves,ports)
        case = dict(anchor=f'{mask:016x}')
        if f is None:
            cases.append(dict(status='OUTSIDE_EXACT_PORT_TABLE',**case))
            continue
        with Cadical195(bootstrap_with=f,with_proof=True) as solver:
            solver.conf_budget(budget)
            answer = solver.solve_limited()
            if answer:
                return dict(key=key,status='FEASIBLE_RELAXATION',**case)
            if answer is None:
                cases.append(dict(status='UNKNOWN',**case))
            else:
                proof = '\n'.join(solver.get_proof())+'\n'
                check(f,proof,checker)
                cases.append(dict(status='UNSAT_DRAT_VERIFIED',proof=proof,**case))
    status = 'UNKNOWN' if any(r['status']=='UNKNOWN' for r in cases) else 'ALL_ANCHORS_EXCLUDED'
    return dict(key=key,status=status,cases=cases)


def run(args):
    bank = json.loads(args.input.read_text())['representatives']
    screen = json.loads(args.screen.read_text())
    assert screen['counts']==[9,9,10]
    remaining = {i:bank[i] for i in screen['colour_survivors']}
    ports = read_ports(args.ports)
    keys = [key for key in proposals(remaining)
            if any(e==25 and c is not None for e,c,_ in key[2])]
    attempted = set()
    with gzip.open(args.output,'wt') as archive:
        for _ in range(args.limit):
            candidates = [(key,[i for i,row in remaining.items() if excludes(row,key)])
                          for key in keys if key not in attempted]
            if not candidates:
                break
            key,hits = max(candidates,key=lambda x:(len(x[1]),len(x[0][2])))
            if not hits:
                break
            attempted.add(key)
            print(json.dumps(dict(status='STARTED',key=key,may_exclude=len(hits))),flush=True)
            record = trial(key,ports,args.checker,args.budget)
            archive.write(json.dumps(record)+'\n')
            archive.flush()
            if record['status']=='ALL_ANCHORS_EXCLUDED':
                for i in hits:
                    del remaining[i]
            print(json.dumps(dict(key=key,status=record['status'],remaining=len(remaining))),flush=True)
    print(json.dumps(dict(status='DONE',remaining=sorted(remaining))),flush=True)


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('input',type=Path)
    p.add_argument('screen',type=Path)
    p.add_argument('ports',type=Path)
    p.add_argument('output',type=Path)
    p.add_argument('checker')
    p.add_argument('--limit',type=int,default=16)
    p.add_argument('--budget',type=int,default=20000)
    run(p.parse_args())

