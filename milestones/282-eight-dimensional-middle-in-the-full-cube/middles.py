"""Allow every Q9 extension of each of the 22 archived Q8 intervals."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(next(HERE.parent.glob('280-*'))))
from interval import N, check, rebuild, solve
from compact import compact
from prefix import BASE
from spectrum import shape


def read(p):
    return json.loads(p.read_bytes())


def save(p,data):
    tmp=p.with_suffix('.pending')
    tmp.write_bytes((json.dumps(data,separators=(',',':'))+'\n').encode())
    tmp.replace(p)


def uncontacted(path):
    closed=set(path)
    for v in path:
        closed.update(N[v][:8])
    return sorted(set(range(256))-closed)


def middle_runs(m):
    # Stop either free end at any stage; these are the possible entire runs in
    # this face, including a run that the full Q8 graph would permit extending.
    def steps(p,v):
        return [w for w in N[v][:8] if w not in p and len(set(N[w][:8]).intersection(p))==1]
    runs=[]
    def right(p):
        runs.append(p)
        for w in steps(p,p[-1]):
            right(p+[w])
    def left(p):
        right(p)
        for w in steps(p,p[0]):
            left([w]+p)
    left(m)
    assert len({tuple(p) for p in runs})==len(runs)
    return runs


def inventory():
    witnesses=read(BASE/'whole-middle-witnesses.json')['rows']
    out={}
    for k,r in witnesses.items():
        m=r['m']
        check(m)
        U=uncontacted(m)
        assert all((u^v).bit_count()>1 for u,v in combinations(U,2))
        models=[]
        for p in middle_runs(m):
            check(p)
            u=uncontacted(p)
            assert set(u)<=set(U)
            for count in range(min(2,len(u))+1):
                for tails in combinations(u,count):
                    models.append(dict(run=p,terminal_returns=list(tails)))
        # A direct lower bound is present in the archived representative coordinates.
        donor=r['best_archived']
        orig=donor['archive_vertices']
        check(orig)
        options=[i for i in range(len(orig)-len(m)+1) if shape(orig[i:i+len(m)])==shape(m)]
        assert options and len(orig)-1==r['best_archived_edges']
        out[k]=dict(middle=m,undominated=U,maximum_crossings=2+min(2,len(U)),
                    runs=len(middle_runs(m)),patterns=models,archived_lower=len(orig)-1,
                    archived_source=donor['source'],archived_interval_start=options[0],
                    archived_191_count=len(r['distinct_archived_191_sources']))
    save(HERE/'geometry.json',out)
    return out


def main():
    ap=ArgumentParser()
    ap.add_argument('--first',type=int,default=22)
    ap.add_argument('--seconds',type=int,default=4)
    ap.add_argument('--target',type=int,default=192)
    args=ap.parse_args()
    data=inventory()
    print('Undominated site counts',Counter(len(r['undominated']) for r in data.values()),flush=True)
    file=HERE/('full-'+str(args.target)+'.json')
    ledger=read(file) if file.exists() else {}
    with TemporaryDirectory() as tmp:
        scratch=Path(tmp)
        tools=rebuild.masks.compilers(scratch)
        for k,r in sorted(data.items(),key=lambda e:(-e[1]['archived_191_count'],len(e[1]['patterns']),e[0]))[:args.first]:
            if args.target==191 and r['archived_lower']==191:
                continue
            m=r['middle']
            row=ledger.setdefault(k,{})
            for maj in ((0,1) if args.target%2==0 else (0,)):
                if row.get(str(maj),{}).get('status') in ('excluded','witness'):
                    continue
                case=solve(m,args.target,maj,HERE,scratch,tools[0],args.seconds)
                compact(m,case,HERE,scratch,*tools)
                row[str(maj)]=case
                save(file,ledger)
                print(len(m)-1,r['archived_source'],args.target,maj,case['status'],flush=True)
                if case['status']=='witness' and args.target>=192:
                    return


if __name__=='__main__':
    main()
