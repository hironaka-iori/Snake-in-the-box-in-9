"""Independently replay every finite 25/24 placement catalogue case."""
import argparse
import gzip
import json
from collections import Counter
from pathlib import Path

from q6_star_interfaces import check, formula
from q9_dense_pair_full_lift import audit_pair
from q9_three_tight_star_refine import anchor_list
from verify_q9_free_dimension_cuts import deg, parts


def run(source,destination,checker,cases,anchor_edges=25):
    seen = set()
    positive = []
    with gzip.open(source,'rt') as file:
        for line in file:
            row = json.loads(line)
            mask = int(row['anchor'],16)
            e,c,r = leaf = tuple(row['leaf'])
            center = row.get('center_components',3)
            assert row.get('center_edges',25)==anchor_edges
            key = center,mask,leaf
            assert key not in seen and row['status']=='CATALOGUE_COVERAGE_VERIFIED'
            seen.add(key)
            f = formula(mask,(leaf,))
            fixed = {u for u in range(64) if mask>>u&1}
            assert len(set(row['models']))==len(row['models'])
            for word in row['models']:
                b = int(word,16)
                audit_pair(mask,b,anchor_edges,center,e,c,r)
                f.append([-u-1 for u in range(64) if b>>u&1])
                positive.append(dict(edges=[anchor_edges,e],components=[center,c],crossings=r,masks=[row['anchor'],word]))
            for cycle in row['cycles']:
                s = set(cycle)
                assert len(s)==len(cycle) and all(0<=u<128 for u in s)
                assert len(parts(s,7))==1 and all(deg(s,u,7)==2 for u in s)
                assert {u for u in s if u<64} <= fixed
                cut = [-u+63 for u in cycle if u>=64]
                assert cut
                f.append(cut)
            check(f,row['proof'],checker)
    assert seen=={(center,mask,(e,c,r)) for center,e,c,r in cases for mask in anchor_list(center,anchor_edges)}
    destination.write_text(''.join(json.dumps(row)+'\n' for row in positive))
    counts = Counter((row['edges'][1],row['components'][1],row['crossings']) for row in positive)
    print(json.dumps(dict(status='VERIFIED',catalogue_proofs=len(seen),covered_cases=cases,anchor_edges=anchor_edges,
                          layouts=[[k,v] for k,v in sorted(counts.items())])),flush=True)


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('archive',type=Path)
    p.add_argument('export',type=Path)
    p.add_argument('checker')
    p.add_argument('--case',type=int,nargs=4,action='append',metavar=('CENTER_COMPONENTS','EDGES','COMPONENTS','CROSSES'))
    p.add_argument('--anchor-edges',type=int,choices=(24,25,26),default=25)
    a = p.parse_args()
    if a.anchor_edges==24:
        assert a.case and all(case[0]==4 for case in a.case)
    run(a.archive,a.export,a.checker,a.case or [(3,24,4,2),(3,24,3,2)],a.anchor_edges)

