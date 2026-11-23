"""Independently rebuild and replay certificates for anchored 221-edge cases."""
import argparse
import gzip
import json
from collections import defaultdict
from pathlib import Path

from q6_star_interfaces import check
from q9_lift_three_tight_pairs import surviving_profiles
from q9_three_tight_anchored_lift import form
from q9_three_tight_star_refine import anchor_list
from verify_q9_free_dimension_cuts import deg, parts


def verify(path, checker):
    rows = list(surviving_profiles())
    reconstructed = {}
    cases = defaultdict(dict)
    with gzip.open(path,'rt') as archive:
        for line in archive:
            rec = json.loads(line)
            i,center = int(rec['index']),rec['center']
            mask = int(rec['anchor'],16)
            e,c,_ = rows[i]
            assert e[center]==25 and mask in set(anchor_list(c[center]))
            family = cases[i,center]
            assert mask not in family
            family[mask] = rec['status']
            if rec['status']!='UNSAT_DRAT_VERIFIED':
                continue
            if i not in reconstructed:
                reconstructed[i] = form(rows[i])
            f = reconstructed[i]
            pins = [[64*center+v+1 if mask>>v&1 else -64*center-v-1] for v in range(64)]
            clauses = list(pins)
            for cycle in rec['cycles']:
                selected = set(cycle)
                assert len(selected)==len(cycle) and all(0<=u<512 for u in selected)
                assert len(parts(selected,9))==1 and all(deg(selected,u,9)==2 for u in selected)
                clauses.append([-u-1 for u in cycle])
            f.extend(clauses)
            try:
                check(f,rec['proof'],checker)
            finally:
                del f.clauses[-len(clauses):]
    for (i,center),family in sorted(cases.items()):
        anchors = set(anchor_list(rows[i][1][center]))
        certified = {m for m,status in family.items() if status=='UNSAT_DRAT_VERIFIED'}
        print(json.dumps(dict(index=i,center=center,proved=len(certified),total=len(anchors),
                              complete=certified==anchors)),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('archive',type=Path)
    p.add_argument('checker')
    args=p.parse_args()
    verify(args.archive,args.checker)

