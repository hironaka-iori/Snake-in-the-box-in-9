"""Replay dense-port SAT certificates against the exhaustive anchor table."""
import argparse
import gzip
import json
from pathlib import Path

from q6_star_interfaces import check
from q9_screen_dense_anchor_stars import constrained, read_ports
from q9_three_tight_star_refine import anchor_list, excludes


def verify(args):
    rows = json.loads(args.input.read_text())['representatives']
    indices = json.loads(args.screen.read_text())['colour_survivors']
    active = {i:rows[i] for i in indices}
    ports = read_ports(args.ports)
    proofs = 0
    with gzip.open(args.archive,'rt') as source:
        for line in source:
            row = json.loads(line)
            if row['status']!='ALL_ANCHORS_EXCLUDED':
                continue
            key = row['key']
            e,c,leaves = key
            anchors = anchor_list(c)
            assert e==25 and anchors
            assert [int(case['anchor'],16) for case in row['cases']]==anchors
            for mask,case in zip(anchors,row['cases']):
                f = constrained(mask,leaves,ports)
                if case['status']=='OUTSIDE_EXACT_PORT_TABLE':
                    assert f is None
                else:
                    assert f is not None and case['status']=='UNSAT_DRAT_VERIFIED'
                    check(f,case['proof'],args.checker)
                    proofs += 1
            hits = [i for i,x in active.items() if excludes(x,key)]
            assert hits
            for i in hits:
                del active[i]
            print(json.dumps(dict(status='REPLAYED_STAR',key=key,excluded=hits)),flush=True)
    print(json.dumps(dict(status='VERIFIED',initial=len(indices),remaining=len(active),drat=proofs,
                          indices=sorted(active))),flush=True)


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('input',type=Path)
    p.add_argument('screen',type=Path)
    p.add_argument('ports',type=Path)
    p.add_argument('archive',type=Path)
    p.add_argument('checker')
    verify(p.parse_args())

