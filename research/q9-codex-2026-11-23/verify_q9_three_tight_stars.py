"""Verify the local certificate chain closing the three-nine-direction branch."""
import argparse
import gzip
import json
from pathlib import Path

from q6_star_interfaces import check, formula
from q9_lift_three_tight_pairs import surviving_profiles
from q9_three_tight_star_refine import anchor_list, excludes, replay_existing


def verify(archive, residual, checker):
    rows = dict(enumerate(surviving_profiles()))
    before = len(rows)
    cuts = list(replay_existing(rows,checker))
    after_old = len(rows)
    replayed = 0
    with gzip.open(archive,'rt') as file:
        for line in file:
            record = json.loads(line)
            if record['status']!='UNSAT_all_anchors_verified':
                continue
            key = record['key']
            e,c,leaves = key
            anchors = anchor_list(c)
            assert e==25 and anchors
            cases = record['cases']
            assert [int(case['anchor'],16) for case in cases]==anchors
            for mask,case in zip(anchors,cases):
                assert case['status']=='UNSAT_DRAT_verified'
                check(formula(mask,leaves),case['proof'],checker)
                replayed += 1
            hits = [i for i,row in rows.items() if excludes(row,key)]
            assert hits
            for i in hits:
                del rows[i]
            cuts.append(key)
            print(json.dumps(dict(status='NEW_DRAT_REPLAYED',excluded=hits,
                                  anchors=len(anchors),key=key)),flush=True)
    expected = json.loads(residual.read_text())
    assert expected==dict(cuts=cuts,profiles={str(i):x for i,x in rows.items()})
    assert before==29 and not rows
    print(json.dumps(dict(status='TRIPLE_NINE_BRANCH_VERIFIED',initial=before,
                          after_old=after_old,new_drat=replayed,remaining=len(rows))),flush=True)


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('archive',type=Path)
    p.add_argument('residual',type=Path)
    p.add_argument('checker')
    args=p.parse_args()
    verify(args.archive,args.residual,args.checker)

