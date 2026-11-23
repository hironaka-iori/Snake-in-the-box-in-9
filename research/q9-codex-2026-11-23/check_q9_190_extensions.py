"""Check extension relations for the published 190- and 191-edge Q9 banks."""
import argparse
from collections import Counter
import csv
import json
from pathlib import Path
from search_q9_wynn_plateau import canonical, verify


def extend(path):
    used = set(path)
    for oriented in (path, path[::-1]):
        end = oriented[-1]
        for axis in range(9):
            v = end ^ (1 << axis)
            if v not in used and all((v ^ w).bit_count() != 1 for w in oriented[:-1]):
                yield oriented + [v]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bank191",type=Path)
    parser.add_argument("csv190",type=Path)
    args=parser.parse_args()
    known=set()
    for row in json.loads(args.bank191.read_text()):
        p=row["vertex_sequence"]
        assert len(p)==192 and verify(p)
        assert not list(extend(p))
        known.add(canonical(p))
    seen=set()
    histogram=Counter()
    children=set()
    with args.csv190.open() as source:
        for row in csv.DictReader(source):
            p=list(map(int,row["vertices"].split()))
            assert len(p)==191 and verify(p)
            assert list(map(int,row["actions"].split()))==[(u^v).bit_length()-1 for u,v in zip(p,p[1:])]
            key=canonical(p)
            assert key not in seen
            seen.add(key)
            out=list(extend(p))
            histogram[len(out)]+=1
            for q in out:
                assert verify(q)
                children.add(canonical(q))
    print(json.dumps({"parents":len(seen),"extension_histogram":histogram,
                      "distinct_children":len(children),"outside_bank":len(children-known),
                      "unrecovered_bank_classes":len(known-children)},sort_keys=True))


if __name__=="__main__":
    main()
