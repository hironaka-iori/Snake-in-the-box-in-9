"""Apply empty interface catalogues that have passed independent DRAT replay."""

import argparse
from collections import Counter
import json
from pathlib import Path

from q9_dense_pair_full_lift import table
from q9_three_tight_pairs import BONDS
from q9_three_tight_star_refine import anchor_list


def empty_interfaces(stem):
    report = json.loads(stem.with_suffix(".replay.log").read_text().splitlines()[-1])
    assert report["status"] == "VERIFIED"
    edges = report["anchor_edges"]
    cases = [tuple(row) for row in report["covered_cases"]]
    assert len(cases) == len(set(cases))
    assert report["catalogue_proofs"] == sum(len(anchor_list(c,edges)) for c,_,_,_ in cases)
    exported = table(stem.with_suffix(".verified.jsonl"))
    covered = {(edges,*case) for case in cases}
    assert set(exported) <= covered
    export_hist = Counter()
    for key,placements in exported.items():
        export_hist[key[2:]] += len(placements)
    assert dict(export_hist) == {tuple(key):n for key,n in report["layouts"]}
    impossible = set()
    for key in covered-set(exported):
        e,c,f,d,r = key
        impossible.update((key,(f,d,e,c,r)))
    return impossible


def run(args):
    blocked = set().union(*(empty_interfaces(stem) for stem in args.catalogue))
    profiles = json.loads(args.profiles.read_text())["representatives"]
    before = json.loads(args.screen.read_text())
    assert before["status"] == "VERIFIED"
    assert before["initial"] == before["excluded_by_local"]+len(before["indices"])
    retained,excluded = [],[]
    for i in before["indices"]:
        e,c,r = profiles[i]
        found = any((e[a],c[a],e[b],c[b],n) in blocked for (a,b),n in zip(BONDS,r))
        (excluded if found else retained).append(i)
    result = dict(before, indices=retained, excluded_by_local=before["excluded_by_local"]+len(excluded),
                  new_exclusions=excluded, empty_catalogues=[str(stem) for stem in args.catalogue],
                  prior_screen=str(args.screen))
    assert result["initial"] == result["excluded_by_local"]+len(retained)
    with args.output.open("x") as out:
        out.write(json.dumps(result)+"\n")
    print(json.dumps(dict(counts=before["counts"],newly_excluded=len(excluded),
                          empty_orientations=len(blocked),remaining=len(retained))),flush=True)


if __name__=="__main__":
    parser = argparse.ArgumentParser()
    for name in ("profiles","screen","output"):
        parser.add_argument(name,type=Path)
    parser.add_argument("--catalogue",required=True,type=Path,action="append")
    run(parser.parse_args())
