"""Apply additional independently replayed local obstructions to a Q9 screen."""

import argparse
from collections import defaultdict
from functools import lru_cache
import json
from pathlib import Path

from q9_geometry_cut_library import orientations
from q9_three_tight_pairs import BONDS


def canonical_patterns(path):
    patterns = json.loads(path.read_text())["patterns"]
    return {min(orientations(record["faces"], record["links"])) for record in patterns}


def compile_patterns(patterns):
    bond_index = {bond: index for index,bond in enumerate(BONDS)}
    checks = defaultdict(set)
    for shape in patterns:
        for faces, links in orientations(*shape):
            layers = tuple(a for a,_,_ in faces)
            bonds = tuple(bond_index[a,b] for a,b,_ in links)
            checks[layers,bonds].add((tuple((e,c) for _,e,c in faces),tuple(r for _,_,r in links)))
    return checks


def screen(profiles, indices, checks):
    by_contact = []
    for (layers, bonds), forbidden in checks.items():
        bank = defaultdict(set)
        for face_values, seam_values in forbidden:
            bank[seam_values].add(face_values)
        by_contact.append((layers, bonds, bank))

    @lru_cache(maxsize=50000)
    def active_shapes(crossings):
        # Several distinct layer populations can share an entire seam vector.
        active = []
        for layers, bonds, bank in by_contact:
            matches = bank.get(tuple(crossings[b] for b in bonds))
            if matches:
                active.append((layers, matches))
        return active

    retained, excluded = [], []
    for i in indices:
        e, c, crossings = profiles[i]
        active = active_shapes(tuple(crossings))
        faces = tuple(zip(e, c))
        conflict = any(tuple(faces[a] for a in layers) in forbidden
                       for layers, forbidden in active)
        (excluded if conflict else retained).append(i)
    return retained, excluded


def run(args):
    previous = canonical_patterns(args.previous_library)
    available = canonical_patterns(args.library)
    assert previous <= available
    checks = compile_patterns(available-previous)
    for prefix in args.prefix:
        def read(suffix):
            return json.loads(prefix.with_name(f"{prefix.name}_{suffix}.json").read_text())
        source = read(args.source)
        profiles = read("profiles")["representatives"]
        assert source["status"] == "VERIFIED"
        assert source["initial"] == source["excluded_by_local"] + len(source["indices"])
        retained,excluded = screen(profiles,source["indices"],checks)
        report = dict(source,indices=retained,excluded_by_local=source["excluded_by_local"]+len(excluded),
                      new_exclusions=excluded,certificate_library=str(args.library),
                      prior_screen=args.source)
        assert report["initial"] == report["excluded_by_local"] + len(retained)
        out = prefix.with_name(f"{prefix.name}_{args.destination}.json")
        with out.open("x") as fp:
            fp.write(json.dumps(report)+"\n")
        print(json.dumps(dict(counts=source["counts"],new=len(excluded),remaining=len(retained))),flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("previous_library",type=Path)
    parser.add_argument("library",type=Path)
    parser.add_argument("source")
    parser.add_argument("destination")
    parser.add_argument("prefix",nargs="+",type=Path)
    run(parser.parse_args())
