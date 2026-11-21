"""Strengthen the rooted 95-edge formula with exact occupancy restrictions from Q4 faces."""
from argparse import ArgumentParser
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import sys

import partners255 as driver

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent / "248-rooted-arm-capacity"))
import conditioned


@lru_cache(maxsize=1)
def capacities():
    # The maximum size of a linear forest in the available Q4 subset.
    # A non-forest must omit at least one of its vertices.
    forests, _ = conditioned.forest_degrees()
    sizes = bytearray(1 << 16)
    for mask in range(1,1 << 16):
        if forests[mask] >= 0:
            sizes[mask] = mask.bit_count()
        else:
            other = mask
            while other:
                bit = other & -other
                sizes[mask] = max(sizes[mask],sizes[mask ^ bit])
                other ^= bit
    return sizes


@lru_cache(maxsize=1)
def partitions():
    result = []
    for axes in combinations(range(8),4):
        offsets = [0]
        for a in axes:
            offsets += [v | (1 << a) for v in offsets]
        faces = [[base | offset for offset in offsets]
                 for base in range(256) if base & offsets[-1] == 0]
        result.append((axes,faces))
    return result


def tighten(cnf,chosen,parent,prefix,number,shortlist):
    fixed = set(prefix)
    domain = conditioned.domain_after_prefix(parent,prefix)
    if not fixed <= domain:
        cnf.clauses.append([])
        return
    for v in sorted(set(chosen)-domain):
        cnf.clauses.append([-chosen[v]])
    conditioned.articulation_cuts(cnf,chosen,domain)
    size = capacities()
    candidates = []
    for axes,faces in partitions():
        total = sum(size[sum(1 << i for i,v in enumerate(face) if v in domain)] for face in faces)
        candidates.append((total,axes,faces))
    if min(r[0] for r in candidates) < 96:
        cnf.clauses.append([])
        return
    weighted = []
    for _,axes,faces in sorted(candidates)[:shortlist]:
        groups = [(face,conditioned.face_table(face,domain,fixed)) for face in faces]
        if not conditioned.attainable(conditioned.reachable(groups),48,48):
            cnf.clauses.append([])
            return
        rating = (sum(max(e+o for e,o in pairs) for _,pairs in groups),
                  sum(len(pairs) for _,pairs in groups),axes)
        weighted.append((rating,groups))
    for _,groups in sorted(weighted)[:number]:
        conditioned.add_partition(cnf,chosen,groups,domain)


def main():
    cli = ArgumentParser(add_help=False)
    cli.add_argument("--partitions",type=int,default=2)
    cli.add_argument("--shortlist",type=int,default=5)
    args,remaining = cli.parse_known_args()
    if not 1 <= args.partitions <= args.shortlist <= 70:
        raise ValueError("Invalid Q4 partition selection")
    folder = HERE / ("face-caps-"+str(args.partitions)+"-of-"+str(args.shortlist))
    folder.mkdir(exist_ok=True)
    driver.HERE = folder
    driver.LEDGER = folder / "cases.json"
    base_sources = driver.sources
    base_anchored = driver.shared.anchored_model
    def sources():
        old,pins = base_sources()
        files = [Path(__file__),Path(conditioned.__file__),Path(conditioned.lifts.__file__),
                 Path(conditioned.partner.__file__)]
        pins.update({p.relative_to(HERE.parent).as_posix():driver.file_hash(p) for p in files})
        pins["partitions"] = args.partitions
        pins["shortlist"] = args.shortlist
        return old,pins
    def anchored(prefix):
        inherited = base_anchored(prefix)
        def model(parent,length,rules):
            if length != 95:
                raise ValueError("The face parity quotas apply only to 95-edge partners")
            cnf,chosen = inherited(parent,length,rules)
            tighten(cnf,chosen,parent,prefix,args.partitions,args.shortlist)
            return cnf,chosen
        return model
    driver.sources = sources
    driver.shared.anchored_model = anchored
    sys.argv[1:] = remaining
    driver.main()


if __name__ == "__main__":
    main()
