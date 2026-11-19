"""Relate a 190-edge parent to a 192-edge target at the parity/count boundary."""
from collections import Counter
from hashlib import sha256
from io import TextIOWrapper
from pathlib import Path
import csv
import json
import sys
import zipfile

from parents import HERE, ROOT
sys.path.insert(0,str(HERE.parent/"242-seed-trade-construction"))
from seed_orbit import bits, partitions, placements, WITNESS


def main():
    full = json.loads((HERE/"results.json").read_bytes())
    if sum(full["outcomes"].values()) != full["retained_classes"] or set(full["outcomes"]) - {
            "isolated","forced_end","degree_conflict","too_few_ports","separated","native_exclusion"}:
        raise ValueError("Fixed-side exclusion is incomplete")
    sides=[set(),set()]
    with zipfile.ZipFile(ROOT/"work/record_snakes.csv.zip") as z:
        with z.open("snakes_dim9_190.csv") as stream:
            for row in csv.DictReader(TextIOWrapper(stream,encoding="utf-8")):
                path=list(map(int,row["vertices"].split()))
                sides[path[0].bit_count()%2].add(bits(path[::2]))
    if sum(map(len,sides)) != full["retained_classes"]:
        raise ValueError("Input parity classes")
    witness=json.loads(WITNESS.read_bytes())
    hist=[0]*41
    for blocks in partitions():
        for t, minus, plus in placements(blocks,witness):
            for seed in sides[1^(t.bit_count()%2)]:
                k=20-(seed & minus).bit_count()+(seed & plus).bit_count()
                hist[k]+=1
                hist[40-k]+=1
    total=sum(hist)
    if total!=120960*sum(map(len,sides)):
        raise ValueError("Orbit coverage")
    record=dict(source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),comparisons=total,
                classes_per_parity=list(map(len,sides)),histogram=hist, minimum=next(i for i,h in enumerate(hist) if h),
                fixed_class_results_sha256=sha256((HERE/"results.json").read_bytes()).hexdigest())
    (HERE/"balanced-orbit.json").write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8",newline="\n")
    print("closest",record["minimum"],"comparisons",total)


if __name__=="__main__":
    main()
