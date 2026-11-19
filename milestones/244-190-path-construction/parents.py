"""Construct 192-edge Q9 snakes using the published 190-edge path collection."""
from collections import Counter
from hashlib import sha256
from io import TextIOWrapper
from pathlib import Path
from tempfile import TemporaryDirectory
import csv
import json
import sys
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0,str(HERE.parent/"243-coil-opening"))
from census191 import signature
from coil_exchanges import search
from open_coil import ADJ, bits, verify, vertices


def extend(path):
    """All one-step extensions, at either endpoint."""
    selected = bits(path)
    for end, is_left in ((path[0],True),(path[-1],False)):
        for v in vertices(ADJ[end]):
            if selected & (1<<v) or ADJ[v]&selected != 1<<end:
                continue
            yield [v]+path if is_left else path+[v]


def main():
    archive = ROOT/"work/record_snakes.csv.zip"
    bank_file = ROOT/"work/bank9.json"
    bank = {signature(r["vertex_sequence"]):i for i,r in enumerate(json.loads(bank_file.read_bytes()))}
    paths = {}
    row_count = 0
    sides = {}
    with zipfile.ZipFile(archive) as z:
        raw = z.read("snakes_dim9_190.csv")
        with z.open("snakes_dim9_190.csv") as stream:
            for parent_id, row in enumerate(csv.DictReader(TextIOWrapper(stream,encoding="utf-8"))):
                path = list(map(int,row["vertices"].split()))
                if len(path)!=191 or row["n"]!="9" or row["length"]!="190":
                    raise ValueError("Input size")
                verify(path,False)
                current=signature(path)
                row_count += 1
                if current in paths:
                    continue
                paths[current] = (parent_id,path)
                p = path[0].bit_count()%2
                side = bits(path[::2])
                if side.bit_count()!=96:
                    raise ValueError("Wrong class")
                sides.setdefault((p,side),[]).append(parent_id)
    reached = {}
    witness = None
    for parent_id,path in paths.values():
        for longer in extend(path):
            k=signature(longer)
            if k not in reached:
                verify(longer,False)
                reached[k] = dict(parent=parent_id,bank_id=bank.get(k),path=longer)
                candidate = next(extend(longer),None)
                if candidate is not None:
                    verify(candidate,False)
                    witness = dict(method="two extensions",parent=parent_id,path=candidate)
                    break
        if witness:
            break
    counts=Counter()
    statuses=[]
    solver=Path("D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe")
    with TemporaryDirectory(prefix="q9-short-parents-") as tmp:
        for (p,side),ids in sides.items():
            if witness:
                break
            status,candidate=search(side,p,solver,Path(tmp)/"parity.cnf")
            counts[status]+=1
            statuses.append(dict(parents=ids,status=status))
            if candidate is not None:
                witness=dict(method="full opposite-side reconstruction",parent=ids[0],path=candidate)
    data=dict(source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),member_sha256=sha256(raw).hexdigest(),
              bank_sha256=sha256(bank_file.read_bytes()).hexdigest(), input_rows=row_count,
              parent_classes=len(paths),retained_classes=len(sides),outcomes=counts,rows=statuses,
              reached191=list(reached.values()),witness=witness,
              source_archive_url="https://github.com/Math-AI-Caltech/Snake-in-the-Box/blob/46c765399353a588ea50444a5d6610f53102b1c2/record_snakes.csv.zip")
    (HERE/"results.json").write_text(json.dumps(data,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print("rows",row_count,"parent classes",len(paths),"fixed classes",len(sides),"outcomes",dict(counts),
          "191 classes",len(reached),"nonbank",sum(r["bank_id"] is None for r in reached.values()),
          "192 witness",bool(witness))


if __name__ == "__main__":
    main()
