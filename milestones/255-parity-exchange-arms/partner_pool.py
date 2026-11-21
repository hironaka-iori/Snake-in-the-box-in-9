"""All 95-edge Q8 partners keeping or exchanging one site of six donor parity classes."""
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
R248 = HERE.parent / "248-rooted-arm-capacity"
sys.path.insert(0, str(HERE.parent / "252-shorter-reference-segments"))
from replay_core import check_path, digest, word
from replay_exchange import CSC


def require(ok, detail):
    if not ok:
        raise ValueError(detail)


def main():
    src = R248 / "attainers.json"
    audit = R248 / "aggregate.json"
    native = HERE / "Pool95.cs"
    evidence = json.loads(audit.read_bytes())["attainers"]
    require(evidence["complete"] and evidence["labelled"] == 25, "Incomplete Round 248 source")
    sides = defaultdict(list)
    for rec in json.loads(src.read_bytes())["records"]:
        require(rec["status"] == "exhausted" and len(rec["paths"]) == 5, "Unexpected donor census")
        for w in rec["paths"]:
            p = w["path"]
            check_path(p)
            require(len(p) == 95 and p[0] == 0 and w["in_bank"], "Invalid 94-edge source")
            side = tuple(sorted(p[::2]))
            sides[side].append(dict(parent_class=rec["class_id"], bank_id=w["seed"], partner=p))
    require(len(sides) == 6 and sum(map(len,sides.values())) == 25, "Expected six distinct fixed sides")

    labelled, path_ids, shapes, families = [], {}, {}, []
    same_side = {}
    with TemporaryDirectory(prefix="q9-pool255-") as tmp:
        exe = Path(tmp) / "Pool95.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(native)],
                       check=True,capture_output=True,timeout=45)
        for side, donors in sorted(sides.items()):
            base = set(side)
            free = sorted(v for v in range(256) if v.bit_count()%2 == 0 and v not in base)
            require(len(side) == 48 and len(free) == 80, "Wrong donor side")
            expected = {(-1,-1), *product(side,free)}
            run = subprocess.run([str(exe)],input=",".join(map(str,side))+"\n",
                                 text=True,capture_output=True,check=True)
            cases, contents = {}, defaultdict(list)
            contracted = defaultdict(set)
            for line in run.stdout.splitlines():
                what, remove, add, *values = line.split()
                r, a = case = int(remove), int(add)
                require(case in expected, "Unexpected native exchange")
                if what == "S":
                    require(case not in cases and len(values)==3, "Duplicate or malformed summary")
                    cases[case] = tuple(map(int,values))
                    continue
                require(what=="P" and len(values)==1, "Unknown native item")
                p = tuple(map(int,values[0].split(",")))
                target = base if r == -1 else base - {r} | {a}
                require(len(p)==96 and set(p[::2])==target, "Constructed path has an incorrect fixed side")
                check_path(p)
                if p not in path_ids:
                    key = sha256(word(p)).hexdigest()
                    shapes.setdefault(key,list(p))
                    path_ids[p] = len(labelled)
                    labelled.append(dict(shape=key,vertices=list(p)))
                contents[case].append(path_ids[p])
                contracted[case].add(p[::2])
            require(cases.keys()==expected and len(cases)==3841, "Missing exchange")
            rows = []
            for (r,a),(orders,count,nodes) in sorted(cases.items()):
                ids = sorted(contents[r,a])
                require(len(set(ids))==len(ids)==count and orders==len(contracted[r,a]), "Incomplete case")
                mask = sum(1<<v for v in base)
                if r!=-1:
                    mask ^= (1<<r) | (1<<a)
                require(same_side.setdefault(mask,tuple(ids))==tuple(ids), "Shared side has inconsistent answers")
                rows.append([r,a,orders,nodes,ids])
            families.append(dict(source_side=side,donors=donors,cases=rows,
                                 successful=sum(bool(r[4]) for r in rows),labelled=sum(len(r[4]) for r in rows)))
            print("Donors",len(donors),"positive sides",families[-1]["successful"],
                  "labelled",families[-1]["labelled"],"shapes to date",len(shapes),flush=True)
    pins = {p.name:digest(p) for p in (src,audit,native,Path(__file__),CSC,Path(sys.modules["replay_core"].__file__))}
    out = dict(pins=pins,case_fields=["removed","added","contracted_orders","dfs_nodes","labelled_path_indices"],
               unique_labelled_side_sets=len(same_side),unique_nonempty_sides=sum(bool(x) for x in same_side.values()),
               per_side_multiplicities=Counter(map(len,same_side.values())),
               shapes=shapes,paths=labelled,families=families)
    (HERE/"partner-pool.json").write_text(json.dumps(out,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print("Unique labelled paths",len(labelled),"shapes",len(shapes),"distinct sides",len(same_side))


if __name__ == "__main__":
    main()
