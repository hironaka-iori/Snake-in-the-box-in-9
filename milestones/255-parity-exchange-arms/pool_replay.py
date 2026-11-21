"""Independently recover every labelled 95-edge partner by selecting graph edges."""
from collections import defaultdict
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
import subprocess
from tempfile import TemporaryDirectory

from replay_exchange import CSC

HERE = Path(__file__).resolve().parent
ATTAINERS = HERE.parent / "248-rooted-arm-capacity" / "attainers.json"


def require(ok, detail):
    if not ok:
        raise ValueError(detail)


def mask(values):
    return sum(1<<v for v in set(values))


def shape(path):
    flips = [(a^b).bit_length()-1 for a,b in zip(path,path[1:])]
    def normalize(axes):
        seen = {}
        return bytes(seen.setdefault(x,len(seen)) for x in axes)
    return sha256(min(normalize(flips),normalize(reversed(flips)))).hexdigest()


def check(path):
    require(len(path) == len(set(path)) == 96 and all(0<=v<256 for v in path), "Invalid 95-edge path")
    for j,v in enumerate(path):
        require(all(((v^u).bit_count()==1) == (i+1==j) for i,u in enumerate(path[:j])),
                "Pairwise adjacency differs")


def main():
    source = HERE / "partner-pool.json"
    native = HERE / "PoolReplay.cs"
    pool = json.loads(source.read_bytes())
    donors = json.loads(ATTAINERS.read_bytes())["records"]
    seeds = {tuple(sorted(r["path"][::2])) for g in donors for r in g["paths"]}
    require(len(seeds)==6 and all(len(s)==len(set(s))==48 for s in seeds), "Unexpected donor side inventory")
    families = {tuple(f["source_side"]):f for f in pool["families"]}
    require(families.keys()==seeds and len(families)==len(pool["families"]), "Reference sides disagree")
    bank = {}
    for i,r in enumerate(pool["paths"]):
        p = tuple(r["vertices"])
        check(p)
        require(p not in bank and shape(p)==r["shape"], "Repeated labelled path or changed shape")
        bank[p] = i
    require({r["shape"] for r in pool["paths"]} == pool["shapes"].keys()
            and all(tuple(p) in bank and shape(p)==k for k,p in pool["shapes"].items()), "Shape inventory differs")
    expected = {}
    for seed in sorted(seeds):
        free = [v for v in range(256) if (v^seed[0]).bit_count()%2==0 and v not in seed]
        required = {(-1,-1),*product(seed,free)}
        rows = families[seed]["cases"]
        require(len(rows)==3841 and {(r,a) for r,a,*_ in rows}==required, "Missing exchange")
        base = mask(seed)
        for r,a,orders,_,indices in rows:
            side = base if r==-1 else base ^ (1<<r) ^ (1<<a)
            ids = tuple(sorted(indices))
            require(len(set(ids))==len(ids) and all(0<=i<len(bank) for i in ids), "Bad labelled path list")
            require(expected.setdefault(side,(orders,ids))==(orders,ids), "Overlapping seed families disagree")
    require(len(expected)==pool["unique_labelled_side_sets"], "Distinct side count differs")
    sides = sorted(expected)
    side_input = "".join(",".join(str(v) for v in range(256) if (bits>>v)&1)+"\n" for bits in sides)
    with TemporaryDirectory(prefix="snake255-pool-replay-") as tmp:
        exe = Path(tmp)/"PoolReplay.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(native)],
                       check=True,capture_output=True,timeout=45)
        run = subprocess.run([str(exe)],input=side_input,text=True,capture_output=True,check=True)
    found = defaultdict(list)
    checked = set()
    for line in run.stdout.splitlines():
        op,j,*args = line.split()
        j = int(j)
        require(0<=j<len(sides) and j not in checked, "Unexpected side index or late output")
        side = sides[j]
        if op=="P":
            p = tuple(map(int,args[0].split(",")))
            require(p in bank and mask(p[::2])==side, "Additional labelled path or incorrect side")
            found[j].append(bank[p])
        else:
            require(op=="S" and len(args)==2, "Malformed result")
            orders,count = map(int,args)
            require((orders,tuple(sorted(found.get(j,()))))==expected[side]
                    and count==len(found.get(j,())), "Enumeration differs")
            checked.add(j)
    all_ids = {i for ids in found.values() for i in ids}
    require(len(checked)==len(sides) and all_ids==set(bank.values()), "Partial side or path coverage")
    output = dict(pins={f.name:sha256(f.read_bytes()).hexdigest() for f in (source,native,Path(__file__),ATTAINERS,CSC)},
                  source_parity_sets=len(seeds), exchanges_counting_source=len(seeds)*3841,
                  distinct_labelled_sides=len(checked), distinct_nonempty_sides=len(found),
                  labelled_paths=len(bank), shapes=len(pool["shapes"]),
                  native_output_sha256=sha256(run.stdout.encode("ascii")).hexdigest())
    (HERE/"pool-replay.json").write_text(json.dumps(output,indent=2)+"\n",encoding="utf-8",newline="\n")
    print("Recovered",len(bank),"labelled paths and",len(pool["shapes"]),"shapes across",len(checked),"distinct sides")


if __name__=="__main__":
    main()
