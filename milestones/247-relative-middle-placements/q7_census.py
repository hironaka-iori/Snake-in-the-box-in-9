"""Guard the independent DFS and check each reported path directly."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "242-seed-trade-construction"))
from guarded import memory_limit, wait_for_gate


def digest(path):
    h=sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def verify(path, allowed):
    if len(path) not in (48,49) or not set(path)<=allowed or len(set(path))!=len(path):
        raise ValueError("Vertex range, length or distinctness")
    for i,v in enumerate(path):
        for j in range(i+1,len(path)):
            if ((v^path[j]).bit_count()==1)!=(j==i+1):
                raise ValueError("Adjacency or chord")
    return sum(1<<v for v in path)


def even_start(path):
    if len(path)==49:
        # Delete the smaller endpoint, which was the newly appended tip.
        path=path[1:] if path[0]<path[-1] else path[:-1]
    return path[0] if path[0].bit_count()%2==0 else path[-1]


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--start",type=int,default=0,help="First sorted even root index")
    parser.add_argument("--stop",type=int,default=40,help="Exclusive even root index")
    parser.add_argument("--nodes",type=int,default=200000000)
    parser.add_argument("--seconds",type=int,default=200)
    args=parser.parse_args()
    if not 0<=args.start<args.stop<=40 or not 1<=args.nodes<2**63 or args.seconds<=0:
        parser.error("Invalid root shard or budget")
    bound=memory_limit(256)
    suffix="" if (args.start,args.stop)==(0,40) else "-%d-%d"%(args.start,args.stop)
    stem="q7-census"+suffix
    orbit=HERE/"orbit.json"
    sat=HERE/"complementary.json"
    source=HERE/"Q7Census.cs"
    compiler=Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")
    first=json.loads(orbit.read_bytes())["first"]
    allowed=set(range(128))-set(first)
    roots=sorted(v for v in allowed if v.bit_count()%2==0)
    sat_data=json.loads(sat.read_bytes())
    if len(allowed)!=80 or len(roots)!=40 or list(sat_data["first"])!=first:
        raise ValueError("Complement differs from the saved certificate")
    target=HERE/(stem+"-paths.txt")
    with TemporaryDirectory(prefix="q7-census-") as directory:
        folder=Path(directory)
        exe=folder/"Q7Census.exe"
        inp=folder/"first.txt"
        inp.write_text(" ".join(map(str,first)),encoding="ascii")
        comp=wait_for_gate([str(compiler),"/nologo","/optimize+","/platform:x64","/out:"+str(exe),str(source)],
                           folder,HERE/(stem+"-compile.log"),60)
        exe_hash=digest(exe)
        # Write the native stream next to its final destination to allow an
        # atomic replacement after verification, even across distinct volumes.
        raw=target.with_suffix(".tmp")
        stats=folder/"counts.txt"
        run=wait_for_gate([str(exe),str(inp),str(raw),str(stats),str(args.start),str(args.stop),
                           str(args.nodes),str(args.seconds)],folder,HERE/(stem+"-native.log"),args.seconds+60)
        lines=[s.split() for s in stats.read_text("ascii").splitlines()]
    root_rows=[dict(root=int(x[1]),status=x[2],nodes=int(x[3])) for x in lines if x[0]=="root"]
    tail=lines[-1]
    if tail[0]!="total" or [r["root"] for r in root_rows]!=roots[args.start:args.start+len(root_rows)]:
        raise ValueError("Root coverage mismatch")
    status=tail[1]
    if status=="complete" and len(root_rows)!=args.stop-args.start:
        raise ValueError("Incomplete shard")
    seen={47:set(),48:set()}
    endpoints={47:Counter(),48:Counter()}
    starts={r["root"] for r in root_rows}
    with raw.open("r",encoding="ascii") as stream:
        for line in stream:
            path=list(map(int,line.split()))
            n=len(path)-1
            key=verify(path,allowed)
            if even_start(path) not in starts:
                raise ValueError("Path arose outside the assigned shard")
            if n==47 and path[0].bit_count()%2 or n==48 and path[0]>=path[-1]:
                raise ValueError("Noncanonical orientation")
            if key in seen[n]:
                raise ValueError("Duplicated path set")
            seen[n].add(key)
            endpoints[n][(path[0]^path[-1]).bit_count()]+=1
    if (len(seen[47]),len(seen[48]))!=tuple(map(int,tail[3:5])):
        raise ValueError("Native and independent output counts differ")
    completed={r["root"] for r in root_rows if r["status"]=="complete"}
    prior={47:set(),48:set()}
    expected={47:set(),48:set()}
    for row in sat_data["records"]:
        n=row["length"]
        if n not in prior:
            continue
        for p in row["paths"]+row.get("additional_verified_subpaths",[]):
            key=verify(p,allowed)
            prior[n].add(key)
            if even_start(p) in completed:
                expected[n].add(key)
    if any(expected[n]-seen[n] for n in expected):
        raise ValueError("A completed root omitted a previously verified path")
    if all(r["status"]=="native_exhaustion" for r in sat_data["records"] if r["length"]==48) and seen[48]-prior[48]:
        raise ValueError("New length-48 path violates the earlier exhaustion")
    raw.replace(target)
    record=dict(status=status,all_roots_complete=len(completed)==40,first=first,start=args.start,stop=args.stop,
                node_limit=args.nodes,seconds_limit=args.seconds,visited_nodes=int(tail[2]),roots=root_rows,
                lengths={n:len(seen[n]) for n in seen},endpoint_distance_histogram=endpoints,
                earlier_controls={n:dict(known=len(prior[n]),required_for_completed_roots=len(expected[n]),
                                         independently_recovered=len(seen[n]&prior[n])) for n in prior},
                cuts=dict(parity=int(tail[5]),reachable_parity=int(tail[6]),disjoint_stars=int(tail[7])),
                paths=target.name,paths_sha256=digest(target),private_limit=bound,
                pins={p.name:digest(p) for p in (Path(__file__),source,compiler,orbit,sat)},
                executable_sha256=exe_hash,compile=comp,search=run)
    (HERE/(stem+".json")).write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(status,len(completed),"completed roots;",record["lengths"],record["visited_nodes"],"nodes")


if __name__=="__main__":
    main()
