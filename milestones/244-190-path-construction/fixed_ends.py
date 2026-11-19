"""Try 192 edges with any published 190-edge parent's two endpoints fixed."""
from collections import Counter
from io import TextIOWrapper
from pathlib import Path
from tempfile import TemporaryDirectory
import csv
import json
import subprocess
import sys
import zipfile

from parents import HERE, ROOT
sys.path.insert(0,str(HERE.parent/"243-coil-opening"))
from arc_sat import Formula
from open_coil import ADJ, bits, verify, vertices


def try_class(mask, ends, executable, file):
    u,v=ends
    adj={x:set() for x in vertices(mask)}
    labels={}
    for z in range(512):
        pair=ADJ[z]&mask
        if pair.bit_count()!=2:
            continue
        a,b=vertices(pair)
        adj[a].add(b)
        adj[b].add(a)
        labels[pair]=z
    target={x:(1 if x in ends else 2) for x in adj}
    if any(len(adj[x])<t for x,t in target.items()):
        return "deficient_degree",None
    # Endpoints are already specified. A degree-one graph endpoint cannot be internal.
    edges={(x,y) for x in adj for y in adj[x] if x<y}
    chosen=set()
    while True:
        removed=set()
        added=set()
        for x,ns in adj.items():
            incident={tuple(sorted((x,y))) for y in ns}
            fixed=chosen&incident
            free=(incident&edges)-fixed
            need=target[x]-len(fixed)
            if need<0 or need>len(free):
                return "forced_degree",None
            if need==0:
                removed.update(free)
            elif need==len(free):
                added.update(free)
        if removed & added:
            return "forced_degree",None
        if not (removed or added):
            break
        chosen.update(added)
        edges-=removed
    cnf=Formula()
    variables={e:cnf.variable() for e in sorted(edges-chosen)}
    for x,degree in target.items():
        cnf.exactly([i for (a,b),i in variables.items() if x in (a,b)],
                    degree-sum(x in e for e in chosen))
    while True:
        cnf.save(file)
        try:
            p=subprocess.run([str(executable),"-q",str(file)],capture_output=True,timeout=0.40)
        except subprocess.TimeoutExpired:
            return "timeout",None
        if p.returncode==20 and b"s UNSATISFIABLE" in p.stdout:
            return "native_exclusion",None
        if p.returncode!=10 or b"s SATISFIABLE" not in p.stdout:
            raise RuntimeError((p.returncode,p.stderr[-800:]))
        assignment={int(i) for line in p.stdout.splitlines() if line.startswith(b"v ") for i in line.split()[1:]}
        selected=chosen | {e for e,i in variables.items() if i in assignment}
        graph={x:set() for x in adj}
        for a,b in selected:
            graph[a].add(b)
            graph[b].add(a)
        if any(len(ns)!=target[x] for x,ns in graph.items()):
            raise ValueError("Target degrees")
        order=[u]
        while order[-1]!=v:
            x,=graph[order[-1]].difference(order[-2:])
            order.append(x)
        if len(order)==97:
            path=[u]
            for a,b in zip(order,order[1:]):
                path.extend([labels[(1<<a)|(1<<b)],b])
            verify(path,False)
            if len(path)!=193 or path[-1]!=v:
                raise ValueError("Endpoint or length")
            return "witness",path
        reached=set(order)
        cnf.clauses.append([i for (a,b),i in variables.items() if (a in reached)!=(b in reached)])


def main():
    states={}
    with zipfile.ZipFile(ROOT/"work/record_snakes.csv.zip") as z:
        for i,r in enumerate(csv.DictReader(TextIOWrapper(z.open("snakes_dim9_190.csv"),encoding="utf-8"))):
            path=list(map(int,r["vertices"].split()))
            key=(bits(path[::2]),tuple(sorted((path[0],path[-1]))))
            states.setdefault(key,[]).append(i)
    results=Counter()
    unresolved=[]
    witness=None
    solver=Path("D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe")
    with TemporaryDirectory(prefix="q9-ends-") as tmp:
        for (base,ends),seeds in states.items():
            for x in range(512):
                if x.bit_count()%2!=ends[0].bit_count()%2 or base & (1<<x):
                    continue
                status,path=try_class(base|(1<<x),ends,solver,Path(tmp)/"ends.cnf")
                results[status]+=1
                if status=="timeout":
                    unresolved.append([seeds,x])
                if path:
                    witness=dict(seeds=seeds,added=x,path=path)
                    break
            if witness:
                break
    from hashlib import sha256
    data=dict(source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),bases_with_endpoints=len(states),
              descriptions=sum(results.values()),outcomes=results,timeouts=unresolved,witness=witness)
    (HERE/"fixed-ends.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8",newline="\n")
    print("states",len(states),"descriptions",sum(results.values()),"statuses",dict(results))


if __name__=="__main__":
    main()
