"""Construct a Q9 snake of 192 edges with a parent parity class enlarged by one."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import csv
import json
import subprocess
import sys
import zipfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(HERE.parent/"243-coil-opening"))
from arc_sat import Formula
from open_coil import ADJ,bits,verify,vertices


def components(graph):
    left=set(graph)
    result=[]
    while left:
        part=[left.pop()]
        for v in part:
            extra=graph[v]&left
            left.difference_update(extra)
            part.extend(extra)
        result.append(part)
    return result


def decide(mask, opp, minority, executable, file):
    labels={}
    ports={}
    covered=0
    for z in opp:
        near=ADJ[z]&mask
        size=near.bit_count()
        if size==2:
            labels[near]=z
            covered|=near
        elif size==1 and minority:
            ports[near.bit_length()-1]=z
    if covered!=mask:
        return "isolated",None
    endpoints=set(ports) if minority else set(vertices(mask))
    if len(endpoints)<2:
        return "too_few_ends",None
    adj={v:set() for v in vertices(mask)}
    for pair in labels:
        u,v=vertices(pair)
        adj[u].add(v)
        adj[v].add(u)
    leaves={v for v,ns in adj.items() if len(ns)==1}
    if len(leaves)>2 or not leaves<=endpoints:
        return "leaf_obstruction",None
    if len(components(adj))!=1:
        return "disconnected",None
    # End edges in a Hamiltonian cycle through the dummy encode the two global ends.
    if len(leaves)==2:
        endpoints=leaves
    adj[512]=set(endpoints)
    for v in endpoints:
        adj[v].add(512)
    fixed={v:set() for v in adj}
    free={v:set(ns) for v,ns in adj.items()}
    queue=set(adj)
    for v in leaves:
        free[512].remove(v)
        free[v].remove(512)
        fixed[512].add(v)
        fixed[v].add(512)
    while queue:
        v=queue.pop()
        need=2-len(fixed[v])
        if need<0 or need>len(free[v]):
            return "forced_degree",None
        if need and need!=len(free[v]):
            continue
        for w in tuple(free[v]):
            free[v].remove(w)
            free[w].remove(v)
            if need:
                fixed[v].add(w)
                fixed[w].add(v)
            queue.add(w)
    if len(components({v:free[v]|fixed[v] for v in adj}))!=1:
        return "separated_after_forcing",None
    cnf=Formula()
    edges={(v,w):cnf.variable() for v in sorted(adj) for w in sorted(free[v]) if v<w}
    for v in adj:
        incident=[edges[tuple(sorted((v,w)))] for w in sorted(free[v])]
        cnf.exactly(incident,2-len(fixed[v]))
    while True:
        cnf.save(file)
        try:
            p=subprocess.run([str(executable),"-q",str(file)],capture_output=True,timeout=0.75)
        except subprocess.TimeoutExpired:
            return "timeout",None
        if p.returncode==20 and b"s UNSATISFIABLE" in p.stdout:
            return "native_exclusion",None
        if p.returncode!=10 or b"s SATISFIABLE" not in p.stdout:
            raise RuntimeError((p.returncode,p.stderr[:500]))
        positive={int(t) for line in p.stdout.splitlines() if line.startswith(b"v ") for t in line.split()[1:] if int(t)>0}
        graph={v:set(ns) for v,ns in fixed.items()}
        for (v,w),i in edges.items():
            if i in positive:
                graph[v].add(w)
                graph[w].add(v)
        if any(len(ns)!=2 for ns in graph.values()):
            raise ValueError("Invalid degree assignment")
        parts=components(graph)
        if len(parts)==1:
            order=[512,min(graph[512])]
            while len(order)<len(graph):
                v,=graph[order[-1]].difference(order[-2:])
                order.append(v)
            order=order[1:]
            path=[order[0]]
            for u,v in zip(order,order[1:]):
                path.extend([labels[(1<<u)|(1<<v)],v])
            if minority:
                path=[ports[order[0]]]+path+[ports[order[-1]]]
            if len(path)!=193:
                raise ValueError("Wrong target length")
            verify(path,False)
            return "witness",path
        for group in parts:
            group=set(group)
            cnf.clauses.append([i for (u,v),i in edges.items() if (u in group)!=(v in group)])


def main():
    previous=json.loads((HERE.parent/"244-190-path-construction/results.json").read_bytes())
    archive=ROOT/"work/record_snakes.csv.zip"
    with zipfile.ZipFile(archive) as z:
        raw=z.read("snakes_dim9_190.csv")
        if sha256(raw).hexdigest()!=previous["member_sha256"]:
            raise ValueError("Input differs from verified parent collection")
        data=list(csv.DictReader(raw.decode("utf-8").splitlines()))
    sides={False:{},True:{}}
    for seed,r in enumerate(data):
        path=list(map(int,r["vertices"].split()))
        for minority in (False,True):
            base=bits(path[int(minority)::2])
            sides[minority].setdefault(base,[]).append(seed)
    exe=Path("D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe")
    results=[]
    witness=None
    with TemporaryDirectory(prefix="q9-245-") as out:
        for minority,bases in sides.items():
            seen={}
            totals=Counter()
            per_base=[]
            unresolved=[]
            native_inputs=[]
            for base,parents in bases.items():
                parity=(base&-base).bit_length()-1
                parity=parity.bit_count()%2
                opp=[v for v in range(512) if v.bit_count()%2!=parity]
                row=Counter()
                for add in range(512):
                    if add.bit_count()%2!=parity or base&(1<<add):
                        continue
                    candidate=base|(1<<add)
                    if candidate not in seen:
                        status,path=decide(candidate,opp,minority,exe,Path(out)/"circuit.cnf")
                        seen[candidate]=status
                        if status=="timeout":
                            unresolved.append(dict(parent=parents[0],add=add))
                        if status=="native_exclusion":
                            native_inputs.append(dict(parent=parents[0],add=add))
                        if path:
                            witness=dict(parent=parents[0],add=add,minority=minority,path=path)
                    row[seen[candidate]]+=1
                    if witness:
                        break
                totals.update(row)
                per_base.append(dict(parents=parents,outcomes=row))
                if witness:
                    break
            results.append(dict(minority=minority,bases=len(bases),descriptions=sum(totals.values()),
                                distinct_candidates=len(seen),unique_outcomes=Counter(seen.values()),
                                description_outcomes=totals,unresolved=unresolved,native_inputs=native_inputs,
                                per_base=per_base))
            if witness:
                break
    result=dict(input_sha256=previous["member_sha256"],source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                solver_sha256=sha256(exe.read_bytes()).hexdigest(),families=results,witness=witness)
    (HERE/"results.json").write_text(json.dumps(result,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    for row in results:
        print("minority",row["minority"],"bases",row["bases"],"descriptions",row["descriptions"],
              "distinct",row["distinct_candidates"],dict(row["unique_outcomes"]))


if __name__=="__main__":
    main()
