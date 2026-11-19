"""Allow scattered parity changes along a Q9 record coil and arbitrary opposite labels."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import subprocess

from arc_sat import Formula
from open_coil import ADJ, HERE, bits, verify, vertices


def search(mask, parity, solver, file):
    links, ports, covered = {}, {}, 0
    for v in range(512):
        if v.bit_count() % 2 == parity:
            continue
        ns = ADJ[v] & mask
        size = ns.bit_count()
        if size == 1:
            ports[ns.bit_length()-1] = v
        elif size == 2:
            covered |= ns
            links[ns] = v
    if covered != mask:
        return "isolated", None
    if len(ports) < 2:
        return "too_few_ports", None
    graph = {v: set() for v in vertices(mask)}
    for pair in links:
        u, v = vertices(pair)
        graph[u].add(v)
        graph[v].add(u)
    leaves = [v for v, ns in graph.items() if len(ns) == 1]
    if len(leaves)>2 or any(v not in ports for v in leaves):
        return "forced_end", None
    for u in ports:
        graph[u].add(512)
    graph[512] = set(ports)
    # Hamiltonian cycles of the augmented graph correspond to the required paths.
    # Propagate exactly two chosen edges per vertex before invoking the solver.
    undecided = {v: set(ns) for v, ns in graph.items()}
    forced = {v: set() for v in graph}
    todo = set(graph)
    while todo:
        v = todo.pop()
        n = 2 - len(forced[v])
        if n < 0 or n > len(undecided[v]):
            return "degree_conflict", None
        if n and n != len(undecided[v]):
            continue
        for u in tuple(undecided[v]):
            undecided[v].remove(u)
            undecided[u].remove(v)
            if n:
                forced[v].add(u)
                forced[u].add(v)
            todo.add(u)
    def components(adj):
        pending = set(adj)
        groups = []
        while pending:
            part = [pending.pop()]
            for v in part:
                following = adj[v] & pending
                part.extend(following)
                pending -= following
            groups.append(part)
        return groups
    if len(components({v: undecided[v]|forced[v] for v in graph})) > 1:
        return "separated", None
    cnf = Formula()
    edge = {(u,v):cnf.variable() for u in sorted(graph) for v in sorted(undecided[u]) if u<v}
    for u in graph:
        incident = [edge[tuple(sorted((u,v)))] for v in undecided[u]]
        cnf.exactly(incident, 2-len(forced[u]))
    while True:
        cnf.save(file)
        try:
            run = subprocess.run([str(solver), "-q", str(file)], capture_output=True,timeout=0.30)
        except subprocess.TimeoutExpired:
            return "timeout",None
        if run.returncode == 20 and b"s UNSATISFIABLE" in run.stdout:
            return "native_exclusion",None
        if run.returncode != 10 or b"s SATISFIABLE" not in run.stdout:
            raise RuntimeError((run.returncode,run.stderr))
        model = {int(x) for l in run.stdout.splitlines() if l.startswith(b"v ") for x in l.split()[1:]}
        adj = {u:set(f) for u,f in forced.items()}
        for (u,v),i in edge.items():
            if i in model:
                adj[u].add(v)
                adj[v].add(u)
        if not all(len(f)==2 for f in adj.values()):
            raise ValueError("Graph degree")
        parts = components(adj)
        if len(parts)==1:
            order = [512,min(adj[512])]
            while len(order)<97:
                w, = adj[order[-1]] - {order[-2]}
                order.append(w)
            order = order[1:]
            path = [ports[order[0]],order[0]]
            for u,v in zip(order,order[1:]):
                path.extend([links[(1<<u)|(1<<v)],v])
            path.append(ports[order[-1]])
            verify(path,False)
            if len(path)!=193:
                raise ValueError("Target length")
            return "witness",path
        for part in parts:
            component=set(part)
            cnf.clauses.append([i for (u,v),i in edge.items() if (u in component)!=(v in component)])


def main():
    coil = json.loads((HERE/"coil9.json").read_bytes())["q9_rows"][0]["vertices"]
    verify(coil,True)
    solver=Path("D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe")
    result=[]
    with TemporaryDirectory(prefix="q9-coil-exchange-") as t:
        for parity in (0,1):
            base=bits(v for v in coil if v.bit_count()%2==parity)
            other=[v for v in range(512) if v.bit_count()%2==parity and not base & (1<<v)]
            cases=[(None,None)]+[(u,v) for u in vertices(base) for v in other]
            status_counts=Counter()
            timeouts=[]
            found=None
            for u,v in cases:
                mask=base if u is None else base ^ (1<<u) ^ (1<<v)
                status,path=search(mask,parity,solver,Path(t)/"coil.cnf")
                status_counts[status]+=1
                if status=="timeout":
                    timeouts.append([u,v])
                if path:
                    found=dict(deleted=u,inserted=v,path=path)
                    break
            result.append(dict(parity=parity,statuses=status_counts,timeouts=timeouts,witness=found))
            if found:
                break
    record=dict(source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),rows=result,
                solver_sha256=sha256(solver.read_bytes()).hexdigest())
    (HERE/"coil-exchanges.json").write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8",newline="\n")
    print([(r["parity"],r["statuses"]) for r in result])


if __name__ == "__main__":
    main()
