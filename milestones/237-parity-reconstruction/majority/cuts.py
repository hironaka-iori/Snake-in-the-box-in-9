"""Extract small cuts in the double cover of the contraction with a dummy."""
from collections import Counter, deque
import json
from finish import BASES, DUMMY, HERE, contraction


def cut(graph):
    # Any spanning cycle sends one unit in each direction on each cycle edge.
    residual = [{} for _ in range(1028)]
    def arc(u, v, capacity):
        residual[u][v] = capacity
        residual[v][u] = 0
    for u in graph:
        arc(1026, u, 2)
        arc(513+u, 1027, 2)
        for v in graph[u]:
            arc(u, 513+v, 1)
    units = 0
    while True:
        prev = {1026: -1}
        queue = deque([1026])
        while queue and 1027 not in prev:
            u = queue.popleft()
            for v, capacity in residual[u].items():
                if v not in prev and capacity:
                    queue.append(v)
                    prev[v] = u
        if 1027 not in prev:
            break
        v = 1027
        while v != 1026:
            u = prev[v]
            residual[u][v] -= 1
            residual[v][u] += 1
            v = u
        units += 1
    if units == 2*len(graph):
        return None
    reachable = set(prev)
    s = sorted(u for u in graph if u in reachable)
    t = sorted(v for v in graph if 513+v in reachable)
    escaping = sum(len(graph[u] - set(t)) for u in s)
    assert 2*len(s) > 2*len(t) + escaping
    return dict(s=s,t=t,escaping=escaping)


def main():
    bases = [set(b['vertices']) for b in json.loads(BASES.read_bytes())['bases']]
    decisions = json.loads((HERE/'decisions.json').read_bytes())
    rows = []
    for row in decisions:
        i,d,a,b = row['descriptions'][0]
        vertices = (bases[i]-{d}) | {a,b}
        graph = contraction(vertices)
        graph[DUMMY] = set(vertices)
        for v in vertices:
            graph[v].add(DUMMY)
        rows.append(cut(graph))
    sizes = Counter(None if row is None else len(row['s']) for row in rows)
    print('covered',sum(row is not None for row in rows),'of',len(rows),'sizes',dict(sizes))
    (HERE/'cuts.json').write_text(json.dumps(rows,separators=(',',':'))+'\n')


if __name__ == '__main__':
    main()
