"""Decide the surviving contracted graphs by branching on edges of a spanning cycle."""
from collections import Counter
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASES = ROOT / 'milestones/236-parity-exchange-frontier/data/bases.json'
DUMMY = 512


def contraction(vertices):
    graph = {v: set() for v in sorted(vertices)}
    for label in range(512):
        adjacent = [v for v in (label ^ (1 << j) for j in range(9)) if v in vertices]
        if len(adjacent) == 2:
            v, w = adjacent
            graph[v].add(w)
            graph[w].add(v)
    return graph


def search(graph, selected):
    while True:
        changed = False
        for v in graph:
            if len(graph[v]) < 2:
                return ['degree', v]
            if len(selected[v]) > 2:
                return ['forced', v]
            free = graph[v] - selected[v]
            if not free:
                continue
            if len(graph[v]) == 2:
                for w in free:
                    selected[v].add(w)
                    selected[w].add(v)
                changed = True
            elif len(selected[v]) == 2:
                for w in free:
                    graph[v].remove(w)
                    graph[w].remove(v)
                changed = True
        if not changed:
            break

    left = set(graph)
    while left:
        stack = [min(left)]
        component = set()
        while stack:
            v = stack.pop()
            if v not in component:
                component.add(v)
                stack.extend(selected[v] - component)
        if all(len(selected[v]) == 2 for v in component):
            if len(component) < len(graph):
                return ['cycle', min(component)]
            v = DUMMY
            path = []
            previous = None
            while len(path) < len(graph):
                path.append(v)
                following = min(selected[v] - {previous})
                previous, v = v, following
            assert v == DUMMY and len(set(path)) == len(graph)
            return ['witness', path[1:]]
        left -= component

    v = min((u for u in graph if len(selected[u]) < 2),
            key=lambda u: (len(graph[u] - selected[u]), u))
    w = min(graph[v] - selected[v])
    g1 = {u: ns.copy() for u, ns in graph.items()}
    s1 = {u: ns.copy() for u, ns in selected.items()}
    s1[v].add(w)
    s1[w].add(v)
    take = search(g1, s1)
    if take[0] == 'witness':
        return take
    graph[v].remove(w)
    graph[w].remove(v)
    leave = search(graph, selected)
    return leave if leave[0] == 'witness' else ['split', v, w, take, leave]


def solve(vertices):
    graph = contraction(vertices)
    leaves = sorted(v for v in vertices if len(graph[v]) == 1)
    assert all(graph.values()) and len(leaves) <= 2
    ends = leaves if len(leaves) == 2 else sorted(vertices)
    graph[DUMMY] = set(ends)
    for v in ends:
        graph[v].add(DUMMY)
    return search(graph, {v: set() for v in graph})


def main():
    bases = [frozenset(b['vertices']) for b in json.loads(BASES.read_bytes())['bases']]
    descriptions = Path(sys.argv[1]).read_text().splitlines()
    groups = {}
    cache = {}
    for line in descriptions:
        i, d, a, b = map(int, line.split())
        assert d in bases[i] and a < b and not ({a,b} & bases[i])
        vertices = (bases[i] - {d}) | {a,b}
        if vertices not in cache:
            cache[vertices] = len(groups)
            groups[len(groups)] = dict(descriptions=[], proof=solve(vertices))
        groups[cache[vertices]]['descriptions'].append([i,d,a,b])
    result = list(groups.values())
    print(len(descriptions), len(groups), Counter(row['proof'][0] for row in result))
    (HERE/'decisions.json').write_text(json.dumps(result,separators=(',',':'))+'\n')


if __name__ == '__main__':
    main()
