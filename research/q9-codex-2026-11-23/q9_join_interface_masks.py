"""Join exact Q6 interfaces by actual vertex masks across connected layers."""
import argparse
from collections import defaultdict
from functools import lru_cache
from itertools import permutations
import json
from pathlib import Path

from q9_dense_pair_full_lift import table
from q9_three_tight_pairs import BONDS
from verify_q9_free_dimension_cuts import deg, parts


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask -= bit


@lru_cache(maxsize=None)
def move_table(order,origin):
    return tuple(sum(((v^origin)>>axis&1)<<i for i,axis in enumerate(order)) for v in range(64))


def move(mask,mapping):
    return sum(1<<mapping[u] for u in vertices(mask))


@lru_cache(maxsize=40000)
def normalize(mask):
    selected = set(vertices(mask))
    adj = {u:{u^(1<<i) for i in range(6)}&selected for u in selected}
    value = (1<<64)-1
    maps = set()
    for start in selected:
        if len(adj[start])!=1:
            continue
        v,prev = start,None
        axes = []
        while following:=adj[v]-{prev}:
            assert len(following)==1
            w = next(iter(following))
            axis = (v^w).bit_length()-1
            if axis not in axes:
                axes.append(axis)
            prev,v = v,w
        unused = tuple(i for i in range(6) if i not in axes)
        for tail in permutations(unused):
            labels = move_table(tuple(axes)+tail,start)
            transformed = move(mask,labels)
            if transformed<value:
                value = transformed
                maps = set()
            if transformed==value:
                maps.add(labels)
    assert maps
    return value,tuple(sorted(maps))


class Catalogue:
    def __init__(self,source, *, wanted=None):
        self.banks = defaultdict(lambda:defaultdict(set))
        placements = table(source,wanted) if isinstance(source,Path) else source
        for (ea,ca,eb,cb,r),pairs in placements.items():
            for a,b in pairs:
                for key,u,v in (((ea,ca,eb,cb,r),a,b),((eb,cb,ea,ca,r),b,a)):
                    canonical,maps = normalize(u)
                    self.banks[key][canonical].update(move(v,mapping) for mapping in maps)

    @lru_cache(maxsize=100000)
    def activate(self,key,mask):
        canonical,maps = normalize(mask)
        compatible = self.banks[key].get(canonical,())
        inverse = [0]*64
        for before,after in enumerate(maps[0]):
            inverse[after] = before
        return frozenset(move(p,inverse) for p in compatible)


@lru_cache(maxsize=50000)
def degrees(mask):
    selected = set(vertices(mask))
    return tuple(sum(1<<u for u in selected if deg(selected,u,6)==k) for k in (1,2))


def legal(chosen,crossing,endpoint_deficits=None):
    for v,mask in chosen.items():
        one,two = degrees(mask)
        once,twice = 0,0
        for axis in range(3):
            w = v^(1<<axis)
            if w not in chosen:
                continue
            link = mask&chosen[w]
            edge = tuple(sorted((v,w)))
            if link.bit_count()!=crossing[edge] or (link & (two|twice|(one&once))):
                return False
            twice |= once&link
            once |= link
        if endpoint_deficits is not None:
            open_sites = (mask & ~(two | twice | (one & once))).bit_count()
            demands = [endpoint_deficits[v]]
            for axis in range(3):
                neighbor = v ^ (1<<axis)
                if neighbor not in chosen:
                    demands.append(crossing[tuple(sorted((v,neighbor)))])
            if max(demands) > open_sites:
                return False
    return True


def no_cycles(chosen):
    points = {64*layer+u for layer,mask in chosen.items() for u in vertices(mask)}
    return all(any(deg(points,u,9)<2 for u in component) for component in parts(points,9))


def join(row,catalogue,budget,completion_ports=False):
    count_e,count_c,r = row
    crossing = dict(zip(BONDS,r))
    endpoint_deficits = None
    if completion_ports:
        endpoint_deficits = [2*c for c in count_c]
        for (u,v),n in crossing.items():
            endpoint_deficits[u] -= n
            endpoint_deficits[v] -= n
        assert min(endpoint_deficits)>=0 and sum(endpoint_deficits)==2
    graph = defaultdict(dict)
    for (a,b),k in crossing.items():
        ab = (count_e[a],count_c[a],count_e[b],count_c[b],k)
        if ab in catalogue.banks:
            graph[a][b] = ab
            graph[b][a] = (ab[2],ab[3],ab[0],ab[1],k)
    unvisited = set(graph)
    tested = 0
    components = []
    while unvisited:
        start = min(unvisited)
        todo = [start]
        found = {start}
        for v in todo:
            more = set(graph[v])-found
            todo.extend(sorted(more))
            found.update(more)
        unvisited -= found

        def root_masks(v):
            return set.intersection(*(set(catalogue.banks[k]) for k in graph[v].values()))

        root = min(found,key=lambda v:(len(root_masks(v)),-len(graph[v]),v))
        chosen = {}
        def visit():
            nonlocal tested
            if len(chosen)==len(found):
                return no_cycles(chosen)
            if not chosen:
                v,values = root,root_masks(root)
            else:
                possibilities = []
                for v in sorted(found-set(chosen)):
                    options = [catalogue.activate(graph[u][v],chosen[u]) for u in graph[v] if u in chosen]
                    if options:
                        values = set.intersection(*(set(o) for o in options))
                        possibilities.append((len(values),v,values))
                _,v,values = min(possibilities)
            for mask in sorted(values):
                tested += 1
                if tested>budget:
                    raise TimeoutError
                chosen[v] = mask
                if legal(chosen,crossing,endpoint_deficits) and visit():
                    return True
                del chosen[v]
            return False

        try:
            if not visit():
                return dict(status='EXHAUSTIVE_JOIN_EXCLUDED',states=tested,layers=sorted(found))
        except TimeoutError:
            return dict(status='UNKNOWN',states=tested,layers=sorted(found))
        components.append(dict(layers=sorted(found),
                               masks={i:f'{m:016x}' for i,m in sorted(chosen.items())}))
    return dict(status='CONSISTENT_SUBASSEMBLIES',states=tested,components=components)


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('profiles',type=Path)
    p.add_argument('selection',type=Path)
    p.add_argument('table',type=Path)
    p.add_argument('--budget',type=int,default=6000)
    p.add_argument('--completion-ports',action='store_true')
    a=p.parse_args()
    bank=json.loads(a.profiles.read_text())['representatives']
    cases=json.loads(a.selection.read_text())['indices']
    catalogue=Catalogue(a.table)
    for index in cases:
        print(json.dumps(dict(index=index,**join(bank[index],catalogue,a.budget,a.completion_ports))),flush=True)

