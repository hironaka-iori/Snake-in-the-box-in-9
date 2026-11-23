"""Certify failed interface joins with SAT on the actual connected layers."""
import argparse
import gzip
from itertools import combinations
import json
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from q6_star_interfaces import check
from q9_join_interface_masks import Catalogue
from q9_three_tight_pairs import BONDS
from verify_q9_free_dimension_cuts import deg, parts


def domain_graph(row,layers,catalogue,limit):
    e,c,cross = row
    edges = {}
    for (a,b),r in zip(BONDS,cross):
        key = e[a],c[a],e[b],c[b],r
        if a in layers and b in layers and key in catalogue.banks:
            edges[a,b] = key
            edges[b,a] = e[b],c[b],e[a],c[a],r
    base = {a:set.intersection(*(set(catalogue.banks[k])
                                for (u,_),k in edges.items() if u==a)) for a in layers}
    root = min(layers,key=lambda a:(len(base[a]),a))
    domains = {root:base[root]}
    while len(domains)<len(layers):
        frontier = {a:tuple(b for b in domains if (b,a) in edges)
                    for a in layers if a not in domains}
        a = min((i for i in frontier if frontier[i]), key=lambda i:(
            sum(len(domains[b]) for b in frontier[i]),i))
        needed = None
        for b in frontier[a]:
            possible = set().union(*(catalogue.activate(edges[b,a],v) for v in domains[b]))
            needed = possible if needed is None else needed&possible
        domains[a] = needed
        if sum(map(len,domains.values()))>limit:
            raise TimeoutError
    return domains


def prune_interface_domains(row, catalogue, domains):
    # A mask needs a compatible neighbor on every certified seam it meets.
    edges, components, crossings = row
    arcs = []
    for (a, b), count in zip(BONDS, crossings):
        if a not in domains or b not in domains:
            continue
        key = (edges[a], components[a], edges[b], components[b], count)
        if key in catalogue.banks:
            arcs.append((a, b, key))
            arcs.append((b, a, (*key[2:4], *key[:2], count)))
    changed = True
    while changed:
        changed = False
        for a, b, key in arcs:
            old = domains[b]
            if not old:
                continue
            supported = set()
            for mask in sorted(domains[a]):
                supported.update(catalogue.activate(key, mask) & old)
                if len(supported) == len(old):
                    break
            if supported != old:
                domains[b] = supported
                changed = True
    return domains


def omittable_crossings(row,layers,catalogue):
    e,c,cross = row
    return {(a,b) for (a,b),r in zip(BONDS,cross)
            if a in layers and b in layers
            and (e[a],c[a],e[b],c[b],r) not in catalogue.banks}


def require_completion_ports(formula,pool,row,layers,selected,exterior_ports=None,shared_exterior=False,
                             exterior_degree=False):
    """Use virtual neighbours for required crossings to the omitted layers."""
    _,components,crossings = row
    by_vertex = {u:[] for u in selected}
    ends = [2*c for c in components]
    seam_even = {}

    exterior_vertices = {}
    if shared_exterior or exterior_degree:
        threshold = 1 if exterior_degree else 2
        for layer in sorted(set(range(8))-set(layers)):
            if sum((layer^(1<<axis)) in layers for axis in range(3)) >= threshold:
                exterior_vertices[layer] = [pool.id() for _ in range(64)]

    def add_ports(layer, count, exterior=False, neighbour=None):
        ports = []
        even_ports = []
        if count:
            for u in range(64*layer,64*(layer+1)):
                port = pool.id()
                ports.append(port)
                if (u&63).bit_count()%2==0:
                    even_ports.append(port)
                by_vertex[u].append(port)
                if exterior and exterior_ports is not None:
                    exterior_ports[u].append(port)
                formula.append([-port,u+1])
                if neighbour in exterior_vertices:
                    other = exterior_vertices[neighbour][u&63]
                    formula.extend([[-port,other],[-u-1,-other,port]])
            formula.extend(CardEnc.equals(ports,count,vpool=pool,encoding=EncType.cardnetwrk))
        elif neighbour in exterior_vertices:
            for u,other in enumerate(exterior_vertices[neighbour],64*layer):
                formula.append([-u-1,-other])
        return even_ports

    for (a,b),count in zip(BONDS,crossings):
        ends[a] -= count
        ends[b] -= count
        if (a in layers)!=(b in layers):
            inside,outside = (a,b) if a in layers else (b,a)
            seam_even[a,b] = add_ports(inside,count,exterior=True,neighbour=outside)
    assert min(ends)>=0 and sum(ends)==2
    for layer in sorted(layers):
        add_ports(layer,ends[layer])
    for u in sorted(selected):
        neighbors = [v+1 for axis in range(9) if (v:=u^(1<<axis)) in selected]
        neighbors += by_vertex[u]
        if len(neighbors)<2:
            formula.append([-u-1])
            continue
        for omitted in neighbors:
            formula.append([-u-1,*(v for v in neighbors if v!=omitted)])
        for three in combinations(neighbors,3):
            formula.append([-u-1,*(-v for v in three)])
    if exterior_degree:
        present = {u:u+1 for u in selected}
        present.update((64*layer+u,lit) for layer,sites in exterior_vertices.items()
                       for u,lit in enumerate(sites))
        for layer,sites in exterior_vertices.items():
            for u,lit in enumerate(sites,64*layer):
                neighbors = [present[v] for axis in range(9) if (v:=u^(1<<axis)) in present]
                for three in combinations(neighbors,3):
                    formula.append([-lit,*(-v for v in three)])
    return seam_even


def add_completion_colours(formula,pool,row,layers,seam_even,signatures):
    from q9_exact_interface_colour_screen import add_colour_problem
    counts = [sum(n for (u,v),n in zip(BONDS,row[2]) if u^v==1<<axis) for axis in range(3)]
    black,ports = add_colour_problem(formula,pool,row,counts,signatures,start_even=pool.id())

    def equate_count(variables, unary):
        formula.extend(CardEnc.equals(variables+[-b for b in unary],len(unary),
                                       vpool=pool,encoding=EncType.seqcounter))
    for layer in sorted(layers):
        even_vertices = [64*layer+u+1 for u in range(64) if u.bit_count()%2==0]
        equate_count(even_vertices,black[layer])
    for bond,population in seam_even.items():
        equate_count(population,ports[bond])


def pin_domains(f,pool,domains):
    for a in sorted(domains):
        choices = []
        for mask in sorted(domains[a]):
            choice = pool.id()
            choices.append(choice)
            f.extend([[-choice,64*a+v+1 if mask>>v&1 else -64*a-v-1] for v in range(64)])
        if choices:
            f.append(choices)
        else:
            contradiction = pool.id()
            f.extend([[contradiction],[-contradiction]])


def make(row,layers,catalogue,limit,omit=(),completion_ports=False,interface_colours=None,
         exterior_ports=None,shared_exterior=False,exterior_degree=False):
    if interface_colours is not None and not completion_ports:
        raise ValueError('Interface colours require completion ports')
    if (shared_exterior or exterior_degree) and not completion_ports:
        raise ValueError('Shared exterior vertices require completion ports')
    if completion_ports and omit:
        raise ValueError('Completion ports need every specified internal crossing')
    if not set(omit)<=omittable_crossings(row,layers,catalogue):
        raise ValueError('Cannot omit a crossing used to infer a layout domain')
    domains = domain_graph(row,layers,catalogue,limit)
    f = CNF()
    pool = IDPool(start_from=513)
    selected = {64*a+v for a in layers for v in range(64)}
    pin_domains(f,pool,domains)
    if completion_ports:
        seam_even = require_completion_ports(f,pool,row,layers,selected,exterior_ports,shared_exterior,
                                             exterior_degree)
    else:
        for u in sorted(selected):
            neighbors = [u^(1<<i) for i in range(9) if u^(1<<i) in selected]
            for three in combinations(neighbors,3):
                f.append([-u-1,*(-v-1 for v in three)])
    for (a,b),cross in zip(BONDS,row[2]):
        if a not in layers or b not in layers or (a,b) in omit:
            continue
        bonds = []
        for v in range(64):
            u,w = a*64+v+1,b*64+v+1
            bond = pool.id()
            bonds.append(bond)
            f.extend([[-bond,u],[-bond,w],[-u,-w,bond]])
        f.extend(CardEnc.equals(bonds,cross,vpool=pool,encoding=EncType.cardnetwrk))
        if interface_colours is not None:
            seam_even[a,b] = [bond for v,bond in enumerate(bonds) if v.bit_count()%2==0]
    if interface_colours is not None:
        add_completion_colours(f,pool,row,layers,seam_even,interface_colours)
    return f,sum(map(len,domains.values()))


def trial(row,layers,catalogue,limit,budget,checker,omit=(),completion_ports=False,interface_colours=None):
    try:
        f,n = make(row,layers,catalogue,limit,omit,completion_ports,interface_colours)
    except TimeoutError:
        return dict(status='DOMAIN_LIMIT')
    cycles = []
    with Cadical195(bootstrap_with=f,with_proof=True) as solver:
        while (remaining:=budget-solver.accum_stats()['conflicts'])>0:
            solver.conf_budget(remaining)
            answer=solver.solve_limited()
            if answer is None:
                break
            if answer is False:
                proof='\n'.join(solver.get_proof() or ['0'])+'\n'
                check(f,proof,checker)
                return dict(status='UNSAT_DRAT_VERIFIED',layouts=n,cycles=cycles,proof=proof)
            points={u-1 for u in solver.get_model() if 0<u<=512 and (u-1)>>6 in layers}
            found=[sorted(s) for s in parts(points,9) if all(deg(points,u,9)==2 for u in s)]
            if not found:
                return dict(status='CONSISTENT_SUBASSEMBLY',layouts=n,points=sorted(points))
            for cycle in found:
                clause=[-u-1 for u in cycle]
                f.append(clause)
                solver.add_clause(clause)
                cycles.append(cycle)
    return dict(status='UNKNOWN',layouts=n)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('profiles',type=Path)
    p.add_argument('joins',type=Path)
    p.add_argument('table',type=Path)
    p.add_argument('output',type=Path)
    p.add_argument('checker')
    p.add_argument('--limit',type=int,default=12000)
    p.add_argument('--budget',type=int,default=70000)
    p.add_argument('--include-budget-stops',action='store_true')
    p.add_argument('--completion-ports',action='store_true')
    p.add_argument('--completion-colours',action='store_true')
    p.add_argument('--include-consistent',action='store_true')
    a=p.parse_args()
    catalogue=Catalogue(a.table)
    colours = None
    if a.completion_colours:
        if not a.completion_ports:
            p.error('--completion-colours requires --completion-ports')
        from q9_exact_interface_colour_screen import colour_signatures
        colours = colour_signatures(a.table)
    bank=json.loads(a.profiles.read_text())['representatives']
    with gzip.open(a.output,'wt') as output:
        for line in a.joins.read_text().splitlines():
            old=json.loads(line)
            eligible = {'EXHAUSTIVE_JOIN_EXCLUDED','UNKNOWN'} if a.include_budget_stops else {'EXHAUSTIVE_JOIN_EXCLUDED'}
            if old['status']=='CONSISTENT_SUBASSEMBLIES' and a.include_consistent:
                if not old['components']:
                    continue
                layers = set(max(old['components'],key=lambda item:len(item['layers']))['layers'])
            elif old['status'] in eligible:
                layers = set(old['layers'])
            else:
                continue
            i=old['index']
            result=trial(bank[i],layers,catalogue,a.limit,a.budget,a.checker,completion_ports=a.completion_ports,interface_colours=colours)
            row=dict(index=i,layers=sorted(layers),**result)
            if a.completion_ports:
                row['completion_ports'] = True
            if a.completion_colours:
                row['completion_colours'] = True
            print(json.dumps({k:v for k,v in row.items() if k not in ('proof','cycles','points')}),flush=True)
            output.write(json.dumps(row)+'\n')
            output.flush()

