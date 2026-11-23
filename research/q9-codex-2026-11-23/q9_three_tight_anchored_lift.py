"""Replay dense Q6 representatives in a 221-edge search with three tight pairs."""
import argparse
import gzip
import json
from itertools import combinations
from pathlib import Path
from subprocess import CalledProcessError

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from q6_star_interfaces import check
from q9_lift_three_tight_pairs import surviving_profiles
from q9_short_cycle_clauses import add_small_cycles
from q9_three_tight_pairs import BONDS
from q9_three_tight_star_refine import anchor_list
from verify_q9_free_dimension_cuts import deg, parts


def add_layer_colour_balance(f, pool, edges, crossing_edges, endpoints):
    """In one layer, each internal edge contributes once to each colour."""
    from q9_overlapping_cross18 import value_literals
    from q9_square_census import add_popcount

    for layer, internal_count in enumerate(edges):
        for colour in (0, 1):
            # 2*selected = internal_count + crossings + endpoints.
            negative = [-lit for lit in crossing_edges[layer][colour]]
            negative.extend(-lit for u, lit in endpoints[layer]
                            if (u & 63).bit_count() % 2 == colour)
            selected = [u + 1 for u in range(64 * layer, 64 * (layer + 1))
                        if (u & 63).bit_count() % 2 == colour]
            bits = add_popcount(f, pool, [negative[:], selected])
            f.extend([literal] for literal in value_literals(bits, internal_count + len(negative)))


def form(row, saturated=False, balanced=False, layer_colour_balance=False, *, antipodal=False, distance_seven=False, distance_five=False, distance_three=False):
    edges,components,crossings = row
    f = CNF()
    pool = IDPool(start_from=513)
    internal = [[] for _ in range(8)]
    outside = {bond: [] for bond in BONDS}
    deficit = [2*c for c in components]
    endpoints = [[] for _ in components]
    crossing_edges = [[[], []] for _ in components] if layer_colour_balance else None
    assert not layer_colour_balance or (balanced and saturated)
    for (u,v),count in zip(BONDS,crossings):
        deficit[u] -= count
        deficit[v] -= count
    if saturated:
        assert min(deficit)>=0 and sum(deficit)==2
    for u in range(512):
        neighbors = [u^(1<<a) for a in range(9)]
        if balanced and deficit[u>>6]:
            terminal = pool.id()
            endpoints[u>>6].append((u,terminal))
            f.append([-terminal,u+1])
            for a,b in combinations(neighbors,2):
                f.append([-terminal,-a-1,-b-1])
            for omitted in neighbors:
                f.append([-u-1,terminal,*(v+1 for v in neighbors if v!=omitted)])
        if saturated:
            if deficit[u>>6]:
                f.append([-u-1,*(v+1 for v in neighbors)])
            else:
                for omitted in neighbors:
                    f.append([-u-1,*(v+1 for v in neighbors if v!=omitted)])
        for triple in combinations(neighbors,3):
            f.append([-u-1,*(-v-1 for v in triple)])
        for v in neighbors:
            if v <= u:
                continue
            bond = pool.id()
            f.extend([[-bond,u+1],[-bond,v+1],[bond,-u-1,-v-1]])
            left,right = u>>6,v>>6
            bank = internal[left] if left==right else outside[left,right]
            bank.append(bond)
            if crossing_edges is not None and left != right:
                colour = (u & 63).bit_count() % 2
                crossing_edges[left][colour].append(bond)
                crossing_edges[right][colour].append(bond)

    def exact(items,count):
        f.extend(CardEnc.equals(items,count,vpool=pool,encoding=EncType.cardnetwrk))

    for layer,(e,c) in enumerate(zip(edges,components)):
        exact(list(range(64*layer+1,64*(layer+1)+1)),e+c)
        exact(internal[layer],e)
    for bond,count in zip(BONDS,crossings):
        exact(outside[bond],count)
    if balanced:
        population = sum(e+c for e,c in zip(edges,components))
        assert saturated and population%2==0
        exact([u+1 for u in range(512) if u.bit_count()%2==0],population//2)
        for layer,markers in enumerate(endpoints):
            if markers:
                exact([lit for _,lit in markers],deficit[layer])
        exact([lit for markers in endpoints for u,lit in markers if u.bit_count()%2==0],1)
    assert sum((antipodal, distance_seven, distance_five, distance_three)) <= 1
    if antipodal or distance_seven:
        assert balanced and saturated
        terminal_layers = [i for i, count in enumerate(deficit) if count]
        assert len(terminal_layers) == 2
        layer_delta = terminal_layers[0] ^ terminal_layers[1]
        assert layer_delta.bit_count() == (3 if antipodal else 1)
        endpoint_delta = (layer_delta << 6) | 63
        assert all(deficit[layer] == 1 for layer in terminal_layers)
        left, right = (dict(endpoints[layer]) for layer in terminal_layers)
        for vertex, marker in left.items():
            partner = right[vertex ^ endpoint_delta]
            f.extend([[-marker, partner], [marker, -partner]])
    if distance_five or distance_three:
        assert balanced and saturated
        marker_distance = 5 if distance_five else 3
        markers = [pair for layer in endpoints for pair in layer]
        for vertex, marker in markers:
            partners = [lit for other, lit in markers if (vertex ^ other).bit_count() == marker_distance]
            f.append([-marker, *partners])
    if crossing_edges is not None:
        add_layer_colour_balance(f,pool,edges,crossing_edges,endpoints)
    add_small_cycles(f,9,3)
    return f


def candidate(f, assumptions, budget, capture_proof=False):
    cuts = []
    with Cadical195(bootstrap_with=f,with_proof=capture_proof) as solver:
        for bit in assumptions:
            solver.add_clause([bit])
        while (left:=budget-solver.accum_stats()['conflicts'])>0:
            solver.conf_budget(left)
            answer = solver.solve_limited()
            if answer is None:
                break
            if answer is False:
                proof = '\n'.join(solver.get_proof() or ['0'])+'\n' if capture_proof else None
                return 'UNSAT',cuts,None,proof
            selected = {v-1 for v in solver.get_model() if 1<=v<=512}
            assert len(selected)==222 and sum(deg(selected,v,9) for v in selected)==442
            assert max(deg(selected,v,9) for v in selected)<=2
            cycles = [sorted(s) for s in parts(selected,9) if all(deg(s,v,9)==2 for v in s)]
            if not cycles:
                assert len(parts(selected,9))==1
                return 'SAT_PATH_VERIFIED',cuts,sorted(selected),None
            for cycle in cycles:
                solver.add_clause([-u-1 for u in cycle])
                cuts.append(cycle)
    return 'UNKNOWN',cuts,None,None


def verify(f, assumptions, cuts, checker, proposed_proof=None):
    for cycle in cuts:
        vertices = set(cycle)
        assert len(vertices)==len(cycle) and all(0<=u<512 for u in vertices)
        assert len(parts(vertices,9))==1 and all(deg(vertices,u,9)==2 for u in vertices)
    f.extend([[x] for x in assumptions])
    f.extend([[-u-1 for u in cycle] for cycle in cuts])
    try:
        if proposed_proof is not None:
            try:
                check(f,proposed_proof,checker)
            except (AssertionError,CalledProcessError):
                pass
            else:
                return proposed_proof
        with Cadical195(bootstrap_with=f,with_proof=True) as certifier:
            assert certifier.solve() is False
            proof = '\n'.join(certifier.get_proof())+'\n'
        check(f,proof,checker)
        return proof
    finally:
        del f.clauses[-len(assumptions)-len(cuts):]


def run(args):
    if args.residual:
        rows = json.loads(args.residual.read_text())['profiles'].items()
    else:
        rows = ((str(i),row) for i,row in enumerate(surviving_profiles())
                if str(i) in args.indices)
    with gzip.open(args.output,'wt') as archive:
        for index,row in rows:
            e,c,_ = row
            center = min((i for i in range(8) if e[i]==25),key=lambda i: len(anchor_list(c[i])))
            anchors = anchor_list(c[center])
            assert anchors
            f = form(row)
            print(json.dumps(dict(status='STARTED',index=index,center=center,
                                  anchors=len(anchors),clauses=len(f.clauses))),flush=True)
            unknown = 0
            for mask in anchors:
                assumptions = [64*center+v+1 if mask>>v&1 else -64*center-v-1 for v in range(64)]
                status,cuts,witness,_ = candidate(f,assumptions,args.budget)
                proof = verify(f,assumptions,cuts,args.checker) if status=='UNSAT' else None
                unknown += status=='UNKNOWN'
                if proof:
                    status = 'UNSAT_DRAT_VERIFIED'
                record = dict(index=index,center=center,anchor=f'{mask:016x}',
                              status=status,cycles=cuts,proof=proof,witness=witness)
                archive.write(json.dumps(record)+'\n')
                archive.flush()
                if witness:
                    print(json.dumps(record),flush=True)
                    return
            print(json.dumps(dict(index=index,status='UNKNOWN' if unknown else 'PROFILE_EXCLUDED',
                                  tested=len(anchors),unknown=unknown)),flush=True)


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('checker')
    p.add_argument('output',type=Path)
    p.add_argument('--residual',type=Path)
    p.add_argument('--indices',nargs='+',default=[])
    p.add_argument('--budget',type=int,default=10000)
    run(p.parse_args())

