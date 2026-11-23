"""Apply certified Q6 interface cuts to all endpoint orbits of the 221-edge search."""
import argparse
import gzip
import json
from itertools import combinations, permutations
from pathlib import Path

from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_direction_frequency import append_upper_bound, build, profile
from q9_endpoint_distance_bound import read_path
from q9_lift_three_tight_pairs import ROOT
from q9_overlapping_cross18 import value_literals
from q9_square_census import add_popcount
from q9_tight_interface_search import certify


def addition(f,pool,*numbers):
    columns = [[bits[i] for bits in numbers if i<len(bits)]
               for i in range(max(map(len,numbers)))]
    bits = add_popcount(f,pool,columns)
    assert all(x is not None for x in bits)
    return bits


def lower(f,bits,minimum,guard=()):
    append_upper_bound(f,[-x for x in bits],(1<<len(bits))-1-minimum,guard)


def equiv(f,left,right):
    for i in range(max(len(left),len(right))):
        if i>=len(left):
            f.append([-right[i]])
        elif i>=len(right):
            f.append([-left[i]])
        else:
            f.extend([[-left[i],right[i]],[left[i],-right[i]]])


def load_cuts():
    def load(name):
        return json.loads((ROOT/name).read_text())
    replay = [json.loads(line) for line in
              (ROOT/'q9_three_tight_stars_verification.log').read_text().splitlines()]
    assert replay[-1]['status']=='TRIPLE_NINE_BRANCH_VERIFIED' and replay[-1]['remaining']==0
    stars = load('verified_q6_star_cuts_first13.json')
    stars += load('verified_q6_general_star_first3.json')
    stars += load('q9_three_tight_residual.json')['cuts']
    stars = [json.loads(x) for x in sorted({json.dumps(key) for key in stars})]
    return load('verified_exact_interface_cuts_full.json'),stars


def exact_match_indicator(f, pool, literals):
    """Return a literal equivalent to a conjunction of physical count bits."""
    indicator = pool.id()
    f.extend([[-indicator, lit] for lit in literals])
    f.append([indicator, *(-lit for lit in literals)])
    return indicator


def add_geometry(f,end,triples,capacity=None,port_distances=None,geometry_cuts=(),
                 compact_patterns=False,q7_caps=False,q7_contacts=False,face_connectivity=False,projection_connectivity=False,q4_population=False,q4_tilings=False,q4_tiling_connectivity=False,bonds=None,monotone_seams=(),monotone_stars=()):
    pool = IDPool(start_from=f.nv+1)
    if bonds is None:
        actual_bonds = []
        for u in range(512):
            for axis in range(9):
                v = u|(1<<axis)
                if v==u:
                    continue
                x = pool.id()
                f.extend([[-x,u+1],[-x,v+1],[x,-u-1,-v-1]])
                actual_bonds.append((u,v,x))
    else:
        actual_bonds = bonds
    if q4_tilings or q4_tiling_connectivity:
        from q9_q4_forest_diagram import add_tiled_forests
        add_tiled_forests(f,pool,actual_bonds if q4_tiling_connectivity else None)
    if q4_population:
        from q9_q4_population import add_q4_population
        add_q4_population(f,pool,9)
    if projection_connectivity:
        from q9_projection_connectivity import add_projection_connectivity
        add_projection_connectivity(f,pool,actual_bonds,end,222)
    if face_connectivity:
        from q9_cube_face_connectivity import add_face_connectivity
        add_face_connectivity(f,pool,actual_bonds,9,222)
    if q7_caps or q7_contacts:
        from q9_q7_face_caps import add_q7_face_caps
        add_q7_face_caps(f,pool,actual_bonds,end,q7_contacts)
    exact_cuts,stars = load_cuts()
    truth = pool.id()
    f.append([truth])
    for axes in triples:
        labels = [sum((u>>a&1)<<i for i,a in enumerate(axes)) for u in range(512)]
        sides = {(u,u|(1<<i)):[] for i in range(3) for u in range(8) if not u>>i&1}
        physical_sides = {side:[] for side in sides} if port_distances else None
        inside = [[] for _ in range(8)]
        points = [[] for _ in range(8)]
        for u,label in enumerate(labels):
            points[label].append(u+1)
        for u,v,x in actual_bonds:
            a,b = labels[u],labels[v]
            target = inside[a] if a==b else sides[a,b]
            target.append(x)
            if physical_sides is not None and a!=b:
                physical_sides[a,b].append((u,x))
        number = [add_popcount(f,pool,[p]) for p in points]
        edges = [add_popcount(f,pool,[p]) for p in inside]
        cross = {k:add_popcount(f,pool,[p[:]]) for k,p in sides.items()}
        components = []
        for u in range(8):
            incident = [x for side,bank in sides.items() if u in side for x in bank]
            incident += [truth]*(int(u==0)+int(u==labels[end]))
            total = add_popcount(f,pool,[incident])
            f.append([-total[0]])
            c = total[1:]
            components.append(c)
            equiv(f,number[u],addition(f,pool,edges[u],c))
            append_upper_bound(f,number[u],32)
            append_upper_bound(f,edges[u],26)
            append_upper_bound(f,edges[u],0,[-x for x in value_literals(c,0)])
            append_upper_bound(f,edges[u],25,[-x for x in value_literals(c,3)])
            below_four = pool.id()
            append_upper_bound(f,c,3,[-below_four])
            append_upper_bound(f,edges[u],24,[below_four])

        def match(u,e,c):
            return value_literals(edges[u],e)+value_literals(components[u],c)

        thresholds = {}
        def at_least(bits,n):
            key = tuple(bits),n
            if key not in thresholds:
                t = pool.id()
                thresholds[key] = t
                lower(f,bits,n,[-t])
                append_upper_bound(f,bits,n-1,[t])
            return thresholds[key]

        if capacity:
            for face in range(8):
                classes = [[],[]]
                for u,label in enumerate(labels):
                    if label==face:
                        inner_colour = (u.bit_count()-label.bit_count())%2
                        classes[inner_colour].append(u+1)
                black,white = [add_popcount(f,pool,[vertices]) for vertices in classes]
                for (e,b),limit in capacity.items():
                    for minor,major in ((black,white),(white,black)):
                        conditions = value_literals(edges[face],e)+value_literals(minor,b)
                        conditions.append(at_least(major,max(b,limit+1)))
                        f.append([-x for x in conditions])

        if physical_sides is not None:
            dense = []
            for face in range(8):
                active = pool.id()
                dense.append(active)
                required = value_literals(edges[face],25)
                f.extend([[-active,x] for x in required])
                f.append([active,*(-x for x in required)])
            for (a,b),physical in physical_sides.items():
                for (u,x),(v,y) in combinations(physical,2):
                    if (u^v).bit_count() not in port_distances:
                        f.append([-dense[a],-dense[b],-x,-y])

        from q9_geometry_cut_library import compatible_endpoint_patterns

        pattern_indicators = {}
        for faces,links in compatible_endpoint_patterns(geometry_cuts,labels[end]):
            groups = [tuple(match(u,e,c)) for u,e,c in faces]
            groups += [tuple(value_literals(cross[u,v],r)) for u,v,r in links]
            if compact_patterns:
                for group in groups:
                    if group not in pattern_indicators:
                        pattern_indicators[group] = exact_match_indicator(f, pool, group)
                f.append([-pattern_indicators[group] for group in groups])
            else:
                f.append([-lit for group in groups for lit in group])

        for (u,v),bits in cross.items():
            for a,b in ((u,v),(v,u)):
                f.append([-at_least(bits,1),-at_least(edges[a],26),-at_least(edges[b],24)])
                for ea, ca, eb, nb, r in monotone_seams:
                    conditions = match(a,ea,ca)
                    conditions.extend((at_least(edges[b],eb),at_least(number[b],nb),
                                       at_least(bits,r)))
                    f.append([-x for x in conditions])
                for (ea,ca),(eb,cb),r in exact_cuts:
                    conditions = match(a,ea,ca)+match(b,eb,cb)+value_literals(bits,r)
                    f.append([-x for x in conditions])
        for u in range(8):
            neighbors = [u^(1<<i) for i in range(3)]
            for e, c, leaves in monotone_stars:
                for ordering in permutations(neighbors, len(leaves)):
                    conditions = match(u,e,c)
                    for v, (ev, nv, r) in zip(ordering, leaves):
                        bits = cross[tuple(sorted((u,v)))]
                        conditions.extend((at_least(edges[v],ev),at_least(number[v],nv),
                                           at_least(bits,r)))
                    f.append([-x for x in conditions])
            for e,c,leaves in stars:
                for ordering in permutations(neighbors,len(leaves)):
                    conditions = match(u,e,c)
                    for v,(ev,cv,r) in zip(ordering,leaves):
                        bits = cross[tuple(sorted((u,v)))]
                        if cv is None:
                            conditions += [at_least(edges[v],ev),at_least(bits,r)]
                        else:
                            conditions += match(v,ev,cv)+value_literals(bits,r)
                    f.append([-x for x in conditions])


def triples_for(distance):
    triples = [(0,1,2)]
    if distance<9:
        triples.append((0,1,distance))
    if distance+1<9:
        triples.append((0,distance,distance+1))
    if distance+2<9:
        triples.append((distance,distance+1,distance+2))
    if distance>=6:
        triples.append((3,4,5))
    return triples


def control(capacity=None,port_distances=None,geometry_cuts=(),compact_patterns=False):
    with gzip.open(ROOT.parent/'q9_port_followup_public191.txt.gz','rt') as source:
        original = list(map(int,next(source).split()))
    origin = original[0]
    delta = origin^original[-1]
    counts = profile(original,9)
    order = sorted(range(9),key=lambda a:(not (delta>>a&1),counts[a]))
    path = [sum((((v^origin)>>a)&1)<<i for i,a in enumerate(order)) for v in original]
    d = delta.bit_count()
    f,end,_ = build(9,len(path)-1,d)
    add_geometry(f,end,triples_for(d),capacity,port_distances,geometry_cuts,
                 compact_patterns=compact_patterns)
    s = set(path)
    with Cadical195(bootstrap_with=f) as solver:
        assert solver.solve(assumptions=[u+1 if u in s else -u-1 for u in range(512)])
        assert read_path(solver.get_model(),9,len(path)-1,end)==path
    print(json.dumps(dict(status='CONTROL_OK',length=len(path)-1,distance=d)),flush=True)


def search(d,budget,checker,stem):
    f,end,counts = build(9,221,d)
    lower(f,counts[2],11)
    triples = triples_for(d)
    add_geometry(f,end,triples)
    header = dict(distance=d,triples=triples,budget=budget,clauses=len(f.clauses))
    print(json.dumps(dict(status='STARTED',**header)),flush=True)
    with Cadical195(bootstrap_with=f) as solver:
        solver.conf_budget(budget)
        answer = solver.solve_limited()
        status = 'UNKNOWN'
        if answer is False:
            status = certify(f,[end+1],stem,checker)
        elif answer:
            path = read_path(solver.get_model(),9,221,end)
            stem.with_suffix('.path').write_text(' '.join(map(str,path))+'\n')
            status = 'SAT_PATH_VERIFIED'
        print(json.dumps(dict(status=status,conflicts=solver.accum_stats()['conflicts'],
                              **header)),flush=True)


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--control',action='store_true')
    p.add_argument('--distance',type=int,choices=(3,5,7,9))
    p.add_argument('--budget',type=int,default=150000)
    p.add_argument('--checker')
    p.add_argument('--stem',type=Path)
    a = p.parse_args()
    if a.control:
        control()
    else:
        search(a.distance,a.budget,a.checker,a.stem)

