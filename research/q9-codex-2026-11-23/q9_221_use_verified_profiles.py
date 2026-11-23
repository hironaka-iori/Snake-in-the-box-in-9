"""Apply independently replayed forbidden direction triples to the full Q9 model."""
import argparse
import json
from itertools import combinations, permutations
from pathlib import Path

from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_221_global_interface_cuts import add_geometry, addition, lower, triples_for
from q9_direction_frequency import build
from q9_endpoint_distance_bound import read_path
from q9_overlapping_cross18 import value_literals
from q9_tight_interface_search import certify


def exclude_profiles(f, counts, distance, profiles, ordered=True):
    added = 0
    for values in sorted({tuple(sorted(row)) for row in profiles}):
        odd = tuple(n for n in values if n%2)
        even = tuple(n for n in values if n%2==0)
        for first in combinations(range(distance),len(odd)):
            for last in combinations(range(distance,9),len(even)):
                odd_orders = (odd,) if ordered else sorted(set(permutations(odd)))
                even_orders = (even,) if ordered else sorted(set(permutations(even)))
                for odd_values in odd_orders:
                    for even_values in even_orders:
                        f.append([-x for axis,n in zip(first+last,odd_values+even_values)
                                  for x in value_literals(counts[axis],n)])
                        added += 1
    return added


def triple_floor(profiles, odd_count):
    forbidden = {tuple(sorted(row)) for row in profiles}
    for total in range(26,223):
        for a in range(3,total//3+1):
            for b in range(max(a,17-a),(total-a)//2+1):
                c = total-a-b
                if ((a%2)+(b%2)+(c%2)==odd_count and
                        (a,b,c) not in forbidden):
                    return total
    raise ValueError('No frequency triple in the covered range')


def add_triple_floors(f,counts,distance,profiles,ordered=True):
    pool = IDPool(start_from=f.nv+1)
    floors = {}
    for odd in range(4):
        even = 3-odd
        if odd>distance or even>9-distance:
            continue
        first = [tuple(range(odd))] if ordered else combinations(range(distance),odd)
        last = [tuple(range(distance,distance+even))] if ordered else list(combinations(range(distance,9),even))
        bound = triple_floor(profiles,odd)
        for a in first:
            for b in last:
                lower(f,addition(f,pool,*(counts[axis] for axis in a+b)),bound)
        floors[odd] = bound
    return floors


def search(d,budget,checker,stem,ledger,capacity=None,port_distances=None,geometry_cuts=(),
           compact_patterns=False,prefix_cuts=(),column_cuts=False,axis_windows=(),count_lex=False,q7_caps=False,q7_contacts=False,frequency_cubes=False,uniform_profiles=False,two_step_cuts=False,two_step_balls=False,lazy_cycles=False,face_connectivity=False,projection_connectivity=False,q4_population=False,short_cycles=0,q4_tilings=False,q4_tiling_connectivity=False):
    profiles = json.loads(ledger.read_text())
    f,end,counts = build(9,221,d,prefix_cuts=prefix_cuts,column_cuts=column_cuts,
                         axis_windows=axis_windows,include_rank=not lazy_cycles)
    lower(f,counts[2],11)
    added = exclude_profiles(f,counts,d,profiles)
    floors = add_triple_floors(f,counts,d,profiles)
    add_geometry(f,end,triples_for(d),capacity,port_distances,geometry_cuts,
                 compact_patterns=compact_patterns,q7_caps=q7_caps,q7_contacts=q7_contacts,face_connectivity=face_connectivity,
                 projection_connectivity=projection_connectivity,q4_population=q4_population,q4_tilings=q4_tilings,
                 q4_tiling_connectivity=q4_tiling_connectivity)
    if two_step_cuts or two_step_balls:
        from q9_two_step_availability import add_two_step_availability
        add_two_step_availability(f,9,(0,end),221,ball_cuts=two_step_balls)
    if short_cycles:
        from q9_short_cycle_clauses import add_small_cycles
        add_small_cycles(f,9,short_cycles)
    if count_lex:
        from q9_count_lex import add_count_lex
        add_count_lex(f,counts,end,d)
    header = dict(distance=d,budget=budget,clauses=len(f.clauses),
                  variables=f.nv,literals=sum(map(len,f.clauses)),
                  compact_patterns=compact_patterns,prefix_cuts=prefix_cuts,column_cuts=column_cuts,
                  axis_windows=len(axis_windows),count_lex=count_lex,q7_caps=q7_caps,q7_contacts=q7_contacts,two_step_cuts=two_step_cuts,two_step_balls=two_step_balls,lazy_cycles=lazy_cycles,face_connectivity=face_connectivity,projection_connectivity=projection_connectivity,q4_population=q4_population,short_cycles=short_cycles,q4_tilings=q4_tilings,q4_tiling_connectivity=q4_tiling_connectivity,forbidden_profiles=profiles,direction_clauses=added,triple_floors=floors,colour_capacity=bool(capacity),port_distances=sorted(port_distances or ()),geometry_cuts=len(geometry_cuts))
    if uniform_profiles:
        from q9_antipodal_uniform_profiles import solve_uniform
        solve_uniform(f,end,counts,header,stem,checker)
        return
    if frequency_cubes:
        from q9_antipodal_frequency_cubes import solve_cubes
        solve_cubes(f,end,counts,header,stem,checker)
        return
    print(json.dumps(dict(status='STARTED',**header)),flush=True)
    if lazy_cycles:
        from q9_lazy_colour_cycles import solve_relaxation
        solve_relaxation(f,end,header,stem,checker)
        return
    with Cadical195(bootstrap_with=f) as solver:
        solver.conf_budget(budget)
        result = solver.solve_limited()
        status = 'UNKNOWN'
        if result is False:
            status = certify(f,[end+1],stem,checker)
        elif result:
            path = read_path(solver.get_model(),9,221,end)
            stem.with_suffix('.path').write_text(' '.join(map(str,path))+'\n')
            status = 'SAT_PATH_VERIFIED'
        print(json.dumps(dict(status=status,conflicts=solver.accum_stats()['conflicts'],
                              **header)),flush=True)


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('distance',type=int,choices=(3,5,7,9))
    p.add_argument('budget',type=int)
    p.add_argument('checker')
    p.add_argument('stem',type=Path)
    p.add_argument('ledger',type=Path)
    p.add_argument('--capacity-table',type=Path)
    p.add_argument('--port-distance-table',type=Path)
    p.add_argument('--geometric-library',type=Path)
    p.add_argument('--compact-patterns',action='store_true')
    p.add_argument('--prefix-cuts',type=int,nargs='+',default=())
    p.add_argument('--column-cuts',action='store_true')
    p.add_argument('--axis-windows',action='store_true')
    p.add_argument('--short-axis-windows',action='store_true')
    p.add_argument('--count-lex',action='store_true')
    p.add_argument('--q7-caps',action='store_true')
    p.add_argument('--long-axis-windows',action='store_true')
    p.add_argument('--q7-contacts',action='store_true')
    p.add_argument('--frequency-cubes',action='store_true')
    p.add_argument('--uniform-profiles',action='store_true')
    p.add_argument('--two-step-cuts',action='store_true')
    p.add_argument('--two-step-balls',action='store_true')
    p.add_argument('--lazy-cycles',action='store_true')
    p.add_argument('--face-connectivity',action='store_true')
    p.add_argument('--projection-connectivity',action='store_true')
    p.add_argument('--q4-population',action='store_true')
    p.add_argument('--short-cycles',type=int,choices=(2,3,4),default=0)
    p.add_argument('--q4-tilings',action='store_true')
    p.add_argument('--q4-tiling-connectivity',action='store_true')
    a = p.parse_args()
    if (a.frequency_cubes or a.uniform_profiles) and a.distance != 9:
        p.error('frequency partitions require antipodal endpoints (distance 9)')
    if a.frequency_cubes and a.uniform_profiles:
        p.error('choose one frequency partition')
    if a.lazy_cycles and (a.prefix_cuts or a.axis_windows or a.short_axis_windows
                          or a.long_axis_windows or a.frequency_cubes or a.uniform_profiles):
        p.error('lazy cycle separation requires no rank windows or frequency partition')
    capacity = None
    if a.capacity_table:
        from q9_colour_three_axis import capacity_table
        capacity = capacity_table(a.capacity_table)
    distances = None
    if a.port_distance_table:
        distances = {json.loads(line)['port_distance'] for line in a.port_distance_table.read_text().splitlines()}
        assert distances and distances <= set(range(1,7))
    geometry_cuts = ()
    if a.geometric_library:
        from q9_geometry_cut_library import oriented_library
        geometry_cuts = oriented_library(a.geometric_library)
    sizes = []
    if a.axis_windows:
        sizes.append((27,7,14))
    if a.short_axis_windows:
        sizes.extend(((8,5,16),(14,6,14)))
    if a.long_axis_windows:
        sizes.extend(((51,8,17),(99,9,22)))
    windows = []
    for span,minimum,stride in sizes:
        last = 221-span
        for start in sorted(set(range(0,last+1,stride))|{last}):
            windows.append((start,start+span,minimum))
    search(a.distance,a.budget,a.checker,a.stem,a.ledger,capacity,distances,geometry_cuts,a.compact_patterns,a.prefix_cuts,a.column_cuts,windows,a.count_lex,a.q7_caps,a.q7_contacts,a.frequency_cubes,a.uniform_profiles,a.two_step_cuts,a.two_step_balls,a.lazy_cycles,a.face_connectivity,a.projection_connectivity,a.q4_population,a.short_cycles,a.q4_tilings,a.q4_tiling_connectivity)

