"""Native cardinality search for the 221-edge path, with CNF proof replay."""

import argparse
import json
from math import comb
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Minicard

from q9_221_use_verified_profiles import add_triple_floors, exclude_profiles
from q9_direction_frequency import add_frequencies, append_order
from q9_endpoint_distance_bound import read_path
from q9_lazy_colour_cycles import cycle_components
from q9_q4_population import q4_populations
from q9_tight_interface_search import certify


def add_hamming_cut_parity(formula, pool, dim, length, end, physical, limits):
    """Degree parity across concentric Hamming balls around the endpoints."""
    volume_by_fixed_weight = [comb(dim-4,i) for i in range(dim-3)]
    for center, other in ((0,end),(end,0)):
        borders = [[] for _ in range(dim)]
        for u,v,bond in physical:
            radius = min((u^center).bit_count(),(v^center).bit_count())
            borders[radius].append(bond)
        for radius,bonds in enumerate(borders):
            odd = (center^other).bit_count()>radius
            parity = bonds[0]
            for bond in bonds[1:]:
                different = pool.id()
                formula.extend([
                    [parity,bond,-different], [-parity,-bond,-different],
                    [parity,-bond,different], [-parity,bond,different],
                ])
                parity = different
            formula.append([parity if odd else -parity])
            if odd:
                continue
            # Partition into Q4 subcubes and cap each intersection by eight.
            capacity = sum(
                amount * min(8,sum(comb(4,j) for j in range(min(4,radius-i)+1)))
                for i,amount in enumerate(volume_by_fixed_weight)
            )
            if capacity < length+1:
                limits.append(([-bond for bond in bonds],len(bonds)-2))


def add_ball_occupancy(limits):
    """Use complementary Hamming balls and exact Q4 forest capacities."""
    from q9_q4_forest_diagram import forest_masks

    masks = forest_masks()
    radius_five_capacity = 0
    radius_four_opposite_capacity = 0
    for weight in range(6):
        radius_five = sum(1<<v for v in range(16) if weight+v.bit_count()<=5)
        opposite = sum(
            1<<v for v in range(16)
            if weight+v.bit_count()<=4 and (weight+v.bit_count())%2
        )
        radius_five_capacity += comb(5,weight)*max((m&radius_five).bit_count() for m in masks)
        radius_four_opposite_capacity += comb(5,weight)*max((m&opposite).bit_count() for m in masks)
    minimum_in_radius_three = 222-radius_five_capacity
    minimum_same_colour = 111-radius_four_opposite_capacity
    for center in range(512):
        ball_three = [-(v+1) for v in range(512) if (v^center).bit_count()<=3]
        even_four = [-(v+1) for v in range(512) if (v^center).bit_count() in (0,2,4)]
        limits.append((ball_three,len(ball_three)-minimum_in_radius_three))
        limits.append((even_four,len(even_four)-minimum_same_colour))


def q8_vertex_cap(components):
    """Bound a Q8 forest by splitting along a least-used direction."""
    from verify_q9_free_dimension_cuts import edge7

    if not components:
        return 0
    if components == 1:
        return 99
    for edges in range(128-components,-1,-1):
        for crossings in range(edges//8+1):
            min_parts = (crossings+1)//2
            total_parts = components+crossings
            if any(
                edges-crossings <= edge7(a)+edge7(total_parts-a)
                for a in range(min_parts,total_parts-min_parts+1)
            ):
                return edges+components
    raise AssertionError("no possible Q8 forest")


def terminal_half_caps(crossings, parity, first, last, best):
    """Population bounds after removing terminals isolated inside their Q8 half."""
    on_first_half = first + (last if parity == 0 else 0)
    on_second_half = last if parity else 0
    c0 = crossings // 2 + 1
    c1 = (crossings + 1) // 2
    assert c0 >= on_first_half and c1 >= on_second_half
    return (min(128, best[c0-on_first_half]+on_first_half),
            min(128, best[c1-on_second_half]+on_second_half))


def add_q8_layer_caps(formula, counts, distance, terminal_isolates=False):
    """Link each direction frequency to both complementary Q8 populations."""
    from q9_direction_frequency import append_upper_bound
    from q9_overlapping_cross18 import value_literals
    from q9_square_census import add_popcount

    pool = IDPool(start_from=formula.nv+1)
    best = [q8_vertex_cap(c) for c in range(39)]
    for axis,frequency in enumerate(counts):
        first_half = [v+1 for v in range(512) if not v&(1<<axis)]
        pop = add_popcount(formula,pool,[first_half])
        append_upper_bound(formula,pop,128)
        inverted = [-bit for bit in pop]
        append_upper_bound(formula,inverted,(1<<len(pop))-1-94)
        parity = int(axis<distance)
        for crossings in range(4-parity,75,2):
            first = crossings//2+1
            second = (crossings+1)//2
            guard = [-lit for lit in value_literals(frequency,crossings)]
            if best[first]!=128 or best[second]!=128:
                append_upper_bound(formula,pop,best[first],guard)
                # n0 >= 222-cap1, so the bitwise complement of n0 is bounded above.
                append_upper_bound(formula,inverted,(1<<len(pop))-1-222+best[second],guard)
            if not terminal_isolates:
                continue
            end = (1 << distance)-1
            step = 1 << axis
            for at_start, at_end in ((1,0),(0,1),(1,1)):
                a,b = terminal_half_caps(crossings,parity,at_start,at_end,best)
                terminal_guard = guard.copy()
                if at_start:
                    terminal_guard.append(-step-1)
                if at_end:
                    terminal_guard.append(-(end ^ step)-1)
                if a+b<222:
                    formula.append(terminal_guard)
                else:
                    if a<best[first]:
                        append_upper_bound(formula,pop,a,terminal_guard)
                    if b<best[second]:
                        append_upper_bound(formula,inverted,(1<<len(pop))-1-222+b,terminal_guard)


def q6_capacity_evidence(path):
    """Check the independently reproduced finite Q5-to-Q6 join output."""
    from verify_q9_free_dimension_cuts import deg, parts

    rows = {}
    for line in path.read_text().splitlines():
        tokens = line.split()
        if tokens[:1] != ["edge_target"]:
            continue
        assert tokens[2::2] == ["minimum_population","tested","found","witness"]
        key = int(tokens[1]),int(tokens[3])
        assert key not in rows
        rows[key] = int(tokens[5]),int(tokens[7]),int(tokens[9],16)
    assert set(rows) == {(26,0),(27,0),(25,29),(26,29)}
    for key in ((27,0),(25,29),(26,29)):
        pairs,found,witness = rows[key]
        assert pairs > 0 and found == witness == 0
    count,found,mask = rows[26,0]
    assert count>0 and found==1 and 0<mask<1<<64
    selected = {v for v in range(64) if mask>>v&1}
    component_sets = parts(selected,6)
    assert all(deg(selected,v,6)<=2 for v in selected)
    assert sum(deg(selected,v,6) for v in selected)==52
    assert len(selected)-len(component_sets)==26


def add_q6_edge_caps(formula,limits,physical,dim):
    from itertools import combinations

    banks={(a,b):value for a,b,value in physical}
    pool=IDPool(start_from=max(formula.nv,max(abs(lit) for bank,_ in limits for lit in bank))+1)
    for axes in combinations(range(dim),6):
        free=sum(1<<axis for axis in axes)
        faces={}
        for u in range(1<<dim):
            points,edges=faces.setdefault(u&~free,([],[]))
            points.append(u+1)
            for axis in axes:
                v=u^(1<<axis)
                if v>u:
                    edges.append(banks[u,v])
        for points,edges in faces.values():
            high=pool.id()
            positive=pool.id()
            negative=[pool.id() for _ in range(3)]
            formula.extend([[-high,positive],[high,-positive]])
            for bit in negative:
                formula.extend([[high,bit],[-high,-bit]])
            # Four Q4 faces give at most 32 vertices in this Q6.
            limits.append((points+[-high]+negative,32))
            limits.append((edges+[high,positive],26))


def add_d3_terminal_types(formula, dim, end, count):
    """A reversal-symmetric split by how the path leaves either end."""
    assert end.bit_count() == 3 and count in (0, 1, 2)
    first_differs = count >= 1
    last_differs = count == 2
    for axis in range(dim):
        mask = 1 << axis
        differs = bool(end & mask)
        if differs != first_differs:
            formula.append([-mask - 1])
        if differs != last_differs:
            formula.append([-(end ^ mask) - 1])
    if count == 2:
        # Different departure coordinates make the two internal neighbors
        # adjacent, giving a chord in an induced path of more than three edges.
        for axis in range(dim):
            mask = 1 << axis
            if end & mask:
                a, b = mask + 1, (end ^ mask) + 1
                formula.extend([[-a, b], [a, -b]])


def add_d3_same_terminal_axis(formula, pool, end, counts=None, crossings=None):
    """Require both terminal edges to use one shared nondiffering axis."""
    from q9_overlapping_cross18 import value_literals

    assert end == 7
    choices = []
    for axis in range(3,9):
        signal = pool.id()
        step = 1 << axis
        formula.extend([[-signal,step+1],[-signal,(end^step)+1]])
        if crossings is not None:
            formula.extend([-signal,lit] for lit in value_literals(counts[axis],crossings))
        choices.append(signal)
    formula.append(choices)


def build_native(dim,length,distance,ledger=(),hamming_cuts=False,ball_occupancy=False,
                 minimum_profile=None,minimum_triple_sum=None,q8_layer_caps=False,
                 two_axis_population=False,two_axis_contacts=False,geometry_cuts=(),
                 q5_edge_caps=False,q6_edge_caps=False,folded_caps=False,folded_topology=False,
                 root_face_size=None,endpoint_face_population=None,phase_bits=None,
                 q5_colour_caps=False,endpoint_separation=False,d3_terminal_types=None,terminal_rank_windows=False,monotone_seams=(),monotone_stars=(),extra_seam_triples=(),required_projection_rows=None,d3_same_terminal_axis=False,terminal_q8_caps=False,d3_shared_axis_crossings=None,q7_terminal_caps=False,exact_direction_total=False,d3_spanning_mask=None):
    n = 1 << dim
    end = (1 << distance)-1
    formula = CNF()
    pool = IDPool(start_from=n+1)
    formula.extend([[1],[end+1]])
    limits = []
    for colour in (0,1):
        vertices = [v+1 for v in range(n) if v.bit_count()%2==colour]
        target = (length+2-colour)//2
        limits.append((vertices,target))
        limits.append(([-v for v in vertices],len(vertices)-target))
    for vertex in range(n):
        selected = vertex+1
        target = 1 if vertex in (0,end) else 2
        neighbors = [(vertex^(1<<axis))+1 for axis in range(dim)]
        guards = [selected]
        for _ in range(max(dim-target,target)-1):
            equivalent = pool.id()
            formula.extend([[-selected,equivalent],[-equivalent,selected]])
            guards.append(equivalent)
        limits.append((neighbors+guards[:dim-target],dim))
        limits.append(([-v for v in neighbors]+guards[:target],dim))
    face_case = any(value is not None for value in (root_face_size,endpoint_face_population,d3_spanning_mask))
    counts,physical = add_frequencies(formula,pool,dim,length,distance,ordered=not face_case)
    if exact_direction_total:
        from q9_221_global_interface_cuts import addition
        from q9_overlapping_cross18 import value_literals

        formula.extend([lit] for lit in value_literals(addition(formula,pool,*counts),length))
    if root_face_size is not None:
        assert (dim,length,distance)==(9,221,9)
        assert minimum_profile is None and minimum_triple_sum is None
        from q9_antipodal_root_face import constrain_root_face

        constrain_root_face(formula,pool,root_face_size)
    if endpoint_face_population is not None:
        assert (dim,length,distance)==(9,221,3) and root_face_size is None
        assert minimum_profile is None and minimum_triple_sum is None
        from q9_endpoint_spanning_face import constrain_spanning_face

        constrain_spanning_face(formula,pool,endpoint_face_population)
    if d3_spanning_mask is not None:
        from q9_endpoint_three_face import constrain

        assert (dim,distance)==(9,3)
        assert root_face_size is None and endpoint_face_population is None and d3_terminal_types is None
        constrain(formula,pool,counts,d3_spanning_mask)
    elif face_case:
        for preceding,following in zip(counts[4:],counts[5:]):
            append_order(formula,pool,preceding,following)
    if d3_terminal_types is not None:
        assert distance == 3 and length > 3
        add_d3_terminal_types(formula,dim,end,d3_terminal_types)
    if d3_same_terminal_axis:
        assert (dim,distance,d3_terminal_types)==(9,3,0)
        add_d3_same_terminal_axis(formula,pool,end,counts,d3_shared_axis_crossings)
    if phase_bits is not None:
        from q9_modular_orientation import add_counted_edge_phase

        add_counted_edge_phase(formula,pool,n,phase_bits,length,end,physical,terminal_rank_windows)
    if endpoint_separation:
        from q9_endpoint_face_separation import add_endpoint_separation

        assert dim == 9
        add_endpoint_separation(formula,pool,physical,end,length+1)
    if hamming_cuts:
        assert dim >= 4
        add_hamming_cut_parity(formula,pool,dim,length,end,physical,limits)
    if ball_occupancy:
        assert (dim,length)==(9,221)
        add_ball_occupancy(limits)
    if ledger:
        assert (dim,length)==(9,221)
        if not face_case or d3_spanning_mask is not None:
            add_triple_floors(formula,counts,distance,ledger,ordered=not face_case)
        exclude_profiles(formula,counts,distance,ledger,ordered=not face_case)
    if q8_layer_caps:
        assert (dim,length)==(9,221)
        add_q8_layer_caps(formula,counts,distance,terminal_isolates=terminal_q8_caps)
    if two_axis_population:
        assert (dim,length,distance)==(9,221,9) and minimum_profile is not None
        from q9_221_two_axis_population import add_fixed_profiles

        add_fixed_profiles(formula,physical,length,minimum_profile,two_axis_contacts)
    if minimum_profile is not None:
        for bits,value in zip(counts[:3],minimum_profile):
            formula.extend([[bit if value>>i&1 else -bit] for i,bit in enumerate(bits)])
    if minimum_triple_sum is not None:
        from q9_221_global_interface_cuts import addition, lower

        extra = IDPool(start_from=formula.nv+1)
        lower(formula,addition(formula,extra,*counts[:3]),minimum_triple_sum)
    if geometry_cuts or monotone_seams or monotone_stars:
        from q9_221_global_interface_cuts import add_geometry,triples_for

        assert dim==9
        standard = triples_for(distance)
        add_geometry(formula,end,standard,geometry_cuts=geometry_cuts,
                     compact_patterns=True,bonds=physical,monotone_seams=monotone_seams,
                     monotone_stars=monotone_stars)
        extra = sorted(set(map(tuple, extra_seam_triples)) - set(standard))
        if extra:
            add_geometry(formula,end,extra,bonds=physical,monotone_seams=monotone_seams,
                         monotone_stars=monotone_stars)
    if q7_terminal_caps:
        from q9_q7_face_caps import add_q7_face_caps

        assert dim==9
        extra=IDPool(start_from=formula.nv+1)
        add_q7_face_caps(formula,extra,physical,end,contact_cuts=True,terminal_isolates=True)
    if required_projection_rows is not None:
        from q9_lift_three_tight_pairs import add_projected_rows

        assert (dim,length,distance)==(9,221,9) and minimum_profile is not None
        add_projected_rows(formula, required_projection_rows)
    limits.extend((points,8) for points in q4_populations(dim))
    if q5_edge_caps:
        from q5_certified_edge_capacity import lift
        lift(dim,physical,formula,limits)
    if q6_edge_caps:
        add_q6_edge_caps(formula,limits,physical,dim)
    if q5_colour_caps:
        from q5_colour_caps import lift

        assert dim == 9
        lift(formula,physical)
    if folded_caps or folded_topology:
        from q9_folded_path_caps import add_folded_caps
        assert dim==9
        add_folded_caps(formula,limits,end,physical if folded_topology else None)
    return formula,limits,end


def cnf_replay_formula(formula,limits):
    result = CNF(from_clauses=formula.clauses)
    pool = IDPool(start_from=max(result.nv,max(abs(v) for row,_ in limits for v in row))+1)
    for row,upper in limits:
        result.extend(CardEnc.atmost(row,upper,vpool=pool,encoding=EncType.seqcounter).clauses)
    return result


def run(distance,budget,checker,stem,ledger,hamming_cuts=False,ball_occupancy=False,
        minimum_profile=None,minimum_triple_sum=None,q8_layer_caps=False,
                 two_axis_population=False,two_axis_contacts=False,geometry_cuts=(),
                 q5_evidence=None,q6_evidence=None,folded_caps=False,folded_topology=False,
        root_face_size=None,endpoint_face_population=None,phase_bits=None,
        q5_colour_evidence=None,endpoint_separation=False,d3_terminal_types=None,terminal_rank_windows=False,monotone_seams=(),monotone_stars=(),extra_seam_triples=(),required_projection_rows=None,d3_same_terminal_axis=False,terminal_q8_caps=False,d3_shared_axis_crossings=None,q7_terminal_caps=False,exact_direction_total=False,d3_spanning_mask=None):
    if q5_evidence:
        from q5_certified_edge_capacity import replay
        replay(q5_evidence,checker)
    if q6_evidence:
        q6_capacity_evidence(q6_evidence)
    if q5_colour_evidence:
        from q5_colour_caps import replay

        replay(q5_colour_evidence,checker)
    formula,limits,end = build_native(9,221,distance,json.loads(ledger.read_text()),hamming_cuts,ball_occupancy,
                                      minimum_profile,minimum_triple_sum,q8_layer_caps,two_axis_population,two_axis_contacts,
                                      geometry_cuts,q5_edge_caps=bool(q5_evidence),q6_edge_caps=bool(q6_evidence),
                                      folded_caps=folded_caps,folded_topology=folded_topology,
                                      root_face_size=root_face_size,endpoint_face_population=endpoint_face_population,
                                      phase_bits=phase_bits,q5_colour_caps=bool(q5_colour_evidence),
                                      endpoint_separation=endpoint_separation,d3_terminal_types=d3_terminal_types,terminal_rank_windows=terminal_rank_windows,monotone_seams=monotone_seams,monotone_stars=monotone_stars,extra_seam_triples=extra_seam_triples,required_projection_rows=required_projection_rows,d3_same_terminal_axis=d3_same_terminal_axis,terminal_q8_caps=terminal_q8_caps,d3_shared_axis_crossings=d3_shared_axis_crossings,q7_terminal_caps=q7_terminal_caps,exact_direction_total=exact_direction_total,d3_spanning_mask=d3_spanning_mask)
    print(json.dumps(dict(status="NATIVE_CARDINALITY_STARTED",distance=distance,
                          budget=budget,clauses=len(formula.clauses),limits=len(limits),hamming_cuts=hamming_cuts,
                          ball_occupancy=ball_occupancy,minimum_profile=minimum_profile,
                          minimum_triple_sum=minimum_triple_sum,q8_layer_caps=q8_layer_caps,
                          two_axis_population=two_axis_population,
                          two_axis_contacts=two_axis_contacts,geometry_patterns=len(geometry_cuts),
                          monotone_seams=monotone_seams,monotone_stars=monotone_stars,
                          extra_seam_triples=extra_seam_triples,
                          d3_same_terminal_axis=d3_same_terminal_axis,terminal_q8_caps=terminal_q8_caps,
                          d3_shared_axis_crossings=d3_shared_axis_crossings,
                          q7_terminal_caps=q7_terminal_caps,exact_direction_total=exact_direction_total,
                          d3_spanning_mask=d3_spanning_mask,
                          required_projection_rows=len(required_projection_rows) if required_projection_rows is not None else None,
                          q5_edge_caps=bool(q5_evidence),q6_edge_caps=bool(q6_evidence),
                          folded_caps=folded_caps or folded_topology,folded_topology=folded_topology,
                          root_face_size=root_face_size,endpoint_face_population=endpoint_face_population,
                                      phase_bits=phase_bits,q5_colour_caps=bool(q5_colour_evidence),
                          endpoint_separation=endpoint_separation,d3_terminal_types=d3_terminal_types,terminal_rank_windows=terminal_rank_windows)),flush=True)
    cycles=[]
    status="UNKNOWN"
    with Minicard(bootstrap_with=formula) as solver:
        for row,upper in limits:
            solver.add_atmost(row,upper)
        while (left:=budget-solver.accum_stats()["conflicts"])>0:
            solver.conf_budget(left)
            answer=solver.solve_limited()
            if answer is None:
                break
            if answer is False:
                print(json.dumps(dict(status="NATIVE_UNSAT_REPLAY_STARTED",cycles=len(cycles))),flush=True)
                status=certify(cnf_replay_formula(formula,limits),[end+1],stem,checker)
                break
            model=solver.get_model()
            selected={u-1 for u in model if 1<=u<=512}
            assert len(selected)==222
            detached=cycle_components(selected,9,(0,end))
            if not detached:
                path=read_path(model,9,221,end)
                stem.with_suffix(".path").write_text(" ".join(map(str,path))+"\n")
                status="SAT_PATH_VERIFIED"
                break
            for loop in detached:
                assert loop not in cycles
                cycles.append(loop)
                clause=[-u-1 for u in loop]
                formula.append(clause)
                solver.add_clause(clause)
            print(json.dumps(dict(status="CYCLE_CUTS",new=len(detached),total=len(cycles),
                                  lengths=list(map(len,detached)))),flush=True)
        conflicts=solver.accum_stats()["conflicts"]
    if cycles:
        stem.with_suffix(".cycles.json").write_text(json.dumps(cycles)+"\n")
    print(json.dumps(dict(status=status,distance=distance,conflicts=conflicts,
                          cycle_cuts=len(cycles))),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("distance",type=int,choices=(3,5,7,9))
    parser.add_argument("budget",type=int)
    parser.add_argument("checker")
    parser.add_argument("stem",type=Path)
    parser.add_argument("ledger",type=Path)
    parser.add_argument("--hamming-cuts",action="store_true")
    parser.add_argument("--ball-occupancy",action="store_true")

    split=parser.add_mutually_exclusive_group()
    split.add_argument("--minimum-profile",type=int,nargs=3)
    split.add_argument("--minimum-triple-sum",type=int)
    split.add_argument("--root-face-size",type=int,choices=range(2,9))
    split.add_argument("--endpoint-face-population",type=int,choices=range(2,9))
    parser.add_argument("--q8-layer-caps",action="store_true")
    parser.add_argument("--terminal-q8-caps",action="store_true")
    parser.add_argument("--q7-terminal-caps",action="store_true")
    parser.add_argument("--exact-direction-total",action="store_true")
    parser.add_argument("--two-axis-population",action="store_true")
    parser.add_argument("--two-axis-contacts",action="store_true")
    parser.add_argument("--geometric-library",type=Path)
    parser.add_argument("--monotone-seams",type=Path,
                        help="Independently replayed Q6 seam-rule manifest")
    parser.add_argument("--monotone-stars",type=Path,
                        help="Independently replayed multiple-seam rule manifest")
    parser.add_argument("--extra-seam-triple",type=int,nargs=3,action="append",default=[],
                        choices=range(9),help="An extra projection for certified seam rules")
    parser.add_argument("--required-projection",type=Path,
                        help="Immutable selection of surviving canonical projections")
    parser.add_argument("--q5-edge-caps",type=Path)
    parser.add_argument("--q5-colour-caps",type=Path)
    parser.add_argument("--q6-edge-caps-log",type=Path)
    parser.add_argument("--folded-caps",action="store_true")
    parser.add_argument("--folded-topology",action="store_true")
    parser.add_argument("--phase-bits",type=int,choices=range(1,8))
    parser.add_argument("--endpoint-separation",action="store_true")
    from q9_endpoint_three_face import MASKS
    parser.add_argument("--d3-spanning-mask",type=int,choices=MASKS)
    parser.add_argument("--d3-terminal-types",type=int,choices=(0,1,2))
    parser.add_argument("--d3-same-terminal-axis",action="store_true")
    parser.add_argument("--d3-shared-axis-crossings",type=int,choices=range(4,75,2))
    parser.add_argument("--terminal-rank-windows",action="store_true")
    a=parser.parse_args()
    if a.terminal_rank_windows and a.phase_bits!=7:
        parser.error("Terminal rank windows require the complete seven-bit phase.")
    if a.d3_terminal_types is not None and a.distance!=3:
        parser.error("Terminal step partition requires distance-three endpoints.")
    if any(value is not None for value in (a.minimum_profile,a.minimum_triple_sum,a.root_face_size)) and a.distance!=9:
        parser.error("The three-axis split requires antipodal endpoints.")
    if a.endpoint_face_population is not None and a.distance!=3:
        parser.error("The endpoint face requires distance-three endpoints.")
    if a.two_axis_contacts and not a.two_axis_population:
        parser.error("Contact bounds require --two-axis-population.")
    if a.two_axis_population and a.minimum_profile is None:
        parser.error("The two-axis bounds need a fixed minimum profile.")
    geometry_cuts = ()
    if a.geometric_library:
        from q9_geometry_cut_library import oriented_library
        geometry_cuts = oriented_library(a.geometric_library,json.loads(a.ledger.read_text()))
    monotone_seams = ()
    if a.monotone_seams:
        report = json.loads(a.monotone_seams.read_text())
        if report["status"] != "VERIFIED" or not report["anchor_certificates"]:
            parser.error("Expected a verified seam-rule manifest.")
        monotone_seams = report["rules"]
    monotone_stars = ()
    if a.monotone_stars:
        from q9_screen_monotone_seams import verified_star_rules
        checked = verified_star_rules([a.monotone_stars])
        monotone_stars = sorted((e,c,shape) for (e,c), shapes in checked.items() for shape in shapes)
    if a.extra_seam_triple and not (monotone_seams or monotone_stars):
        parser.error("Extra seam triples require certified seam rules.")
    if any(len(set(triple))!=3 for triple in a.extra_seam_triple):
        parser.error("Projection coordinates must be distinct.")
    extra = sorted({tuple(sorted(triple)) for triple in a.extra_seam_triple})
    required_rows = None
    if a.required_projection:
        data = json.loads(a.required_projection.read_text())
        if a.distance != 9 or not a.minimum_profile or data["counts"] != a.minimum_profile:
            parser.error("Projection evidence must match the fixed antipodal frequency profile.")
        if data["status"] != "VERIFIED_PROJECTION_SELECTION" or not data["rows"]:
            parser.error("Expected a nonempty audited projection selection.")
        required_rows = data["rows"]
    if a.d3_same_terminal_axis and (a.distance!=3 or a.d3_terminal_types!=0):
        parser.error("The same-axis split requires distance-three terminals of type zero.")
    if a.d3_shared_axis_crossings is not None and not a.d3_same_terminal_axis:
        parser.error("A fixed shared-axis count requires the same terminal axis.")
    if a.terminal_q8_caps and not a.q8_layer_caps:
        parser.error("Terminal Q8 caps require the Q8 layer caps.")
    if a.d3_spanning_mask is not None and (a.distance!=3 or a.endpoint_face_population is not None or a.d3_terminal_types is not None):
        parser.error("Q3 mask pinning requires distance three without another terminal-face normalization.")
    run(a.distance,a.budget,a.checker,a.stem,a.ledger,a.hamming_cuts,a.ball_occupancy,
        a.minimum_profile,a.minimum_triple_sum,a.q8_layer_caps,a.two_axis_population,a.two_axis_contacts,
        geometry_cuts,a.q5_edge_caps,a.q6_edge_caps_log,a.folded_caps,a.folded_topology,a.root_face_size,a.endpoint_face_population,a.phase_bits,a.q5_colour_caps,a.endpoint_separation,a.d3_terminal_types,a.terminal_rank_windows,monotone_seams,monotone_stars,extra,required_rows,a.d3_same_terminal_axis,a.terminal_q8_caps,a.d3_shared_axis_crossings,a.q7_terminal_caps,a.exact_direction_total,a.d3_spanning_mask)
