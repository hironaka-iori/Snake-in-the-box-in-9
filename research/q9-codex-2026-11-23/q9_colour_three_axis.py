"""Colour-resolved restrictions for the three-coordinate projection of a Q9 path."""
import argparse
import json
import subprocess
from math import comb
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q6_exact_anchored_profiles import catalogue
from q9_221_global_interface_cuts import load_cuts
from q9_lift_three_tight_pairs import ROOT
from q9_three_axis_profiles import formula
from verify_q9_free_dimension_cuts import deg, parts


def catalogue_balances():
    tables = {}
    for e,name,limit in ((25,'q6_25_edge_catalogue.log',3),
                         (26,'q6_26_edge_interfaces.log',2)):
        for c in range(1,limit+1):
            masks = list(catalogue(ROOT/name,c))
            assert masks
            choices = set()
            for mask in masks:
                pts = {v for v in range(64) if mask>>v&1}
                assert len(pts)==e+c
                assert len(parts(pts,6))==c
                degrees = [deg(pts,v,6) for v in pts]
                assert max(degrees)<=2 and sum(degrees)==2*e
                black = sum(v.bit_count()%2==0 for v in pts)
                choices.update((black,len(pts)-black))
            tables[e,c] = tuple(sorted(choices))
    return tables


def unary_exact(row,n):
    return ([row[n-1]] if n else []) + ([-row[n]] if n<len(row) else [])


def capacity_table(path):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    assert [row['minority'] for row in rows] == list(range(11,17))
    for row in rows:
        assert row['supports'] == comb(30,row['minority']-2)
    return {(e,row['minority']):w for row in rows
            for e,w in enumerate(row['majority_upper_22_23_24'],start=22)}


def interface_table(path):
    records = [json.loads(line) for line in path.read_text().splitlines()]
    header, rows = records[0], records[1:]
    assert header['placements'] == 208**2 * 720 * 64
    assert len(rows) == header['signatures']
    signatures = set()
    for row in rows:
        a,b = [{u for u in range(64) if int(mask,16)>>u&1} for mask in row['masks']]
        union = a|{u|64 for u in b}
        assert max(deg(union,u,7) for u in union)<=2
        assert sum(deg(union,u,7) for u in union)==2*(len(a)+len(b)-len(parts(union,7)))
        assert all(sum(deg(s,u,6) for u in s)==50 for s in (a,b))
        def black(s):
            return sum(u.bit_count()%2==0 for u in s)
        crossing = a&b
        key = (len(a)-25,len(b)-25,black(a),black(b),black(crossing),len(crossing)-black(crossing))
        assert key==tuple(row['key']) and key not in signatures
        signatures.add(key)
    return sorted(signatures)


def colour_formula(counts,end,caps=None,interfaces=None,interfaces24=None):
    exact,stars = load_cuts()
    f,edges,components,crossing = formula(counts,end,exact,stars)
    pool = IDPool(start_from=f.nv+1)

    def unary(n):
        row = [pool.id() for _ in range(n)]
        f.extend([[-b,a] for a,b in zip(row,row[1:])])
        return row

    def sum_eq(positive,negative,offset=0):
        f.extend(CardEnc.equals(positive+[-x for x in negative],len(negative)+offset,
                                vpool=pool,encoding=EncType.cardnetwrk))

    colours = {bond:(unary(len(row)),unary(len(row))) for bond,row in crossing.items()}
    for bond,(black,white) in colours.items():
        sum_eq(black+white,crossing[bond])
    balances = catalogue_balances()
    end_inner_colour = 1-end.bit_count()%2
    black_sizes = []
    for face in range(8):
        black,white = unary(32),unary(32)
        black_sizes.append(black)
        sum_eq(black+white,edges[face]+components[face])
        for colour,vertices in enumerate((black,white)):
            ports = [x for bond,rows in colours.items() if face in bond for x in rows[colour]]
            endpoints = int(face==0 and colour==0)+int(face==end and colour==end_inner_colour)
            duplicate = [pool.id() for _ in vertices]
            f.extend([[-a,b] for a,b in zip(vertices,duplicate)])
            f.extend([[a,-b] for a,b in zip(vertices,duplicate)])
            # 2*V_colour = internal edges + cross edges of this colour + endpoints.
            sum_eq(edges[face]+ports,vertices+duplicate,offset=-endpoints)
        for (e,b),cap in (caps or {}).items():
            minimum_bad = max(b,cap+1)
            for minor,major in ((black,white),(white,black)):
                conditions = unary_exact(edges[face],e)+unary_exact(minor,b)
                conditions.append(major[minimum_bad-1])
                f.append([-x for x in conditions])
        for (e,c),allowed in balances.items():
            if c>len(components[face]):
                continue
            guard = [-x for x in unary_exact(edges[face],e)+unary_exact(components[face],c)]
            choices = []
            for k in allowed:
                chosen = pool.id()
                choices.append(chosen)
                f.extend([[-chosen,x] for x in unary_exact(black,k)])
            f.append([*guard,*choices])
    for edge_count,options in ((25,interfaces),(24,interfaces24)):
        if not options:
            continue
        for (u,v),(rb,rw) in colours.items():
            total = crossing[u,v]
            if edge_count==24 and len(total)<3:
                continue
            banks = (components[u],components[v],black_sizes[u],black_sizes[v],rb,rw)
            choices = []
            for profile in options:
                if any(n>len(row) for n,row in zip(profile,banks)):
                    continue
                chosen = pool.id()
                choices.append(chosen)
                for bank,n in zip(banks,profile):
                    f.extend([[-chosen,x] for x in unary_exact(bank,n)])
            guards = unary_exact(edges[u],edge_count)+unary_exact(edges[v],edge_count)
            if edge_count==24:
                if min(len(components[u]),len(components[v]))<4:
                    continue
                guards += (unary_exact(components[u],4)+unary_exact(components[v],4)
                           +unary_exact(total,3))
            else:
                guards.append(total[0])
            f.append([*(-x for x in guards),*choices])
    return f,edges,components,crossing


def run(input_log,out,checker,budget,caps=None,interfaces=None):
    for line in input_log.read_text().splitlines():
        row = json.loads(line)
        if row['status']!='FEASIBLE_RELAXATION':
            continue
        counts = tuple(row['counts'])
        end = row['end']
        f,edges,components,crossing = colour_formula(counts,end,caps,interfaces)
        pins = [x for rows,values in ((edges,row['edges']),(components,row['components']),
                                    (crossing.values(),row['crossings']))
                for unary,n in zip(rows,values) for x in unary_exact(unary,n)]
        with Cadical195(bootstrap_with=f) as solver:
            pin_ok = solver.solve(assumptions=pins)
        print(json.dumps(dict(status='STARTED',counts=counts,end=end,old_profile_passes=pin_ok,
                              clauses=len(f.clauses))),flush=True)
        with Cadical195(bootstrap_with=f,with_proof=True) as solver:
            solver.conf_budget(budget)
            result = solver.solve_limited()
            status = ('UNKNOWN' if result is None else 'FEASIBLE_COLOUR_RELAXATION')
            proof = None
            if result is False:
                stem = out/('colour_'+'_'.join(map(str,counts)))
                cnf,proof = stem.with_suffix('.cnf'),stem.with_suffix('.drat')
                f.to_file(str(cnf))
                proof.write_text('\n'.join(solver.get_proof())+'\n')
                replay = subprocess.run([checker,str(cnf),str(proof)],check=True,capture_output=True)
                assert b's VERIFIED' in replay.stdout
                status = 'UNSAT_COLOUR_DRAT_VERIFIED'
            print(json.dumps(dict(status=status,counts=counts,end=end,proof=str(proof) if proof else None,
                                  old_profile_passes=pin_ok,conflicts=solver.accum_stats()['conflicts'])),flush=True)


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('input_log',type=Path)
    p.add_argument('out',type=Path)
    p.add_argument('checker')
    p.add_argument('--budget',type=int,default=75000)
    p.add_argument('--capacity-table',type=Path)
    p.add_argument('--interface-table',type=Path)
    a = p.parse_args()
    caps = capacity_table(a.capacity_table) if a.capacity_table else None
    interfaces = interface_table(a.interface_table) if a.interface_table else None
    run(a.input_log,a.out,a.checker,a.budget,caps,interfaces)

