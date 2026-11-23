"""Screen exhaustive three-direction count representatives with colour interfaces."""
import argparse
import json
from pathlib import Path

from pysat.solvers import Cadical195

from q9_221_global_interface_cuts import load_cuts
from q9_colour_three_axis import capacity_table, colour_formula, interface_table, unary_exact
from q9_three_axis_profiles import formula
from q9_three_tight_pairs import BONDS


def pinned(edges,components,cross,row):
    return [lit for bank,values in zip((edges,components,[cross[b] for b in BONDS]),row)
            for unary,value in zip(bank,values) for lit in unary_exact(unary,value)]


def scan(counts,path,capacities,interfaces,result,interfaces24=None):
    source = json.loads(path.read_text())
    rows = source['representatives']
    end = sum((count%2)<<i for i,count in enumerate(counts))
    plain,*a = formula(counts,end,*load_cuts())
    coloured,*b = colour_formula(counts,end,capacity_table(capacities),interface_table(interfaces),interfaces24)
    accepted,colour_reject = [],[]
    with Cadical195(bootstrap_with=plain) as p, Cadical195(bootstrap_with=coloured) as c:
        for i,row in enumerate(rows):
            if not p.solve(assumptions=pinned(*a,row)):
                continue
            if c.solve(assumptions=pinned(*b,row)):
                accepted.append(i)
            else:
                colour_reject.append(i)
    result.write_text(json.dumps(dict(counts=counts,source_orbits=len(rows),
                                      base_survivors=len(accepted)+len(colour_reject),
                                      colour_survivors=accepted,colour_rejected=colour_reject))+'\n')
    print(json.dumps(dict(source=len(rows),after_base=len(accepted)+len(colour_reject),
                          after_colour=len(accepted))),flush=True)


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('counts',type=int,nargs=3)
    p.add_argument('input',type=Path)
    p.add_argument('capacities',type=Path)
    p.add_argument('interfaces',type=Path)
    p.add_argument('output',type=Path)
    p.add_argument('--interfaces24',type=Path)
    p.add_argument('--interfaces24-summary',type=Path)
    a = p.parse_args()
    sig24 = None
    if a.interfaces24:
        assert a.interfaces24_summary
        from q9_dense_pair_full_lift import table
        rows = table(a.interfaces24)[(24,4,24,4,3)]
        def black(mask):
            return sum(u.bit_count()%2==0 and bool(mask>>u&1) for u in range(64))
        signatures = {(4,4,black(a),black(b),black(a&b),3-black(a&b)) for a,b in rows}
        # Anchoring the first mask removes translations that exchange both colours.
        reflected = {(c,d,28-p,28-q,white,black_count)
                     for c,d,p,q,black_count,white in signatures}
        sig24 = sorted(signatures|reflected)
        summary = [json.loads(line) for line in a.interfaces24_summary.read_text().splitlines()]
        assert summary[0]['placements']==289**2*720*64
        assert sig24==sorted(tuple(row['key']) for row in summary[1:])
    scan(tuple(a.counts),a.input,a.capacities,a.interfaces,a.output,sig24)

