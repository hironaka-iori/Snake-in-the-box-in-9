"""Degree-exact compact selector with lazy cycle separation for Q9."""

import argparse
import json
from pathlib import Path

from pysat.formula import CNF, IDPool

from q9_221_global_interface_cuts import addition
from q9_221_use_verified_profiles import exclude_profiles, add_triple_floors
from q9_direction_frequency import add_frequencies
from q9_lazy_colour_cycles import solve_relaxation
from q9_overlapping_cross18 import value_literals
from q9_q4_forest_diagram import add_tiled_forests, DEFAULT_TILINGS
from q9_square_census import add_popcount
from q9_two_step_availability import add_exact_degrees


def build_compact(length,distance,profiles=(),ordered=True,long_q5_cycles=False):
    end = (1 << distance)-1
    formula = CNF()
    formula.extend([[1],[end+1]])
    pool = IDPool(start_from=513)
    for colour in (0,1):
        population = add_popcount(formula,pool,[[u+1 for u in range(512) if u.bit_count()%2==colour]])
        formula.extend([[lit] for lit in value_literals(population,(length+2-colour)//2)])
    add_exact_degrees(formula,pool,9,(0,end))
    counts,bonds = add_frequencies(formula,pool,9,length,distance,ordered=ordered)
    total = addition(formula,pool,*counts)
    formula.extend([[lit] for lit in value_literals(total,length)])
    if profiles:
        assert length==221
        exclude_profiles(formula,counts,distance,profiles,ordered=ordered)
        add_triple_floors(formula,counts,distance,profiles,ordered=ordered)
    # The floors allocate auxiliary variables in a separate pool.
    pool = IDPool(start_from=formula.nv+1)
    add_tiled_forests(formula,pool,bonds,DEFAULT_TILINGS[:2])
    if long_q5_cycles:
        from q9_q5_long_cycle_diagram import add_long_cycle_tilings
        add_long_cycle_tilings(formula,pool)
    return formula,end


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("distance",type=int,choices=(3,5,7,9))
    parser.add_argument("budget",type=int)
    parser.add_argument("checker")
    parser.add_argument("stem",type=Path)
    parser.add_argument("ledger",type=Path)
    parser.add_argument('--long-q5-cycles',action='store_true')
    args=parser.parse_args()
    profiles=json.loads(args.ledger.read_text())
    formula,end=build_compact(221,args.distance,profiles,long_q5_cycles=args.long_q5_cycles)
    header=dict(distance=args.distance,budget=args.budget,clauses=len(formula.clauses),
                literals=sum(map(len,formula.clauses)),variables=formula.nv,
                selected=222,long_q5_cycles=args.long_q5_cycles,verified_frequency_cuts=len(profiles))
    print(json.dumps(dict(status="STARTED",**header)),flush=True)
    solve_relaxation(formula,end,header,args.stem,args.checker)
