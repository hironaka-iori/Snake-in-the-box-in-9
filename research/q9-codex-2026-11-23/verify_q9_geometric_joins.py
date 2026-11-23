"""Rebuild and replay exact local geometry certificates before using exclusions."""
import argparse
import gzip
import json
from pathlib import Path

from q6_star_interfaces import check
from q9_certify_geometric_joins import make
from q9_join_interface_masks import Catalogue
from verify_q9_free_dimension_cuts import deg, parts


def review(args):
    bank = json.loads(args.profiles.read_text())['representatives']
    selection = json.loads(args.selection.read_text())
    keep = set(selection['indices'])
    catalogue = Catalogue(args.table)
    colours = None
    looked = set()
    excluded = set()
    with gzip.open(args.archive,'rt') as archive:
        for line in archive:
            row = json.loads(line)
            i = row['index']
            assert i in keep and i not in looked
            looked.add(i)
            if row['status']!='UNSAT_DRAT_VERIFIED':
                continue
            layers = set(row['layers'])
            assert layers and layers<=set(range(8))
            if row.get('completion_colours') and colours is None:
                from q9_exact_interface_colour_screen import colour_signatures
                colours = colour_signatures(args.table)
            f,n = make(bank[i],layers,catalogue,args.limit,completion_ports=row.get('completion_ports',False),
                       interface_colours=colours if row.get('completion_colours') else None)
            assert n==row['layouts']
            for cycle in row['cycles']:
                s = set(cycle)
                assert len(s)==len(cycle) and all(u>>6 in layers for u in s)
                assert len(parts(s,9))==1 and all(deg(s,u,9)==2 for u in s)
                f.append([-u-1 for u in cycle])
            check(f,row['proof'],args.checker)
            excluded.add(i)
    result=dict(status='VERIFIED_GEOMETRIC',counts=selection['counts'],
                base=len(keep),checked=len(looked),excluded=sorted(excluded),
                indices=sorted(keep-excluded))
    args.output.write_text(json.dumps(result)+'\n')
    print(json.dumps(dict(status=result['status'],counts=result['counts'],base=len(keep),
                          excluded=len(excluded),remaining=len(keep-excluded))),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('profiles',type=Path)
    p.add_argument('selection',type=Path)
    p.add_argument('table',type=Path)
    p.add_argument('archive',type=Path)
    p.add_argument('checker')
    p.add_argument('output',type=Path)
    p.add_argument('--limit',type=int,default=12000)
    review(p.parse_args())

