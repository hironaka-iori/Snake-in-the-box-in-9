"""Check full-graph 9,9,10 proofs by rebuilding their pinned-layout formulas."""
import argparse
import gzip
import json
import re
from itertools import islice
from pathlib import Path

from pysat.formula import IDPool

from q6_star_interfaces import check
from q9_certify_geometric_joins import domain_graph, pin_domains, prune_interface_domains
from q9_join_interface_masks import Catalogue
from q9_dense_pair_full_lift import pin_pair, table, wanted_pairs
from q9_three_tight_anchored_lift import form
from q9_three_tight_pairs import BONDS
from q9_three_tight_star_refine import anchor_list
from verify_q9_free_dimension_cuts import deg, parts


INDEX_PREFIX = re.compile(r'^\{\s*"index"\s*:\s*(\d+)\s*,')


def replay(archive,profiles,data,checker,legacy,indices=None,prefix_records=None,allowed=None,*,antipodal=False,distance_seven=False,distance_five=False,distance_three=False):
    checked_status, done_status = 'VERIFIED_FULL_Q9', 'REPLAY_DONE'
    if antipodal:
        checked_status, done_status = 'VERIFIED_ANTIPODAL_Q9', 'ANTIPODAL_REPLAY_DONE'
    if distance_seven:
        checked_status, done_status = 'VERIFIED_D7_Q9', 'D7_REPLAY_DONE'
    if distance_five:
        checked_status, done_status = 'VERIFIED_D5_Q9', 'D5_REPLAY_DONE'
    if distance_three:
        checked_status, done_status = 'VERIFIED_D3_Q9', 'D3_REPLAY_DONE'
    verified = set()
    tested = set()
    catalogue = None
    with gzip.open(archive,'rt') as source:
        rows = source if prefix_records is None else islice(source,prefix_records)
        for line in rows:
            if indices is not None:
                match = INDEX_PREFIX.match(line)
                if match and int(match.group(1)) not in indices:
                    continue
            rec = json.loads(line)
            i = rec['index']
            if indices is not None and i not in indices:
                continue
            assert i not in tested and (allowed is None or i in allowed)
            assert rec.get('antipodal', False) == antipodal
            assert rec.get('distance_seven', False) == distance_seven
            assert rec.get('distance_five', False) == distance_five
            assert rec.get('distance_three', False) == distance_three
            tested.add(i)
            e,c,crossings = row = profiles[i]
            layers = tuple(rec['layers'])
            layouts = ()
            domains = None
            if "domain_limit" in rec:
                if rec['status'] != 'UNSAT_DRAT_VERIFIED':
                    continue
                assert not legacy and len(layers)>=2 and not rec['key']
                assert len(set(layers))==len(layers) and set(layers)<=set(range(8))
                if catalogue is None:
                    catalogue = Catalogue(data)
                domains = domain_graph(row,set(layers),catalogue,rec["domain_limit"])
                if rec.get("arc_consistency", False):
                    prune_interface_domains(row, catalogue, domains)
                assert sum(map(len,domains.values()))==rec['layout_count']
            elif len(layers)==2:
                a,b = layers
                n = crossings[BONDS.index(tuple(sorted(layers)))]
                key = (e[a],c[a],e[b],c[b],n)
                assert n>0 and tuple(rec['key'])==key and data[key]
                layouts = data[key]
            elif len(layers)==1:
                assert not legacy
                a, = layers
                assert 0<=a<8 and (e[a] in (25,26) or (e[a],c[a])==(24,4))
                assert tuple(rec['key'])==(e[a],c[a])
                layouts = [(mask,) for mask in anchor_list(c[a],e[a])]
                assert layouts
            else:
                assert not layers and not rec['key'] and not legacy
            if domains is None:
                assert len(layouts)==rec['layout_count']
            if rec['status']!='UNSAT_DRAT_VERIFIED':
                continue
            f = form(row,rec.get('saturated',False),rec.get('balanced',False),
                     rec.get('layer_colour_balance',False),antipodal=antipodal,
                     distance_seven=distance_seven,distance_five=distance_five,
                     distance_three=distance_three)
            if legacy:
                choices = []
                for left,right in sorted(data[key]):
                    x = f.nv+1
                    choices.append(x)
                    f.append([x,-x])
                    for layer,mask in ((a,left),(b,right)):
                        f.extend([[-x,64*layer+u+1 if mask>>u&1 else -64*layer-u-1] for u in range(64)])
                f.append(choices)
            elif domains is not None:
                pin_domains(f,IDPool(start_from=f.nv+1),domains)
            elif layouts:
                pin_pair(f,layers,layouts)
            extra = f.nv+1
            f.extend([[extra],[extra]])
            for cycle in rec['cycles']:
                v = set(cycle)
                assert len(v)==len(cycle) and all(0<=u<512 for u in v)
                assert len(parts(v,9))==1 and all(deg(v,u,9)==2 for u in v)
                f.append([-u-1 for u in cycle])
            check(f,rec['proof'],checker)
            verified.add(i)
            print(json.dumps(dict(status=checked_status,index=i,layout_count=rec['layout_count'])),flush=True)
    if indices is not None:
        assert tested==indices
    print(json.dumps(dict(status=done_status,tested=len(tested),verified=len(verified),
                          unresolved=sorted(tested-verified))),flush=True)


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('profiles',type=Path)
    p.add_argument('table',type=Path)
    p.add_argument('archive',type=Path)
    p.add_argument('checker')
    p.add_argument('--legacy-tautologies',action='store_true')
    endpoint_scope = p.add_mutually_exclusive_group()
    endpoint_scope.add_argument('--antipodal',action='store_true')
    endpoint_scope.add_argument('--distance-seven',action='store_true')
    endpoint_scope.add_argument('--distance-five',action='store_true')
    endpoint_scope.add_argument('--distance-three',action='store_true')
    p.add_argument('--selection',type=Path,help='Use only seam types for these profiles')
    p.add_argument('--indices',nargs='+',type=int)
    p.add_argument('--prefix-records',type=int,help='number of complete records in a live archive')
    a = p.parse_args()
    if a.prefix_records is not None and (a.prefix_records<1 or a.indices is None):
        p.error('--prefix-records requires a positive count and explicit --indices')
    profiles=json.loads(a.profiles.read_text())['representatives']
    selected=None
    if a.selection:
        report=json.loads(a.selection.read_text())
        assert report['status']=='VERIFIED'
        selected=set(report['indices'])
        assert len(selected)==len(report['indices'])
    requested = None if a.indices is None else set(a.indices)
    lookup_indices = selected if requested is None else requested
    relevant = None if lookup_indices is None else wanted_pairs(profiles,lookup_indices)
    replay(a.archive,profiles,table(a.table,relevant),a.checker,a.legacy_tautologies,
           requested,a.prefix_records,selected,antipodal=a.antipodal,
           distance_seven=a.distance_seven,distance_five=a.distance_five,
           distance_three=a.distance_three)

