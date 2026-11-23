"""Lift remaining 9,9,10 count profiles with both sides of a dense interface fixed."""
import argparse
from collections import defaultdict
import gzip
import json
from pathlib import Path

from q9_three_tight_anchored_lift import candidate, form, verify
from q9_three_tight_pairs import BONDS
from q9_three_tight_star_refine import anchor_list
from verify_q9_free_dimension_cuts import deg, parts


def audit_pair(a,b,ea,ca,eb,cb,r):
    A = {u for u in range(64) if a>>u&1}
    B = {u for u in range(64) if b>>u&1}
    V = A|{u|64 for u in B}
    assert (len(A),len(B),len(A&B))==(ea+ca,eb+cb,r)
    assert sum(deg(A,u,6) for u in A)==2*ea and sum(deg(B,u,6) for u in B)==2*eb
    assert max(deg(V,u,7) for u in V)<=2
    assert sum(deg(V,u,7) for u in V)==2*(len(V)-len(parts(V,7)))


def wanted_pairs(profiles, indices):
    keys = set()
    for index in indices:
        e,c,crossings=profiles[index]
        for (a,b),r in zip(BONDS,crossings):
            keys.add((e[a],c[a],e[b],c[b],r))
            keys.add((e[b],c[b],e[a],c[a],r))
    return keys


def table(path, wanted=None):
    out = defaultdict(set)
    with path.open() as source:
        for line in source:
            row = json.loads(line)
            ca,cb = row['components']
            r = row['crossings']
            ea,eb = row.get('edges',(25,25))
            key=ea,ca,eb,cb,r
            if wanted is not None and key not in wanted:
                continue
            a,b = map(lambda x:int(x,16),row['masks'])
            audit_pair(a,b,ea,ca,eb,cb,r)
            out[key].add((a,b))
    return out


def pin_pair(f, layers, values):
    choices = []
    for masks in sorted(values):
        choice = f.nv+1
        choices.append(choice)
        for layer,mask in zip(layers,masks):
            f.extend([[-choice,64*layer+u+1 if mask>>u&1 else -64*layer-u-1] for u in range(64)])
    f.append(choices)


def single_layer_layouts(edges, components, allow24=False):
    choices = []
    for layer, (e, c) in enumerate(zip(edges, components)):
        if e in (25, 26) or (allow24 and (e,c)==(24,4)):
            layouts = anchor_list(c, e)
            if layouts:
                choices.append((len(layouts), layer, layouts))
    return min(choices) if choices else (0, None, [])


def sibling_cases(path):
    """Only consume complete records from a sibling's live search log."""
    terminal = {"STARTED","UNSAT_DRAT_VERIFIED","SAT_PATH_VERIFIED"}
    states = {}
    for line in path.read_text().splitlines(keepends=True):
        if not line.endswith("\n"):
            continue
        record = json.loads(line)
        if "index" in record:
            states[record["index"]] = record["status"]
    return {index for index,status in states.items() if status in terminal}


def run(args):
    profiles = json.loads(args.profiles.read_text())['representatives']
    record = json.loads(args.verified.read_text().splitlines()[-1])
    assert record.get('status')=='VERIFIED' or 'colour_survivors' in record
    ids = record['indices'] if 'indices' in record else record['colour_survivors']
    if args.indices:
        assert set(args.indices)<=set(ids)
        ids = args.indices
    relevant = wanted_pairs(profiles, ids)
    data = table(args.table,relevant)
    if args.second_table:
        for key,layouts in table(args.second_table,relevant).items():
            data[key].update(layouts)
    with gzip.open(args.archive,'wt') as archive:
        for index in ids:
            if any(index in sibling_cases(path) for path in args.skip_log):
                continue
            row = profiles[index]
            e,c,r = row
            has_dense_pair = any(k and e[u]==e[v]==25 for (u,v),k in zip(BONDS,r))
            if args.mixed_only and has_dense_pair:
                continue
            covered = []
            for bond,k in zip(BONDS,r):
                if not k:
                    continue
                for u,v in (bond,bond[::-1]):
                    key = (e[u],c[u],e[v],c[v],k)
                    if key in data:
                        covered.append((len(data[key]),(u,v),key))
            n,layers,key = min(covered) if covered else (0,(),())
            layouts = []
            if args.smallest_anchor or (args.single_layer and not covered):
                count,layer,options = single_layer_layouts(e,c,args.anchor24)
                if options and (not covered or count<n):
                    n,layers,key = count,(layer,),(e[layer],c[layer])
                    layouts = [(mask,) for mask in options]
            if not layers and not args.allow_unpinned:
                continue
            f = form(row,args.saturated,args.balanced,args.layer_colour_balance,antipodal=args.antipodal,
                     distance_seven=args.distance_seven,distance_five=args.distance_five,
                     distance_three=args.distance_three)
            if len(layers)==1:
                pin_pair(f,layers,layouts)
            if len(layers)==2:
                pin_pair(f,layers,data[key])
            extra = f.nv+1
            f.append([extra])
            print(json.dumps(dict(status='STARTED',index=index,layers=layers,layout_count=n)),flush=True)
            status,cycles,points,proposed = candidate(f,[extra],args.budget,args.proof_during_search)
            proof = verify(f,[extra],cycles,args.checker,proposed) if status=='UNSAT' else None
            status = 'UNSAT_DRAT_VERIFIED' if proof else status
            result = dict(index=index,layers=layers,key=key,status=status,layout_count=n)
            if args.proof_during_search and proof:
                result['search_proof_accepted'] = proposed == proof
            if args.antipodal:
                result['antipodal'] = True
            if args.distance_seven:
                result['distance_seven'] = True
            if args.distance_five:
                result['distance_five'] = True
            if args.distance_three:
                result['distance_three'] = True
            if args.saturated:
                result['saturated'] = True
            if args.balanced:
                result['balanced'] = True
            if args.layer_colour_balance:
                result['layer_colour_balance'] = True
            archive.write(json.dumps(dict(**result,cycles=cycles,proof=proof,points=points))+'\n')
            archive.flush()
            print(json.dumps(dict(**result,cycles=len(cycles))),flush=True)
            if points:
                break


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('profiles',type=Path)
    p.add_argument('verified',type=Path)
    p.add_argument('table',type=Path)
    p.add_argument('archive',type=Path)
    p.add_argument('checker')
    p.add_argument('--budget',type=int,default=300000)
    p.add_argument('--second-table',type=Path)
    p.add_argument('--mixed-only',action='store_true')
    p.add_argument('--saturated',action='store_true')
    endpoint_scope = p.add_mutually_exclusive_group()
    endpoint_scope.add_argument('--antipodal',action='store_true',help='Require complementary endpoints; produces distance-nine-only certificates')
    endpoint_scope.add_argument('--distance-seven',action='store_true',help='Require the six fibre bits to differ when the projected endpoints differ in one bit')
    endpoint_scope.add_argument('--distance-five',action='store_true',help='Require endpoint markers at Hamming distance five')
    endpoint_scope.add_argument('--distance-three',action='store_true',help='Require endpoint markers at Hamming distance three')
    p.add_argument('--balanced',action='store_true')
    p.add_argument('--layer-colour-balance',action='store_true')
    p.add_argument('--allow-unpinned',action='store_true')
    p.add_argument('--single-layer',action='store_true',help='pin a complete Q6 layer catalogue when no pair is available')
    p.add_argument('--smallest-anchor',action='store_true',help='prefer the smallest complete catalogue')
    p.add_argument('--proof-during-search',action='store_true')
    p.add_argument('--anchor24',action='store_true',help='allow the independently reproduced 24-edge four-component catalogue')
    p.add_argument('--skip-log',type=Path,action='append',default=[])
    p.add_argument('--indices',nargs='+',type=int)
    args=p.parse_args()
    if args.layer_colour_balance and not args.balanced:
        p.error("--layer-colour-balance requires --balanced")
    if args.balanced and not args.saturated:
        p.error('--balanced requires --saturated')
    run(args)

