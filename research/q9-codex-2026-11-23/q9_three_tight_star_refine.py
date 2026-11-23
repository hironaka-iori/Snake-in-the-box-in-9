"""Replay targeted Q6 interface cuts and search for cuts on remaining profiles."""
import argparse
import gzip
import json
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path

from q6_exact_anchored_profiles import catalogue
from q6_star_interfaces import check, formula, search
from q9_lift_three_tight_pairs import ROOT, surviving_profiles
from q9_three_tight_pairs import BONDS


def anchor_list(components,edges=25):
    names = {24:'q6_24_edge_catalogue.log',25:'q6_25_edge_catalogue.log',26:'q6_26_edge_interfaces.log'}
    if edges == 23 and components in (3, 4):
        return list(catalogue(ROOT/'q6_23_c3_c4_edge_catalogue.log',components))
    if edges == 24 and components in (1, 2):
        return list(catalogue(ROOT/'q6_24_c1_c2_edge_catalogue.log',components))
    return list(catalogue(ROOT/names[edges],components))


def excludes(row,key):
    e,c,r = row
    center_edges,center_components,leaves = key
    contacts = dict(zip(BONDS,r))
    for u,(eu,cu) in enumerate(zip(e,c)):
        if (eu,cu) != (center_edges,center_components):
            continue
        neighbors = [u^(1<<axis) for axis in range(3)]
        for order in permutations(neighbors,len(leaves)):
            matches = []
            for v,(ev,cv,count) in zip(order,leaves):
                contact = contacts[tuple(sorted((u,v)))]
                matches.append((e[v]>=ev and contact>=count) if cv is None
                               else (e[v],c[v],contact)==(ev,cv,count))
            if all(matches):
                return True
    return False


def replay_existing(rows,checker):
    for name in ('q6_star_interfaces.jsonl.gz','q6_general_star_interfaces.jsonl.gz'):
        with gzip.open(ROOT/name,'rt') as source:
            for i,line in enumerate(source):
                record = json.loads(line)
                key = record['key']
                hits = [k for k,row in rows.items() if excludes(row,key)]
                if not hits or record['status'] != 'UNSAT_all_anchors_verified':
                    continue
                e,c,leaves = key
                anchors = anchor_list(c)
                assert e==25 and anchors and [int(x['anchor'],16) for x in record['cases']]==anchors
                for mask,case in zip(anchors,record['cases']):
                    assert case['status']=='UNSAT_DRAT_verified'
                    check(formula(mask,leaves),case['proof'],checker)
                print(json.dumps(dict(status='EXISTING_DRAT_REPLAYED',archive=name,
                                      index=i,key=key,anchors=len(anchors),excluded=hits)),flush=True)
                for k in hits:
                    del rows[k]
                yield key


def proposals(rows):
    frequencies = Counter()
    for e,c,r in rows.values():
        neighbors = [[] for _ in range(8)]
        for (a,b),n in zip(BONDS,r):
            if n:
                neighbors[a].append((e[b],c[b],n))
                neighbors[b].append((e[a],c[a],n))
        for u,(eu,cu) in enumerate(zip(e,c)):
            if eu!=25:
                continue
            for degree in range(2,len(neighbors[u])+1):
                for selected in combinations(neighbors[u],degree):
                    generic = tuple(sorted(((ev,None,n) for ev,_,n in selected),reverse=True))
                    frequencies[eu,cu,generic] += 1
                    exact = tuple(sorted(selected,reverse=True))
                    frequencies[eu,cu,exact] += 1
    return frequencies


def run(args):
    rows = dict(enumerate(surviving_profiles()))
    cuts = list(replay_existing(rows,args.checker))
    print(json.dumps(dict(status='AFTER_REPLAY',profiles=sorted(rows))),flush=True)
    book = proposals(rows)
    attempted = set()
    with gzip.open(args.archive,'wt') as archive:
        for _ in range(args.limit):
            scored = [(tuple(i for i,row in rows.items() if excludes(row,key)),key)
                      for key in book if key not in attempted]
            scored = [(hits,key) for hits,key in scored if hits]
            if not scored:
                break
            hits,key = max(scored,key=lambda pair: (len(pair[0]),
                            sum(c is not None for _,c,_ in pair[1][2]),book[pair[1]]))
            attempted.add(key)
            anchors = anchor_list(key[1])
            assert anchors
            print(json.dumps(dict(status='STARTED',key=key,anchors=len(anchors),possible=hits)),flush=True)
            record = search(key,anchors,args.checker,args.budget)
            archive.write(json.dumps(record)+'\n')
            archive.flush()
            if record['status']=='UNSAT_all_anchors_verified':
                cuts.append(key)
                for i in hits:
                    del rows[i]
            print(json.dumps({k:v for k,v in record.items() if k!='cases'}),flush=True)
    args.residual.write_text(json.dumps(dict(cuts=cuts,profiles=rows))+'\n')
    print(json.dumps(dict(status='DONE',remaining=sorted(rows))),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('checker')
    p.add_argument('archive',type=Path)
    p.add_argument('residual',type=Path)
    p.add_argument('--limit',type=int,default=7)
    p.add_argument('--budget',type=int,default=20000)
    run(p.parse_args())

