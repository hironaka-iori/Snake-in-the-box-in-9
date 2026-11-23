"""Combine verified projection, local and full Q9 evidence for a frequency triple."""
import argparse
from collections import defaultdict
import json
from pathlib import Path

from q9_three_tight_star_refine import anchor_list, excludes
from q9_three_tight_pairs import BONDS
from q9_geometry_cut_library import oriented_library


def records(path):
    return [json.loads(line) for line in path.read_text().splitlines()]


def completed_replay_records(path, done_status):
    lines = [line for line in path.read_text().splitlines(keepends=True) if line.endswith("\n")]
    if not lines:
        return []
    try:
        terminal = json.loads(lines[-1])
    except json.JSONDecodeError:
        return []
    if not isinstance(terminal, dict) or terminal.get("status") != done_status:
        return []
    return [json.loads(line) for line in lines]


def geometry_screen(profile_path,screen_path,replay_path,empty_pairs=None,geometric_library=None):
    profiles = json.loads(profile_path.read_text())['representatives']
    screen = json.loads(screen_path.read_text())
    rr = records(replay_path)
    assert rr[-1]['status']=='VERIFIED'
    stars = [row['key'] for row in rr if row['status']=='REPLAYED_STAR']
    impossible = set()
    if isinstance(empty_pairs,Path):
        empty_pairs = [empty_pairs]
    for proof in empty_pairs or ():
        pair_proof = records(proof)[-1]
        assert pair_proof['status']=='VERIFIED' and not pair_proof['layouts']
        cases = pair_proof['covered_cases']
        edges = pair_proof.get('anchor_edges',25)
        assert pair_proof['catalogue_proofs']==sum(len(anchor_list(c,edges)) for c,_,_,_ in cases)
        impossible.update((edges,center,e,c,r) for center,e,c,r in cases)
    def unavailable(row):
        e,c,cross = row
        return any((e[u],c[u],e[v],c[v],k) in impossible
                   for bond,k in zip(BONDS,cross) if k for u,v in (bond,bond[::-1]))
    by_shape = defaultdict(set)
    bond_index = {bond:i for i,bond in enumerate(BONDS)}
    if geometric_library:
        for faces,links in oriented_library(geometric_library):
            layer_ids = tuple(v for v,_,_ in faces)
            bond_ids = tuple(bond_index[a,b] for a,b,_ in links)
            values = tuple((e,c) for _,e,c in faces),tuple(r for _,_,r in links)
            by_shape[layer_ids,bond_ids].add(values)
    def forbidden_geometry(row):
        e,c,cross = row
        for (layers,bonds),patterns in by_shape.items():
            values = tuple((e[u],c[u]) for u in layers),tuple(cross[i] for i in bonds)
            if values in patterns:
                return True
        return False
    keep,drop = [],[]
    for i in screen['colour_survivors']:
        row = profiles[i]
        rejected = unavailable(row) or any(excludes(row,key) for key in stars) or forbidden_geometry(row)
        (drop if rejected else keep).append(i)
    return dict(status='VERIFIED',counts=screen['counts'],initial=len(keep)+len(drop),
                excluded_by_local=len(drop),indices=keep)


def replay_indices(rows, allowed):
    summary = rows[-1]
    assert summary['status']=='REPLAY_DONE'
    verified = [r['index'] for r in rows[:-1] if r['status']=='VERIFIED_FULL_Q9']
    checked = set(verified)
    unresolved = set(summary['unresolved'])
    assert len(verified)==len(checked)==summary['verified']
    assert not checked&unresolved and checked|unresolved<=allowed
    assert summary['tested']==len(checked|unresolved)
    return checked


def audit(screen,projection,full,local=()):
    p = records(projection)[-1]
    assert p['status']=='VERIFIED' and p['orbits']==screen['initial']
    if isinstance(full, Path):
        full = [full]
    allowed = set(screen['indices'])
    ids = set().union(*(replay_indices(records(path),allowed) for path in full))
    local = set(local)
    assert local<=allowed and ids|local==allowed
    return dict(status='FREQUENCY_BRANCH_CLOSED',counts=screen['counts'],
                initial_orbits=screen['initial'],excluded_by_local=screen['excluded_by_local']+len(local),
                full_q9_verified=len(ids-local),remaining=0)


if __name__=='__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('profiles',type=Path)
    parser.add_argument('screen',type=Path)
    parser.add_argument('local_replay',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--projection',type=Path)
    parser.add_argument('--full',type=Path,action='append')
    parser.add_argument('--empty-pair-replay',type=Path,action='append')
    parser.add_argument('--geometric-replay',type=Path)
    parser.add_argument('--universal-geometry',type=Path)
    args = parser.parse_args()
    report = geometry_screen(args.profiles,args.screen,args.local_replay,args.empty_pair_replay,args.universal_geometry)
    if args.geometric_replay:
        geometry = records(args.geometric_replay)[-1]
        assert geometry['status']=='VERIFIED_GEOMETRIC' and geometry['counts']==report['counts']
        closed,rest = set(geometry['excluded']),set(geometry['indices'])
        current = set(report['indices'])
        assert not closed&rest and current<=closed|rest
        assert geometry['base']==len(closed|rest)
        report['excluded_by_local']+=len(current&closed)
        report['indices']=sorted(current&rest)
    if args.projection:
        assert args.full
        report = audit(report,args.projection,args.full)
    args.output.write_text(json.dumps(report)+'\n')
    print(json.dumps(report),flush=True)

