"""Export independently replayed geometric obstructions as universal Q9 clauses."""
import argparse
import gzip
from itertools import islice, permutations, product
import json
from pathlib import Path

from q9_three_tight_pairs import BONDS


def orientations(faces,links):
    for order,origin in product(permutations(range(3)),range(8)):
        image = [origin ^ sum((v>>axis&1)<<i for i,axis in enumerate(order)) for v in range(8)]
        a = tuple(sorted((image[v],e,c) for v,e,c in faces))
        b = tuple(sorted((*sorted((image[u],image[v])),r) for u,v,r in links))
        yield a,b


def certificate_pattern(profile, record):
    if record.get('completion_colours'):
        raise ValueError('Colour certificates also depend on the projected endpoint locations')
    e,c,r = profile
    selected = set(record['layers'])
    faces = [(v,e[v],c[v]) for v in selected]
    if record.get('completion_ports'):
        # Endpoint deficits and missing-neighbour demands depend on every
        # seam incident to a selected layer, including zero-count seams.
        links = [(a,b,n) for (a,b),n in zip(BONDS,r) if a in selected or b in selected]
    else:
        links = [(a,b,n) for (a,b),n in zip(BONDS,r) if a in selected and b in selected]
    return min(orientations(faces,links))


def read_batch(profiles,replay,archive):
    check = json.loads(replay.read_text())
    assert check['status']=='VERIFIED_GEOMETRIC'
    verified = set(check['excluded'])
    bank = json.loads(profiles.read_text())['representatives']
    seen = set()
    with gzip.open(archive,'rt') as file:
        prefix = check.get('archive_prefix')
        records = file if prefix is None else islice(file,check.get('archive_start',0),prefix)
        for line in records:
            row = json.loads(line)
            i = row['index']
            if i not in verified:
                continue
            assert i not in seen and row['status']=='UNSAT_DRAT_VERIFIED'
            seen.add(i)
            yield certificate_pattern(bank[i],row), check['counts'], i
    assert seen==verified


def read_branch(stem):
    return read_batch(Path(f'{stem}_profiles.json'),Path(f'{stem}_geometric_replay.json'),
                      Path(f'{stem}_join_proofs.jsonl.gz'))


def write(stems,out,base=None,batches=(),empty_catalogues=()):
    library = {}
    total = 0
    if base:
        existing = json.loads(base.read_text())
        library.update((min(orientations(row['faces'],row['links'])),row)
                       for row in existing['patterns'])
        total = existing['source_certificates']
    initial = len(library)
    sources = [read_branch(stem) for stem in stems]
    sources.extend(read_batch(*batch) for batch in batches)
    for source in sources:
        for key,counts,index in source:
            faces,links = key
            library.setdefault(key,dict(faces=faces,links=links,source=counts,index=index))
            total+=1
    if empty_catalogues:
        from q9_screen_certified_interfaces import empty_interfaces
        for stem in empty_catalogues:
            replay = json.loads(stem.with_suffix(".replay.log").read_text().splitlines()[-1])
            empty = empty_interfaces(stem)
            total += replay["catalogue_proofs"]
            for e,c,f,d,r in empty:
                key = min(orientations(((0,e,c),(1,f,d)),((0,1,r),)))
                faces,links = key
                library.setdefault(key,dict(faces=faces,links=links,catalogue=str(stem)))
    with out.open("x") as dst:
        dst.write(json.dumps(dict(source_certificates=total,patterns=list(library.values())))+'\n')
    print(json.dumps(dict(source_certificates=total,patterns=len(library),new_patterns=len(library)-initial)),flush=True)


def oriented_library(path, forbidden_profiles=()):
    patterns = json.loads(path.read_text())['patterns']
    forbidden = {tuple(sorted(row)) for row in forbidden_profiles}
    selected = []
    for row in patterns:
        links = row['links']
        if forbidden and len(links) == 12:
            frequencies = tuple(sorted(sum(r for a,b,r in links if a ^ b == 1 << i)
                                       for i in range(3)))
            if frequencies in forbidden:
                continue
        selected.append(row)
    return sorted({o for row in selected for o in orientations(row['faces'],row['links'])})


def compatible_endpoint_patterns(patterns, endpoint):
    # For any Q6 layer, twice its component count equals its incident
    # crossing count plus its number of global endpoints.
    terminal_count = [int(v == 0) + int(v == endpoint) for v in range(8)]
    for faces,links in patterns:
        known = [0] * 8
        crossings = [0] * 8
        axis_known = [0] * 3
        axis_crossings = [0] * 3
        for a,b,r in links:
            axis = (a ^ b).bit_length() - 1
            axis_known[axis] += 1
            axis_crossings[axis] += r
            known[a] += 1
            known[b] += 1
            crossings[a] += r
            crossings[b] += r
        if any(n == 4 and c % 2 != (endpoint >> axis) & 1
               for axis,(n,c) in enumerate(zip(axis_known,axis_crossings))):
            continue
        if any(known[v] == 3 and 2 * c != crossings[v] + terminal_count[v]
               for v,_,c in faces):
            continue
        yield faces,links


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('output',type=Path)
    p.add_argument('stems',type=Path,nargs='*')
    p.add_argument('--base-library',type=Path)
    p.add_argument('--batch',type=Path,nargs=3,action='append',default=[])
    p.add_argument("--empty-catalogue",type=Path,action="append",default=[])
    a=p.parse_args()
    write(a.stems,a.output,a.base_library,a.batch,a.empty_catalogue)

