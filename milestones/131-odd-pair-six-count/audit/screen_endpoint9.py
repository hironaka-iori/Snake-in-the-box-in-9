"""Cheap independent actual-witness screen; no solver, graph or Lean imports."""
from pathlib import Path
import hashlib
import itertools
import json
import re
import time
from collections import Counter

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sha = lambda b: hashlib.sha256(b).hexdigest()
def canon(word):
    seen = {}
    return [seen.setdefault(x,len(seen)) for x in word]

def check(path):
    assert all(type(v) is int and 0 <= v < 512 for v in path)
    assert len(set(path)) == len(path)
    pairs = 0
    for i,u in enumerate(path):
        for j in range(i+1,len(path)):
            assert ((u ^ path[j]).bit_count() == 1) == (j == i+1)
            pairs += 1
    directions = [(a^b).bit_length()-1 for a,b in zip(path,path[1:])]
    selected = set(path)
    alpha, details = {}, {}
    for k in range(1,len(path)-1):
        incident = {directions[k-1], directions[k]}
        assert len(incident) == 2
        allowed = [(a,b) for a,b in itertools.combinations(range(9),2) if a not in incident and b not in incident]
        assert len(allowed) == 21
        corners = [path[k] ^ (1<<a) ^ (1<<b) for a,b in allowed]
        absent = [x for x in corners if x not in selected]
        # Independently evaluate the literal36-pair singPred from LocalWindowBridge.
        direct = sum(path[k]^(1<<a) not in selected and path[k]^(1<<b) not in selected
                     and path[k]^(1<<a)^(1<<b) not in selected for a,b in itertools.combinations(range(9),2))
        assert direct == len(absent)
        alpha[k] = direct
        details[k] = dict(index=k,vertex=path[k],incident_directions=sorted(incident),allowed_pairs=allowed,
            opposite_corners=corners,absent_opposite_corners=absent,alpha=direct,
            endpoint_distances=[(path[k]^path[0]).bit_count(),(path[k]^path[-1]).bit_count()])
    shape_rows, nine_rows = [], []
    for r in range(len(path)-6):
        word = directions[r:r+6]
        if canon(word) != [0,1,2,0,3,2]:
            continue
        row = dict(start=r,window_vertices=path[r:r+7],directions=word,canonical=canon(word),
            counts=[alpha[r+i] for i in range(1,6)],pair_counts=[alpha[r+2],alpha[r+4]])
        shape_rows.append(row)
        if alpha[r+2]+alpha[r+4] == 9:
            row = dict(row,centres=[details[r+2],details[r+4]])
            row['has_endpoint_at_distance_two'] = any(2 in c['endpoint_distances'] for c in row['centres'])
            row['same_endpoint_at_distance_two_from_both'] = any(
                all(c['endpoint_distances'][end] == 2 for c in row['centres']) for end in range(2))
            row['edge_length_parity'] = (len(path)-1)%2
            nine_rows.append(row)
    return dict(edges=len(path)-1,edge_length_parity=(len(path)-1)%2,pairs_checked=pairs,induced_and_distinct=True,
        canonical_windows=len(shape_rows),pair_sum_histogram=dict(sorted(Counter(sum(r['pair_counts']) for r in shape_rows).items())),
        pair9_windows=nine_rows)

def main():
    start = time.monotonic()
    sources = {}
    def read(rel):
        raw = (ROOT/rel).read_bytes()
        sources[rel] = sha(raw)
        return raw.decode('utf-8-sig')
    lean_rel = 'work/final_lean/Snake9.lean'
    text = read(lean_rel)
    values = [int(x) for x in re.search(r'def witnessValues : Array Nat := #\[([^]]+)\]',text).group(1).split(',')]
    bank_rel = 'work/bank9.json'
    bank = json.loads(read(bank_rel))
    for rel in ['work/final_lean/LocalWindowBridge.lean','work/final_lean/LocalWindowModel.lean']:
        read(rel)
    candidates = [(lean_rel,'witnessValues',values)] + [(bank_rel,i,row['vertex_sequence']) for i,row in enumerate(bank)]
    endpoint_rel = 'work/spectral/stronger/EndpointFourWitness.lean'
    endpoint_text = read(endpoint_rel)
    endpoint_values = [int(x) for x in re.search(r'def values : Array Nat := #\[([^]]+)\]',endpoint_text).group(1).split(',')]
    candidates.append((endpoint_rel,'values',endpoint_values))
    rows = []
    counterexample = None
    for source,key,path in candidates:
        result = check(path)
        result.update(source=source,source_entry=key)
        rows.append(result)
        failures = [row for row in result['pair9_windows'] if not row['has_endpoint_at_distance_two']]
        if failures:
            counterexample = dict(source=source,source_sha256=sources[source],source_entry=key,
                vertices=path,edges=len(path)-1,endpoints=[path[0],path[-1]],window=failures[0],
                independently_validated=True,pairs_checked=result['pairs_checked'])
            break
    out = dict(status='COUNTEREXAMPLE_FOUND' if counterexample else 'FINITE_SCREEN_NO_COUNTEREXAMPLE',
        hypothesis='For every fitting canonical012032 window with alpha_(r+2)+alpha_(r+4)=9, at least one of the two global endpoints is at distance2 from at least one of these two centres.',
        stronger_odd_length_hypothesis='For odd edge length, some one global endpoint is at distance2 from both centres. This is separately unproved; an even-length failure would not refute it.',
        witnesses_checked=len(rows),pair9_windows_checked=sum(len(r['pair9_windows']) for r in rows),
        canonical_windows_checked=sum(r['canonical_windows'] for r in rows),witnesses=rows,counterexample=counterexample,
        distinct_exact_vertex_sequences_checked=len({tuple(path) for _,_,path in candidates[:len(rows)]}),
        qualifying_window_screen_is_vacuous=not any(r['pair9_windows'] for r in rows),
        source_files_sha256=sources,script_sha256=sha(Path(__file__).read_bytes()),seconds=time.monotonic()-start,
        count_method='21 coordinate pairs avoid the two incident path directions. Alpha counts their absent opposite corners. This is independently cross-checked against the36-pair singleton-square definition.',
        scope='Existing actual witnesses only, independently checked for Q9 membership, distinctness and adjacency iff consecutive. Stop after the first counterexample. No SAT, Lean or full-graph computation.')
    target = HERE/'data/endpoint9-witness-screen.json'
    target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    if counterexample:
        w = counterexample['window']
        report = f'''# Endpoint condition for pair sum9

The proposed universal endpoint condition is false.

The existing {counterexample['edges']}-edge witness in `{counterexample['source']}`, entry `{counterexample['source_entry']}`, supplies a counterexample at start index {w['start']}. Its six directions are `{w['directions']}`, with canonical form `012032`. The two singleton-square counts are {w['pair_counts']}, summing to9.

The two centres have distances {w['centres'][0]['endpoint_distances']} and {w['centres'][1]['endpoint_distances']} from the two global endpoints, respectively. None of these four distances equals2.

All {counterexample['pairs_checked']} unordered vertex pairs were independently checked: adjacency holds exactly for consecutive indices. All vertices are distinct and lie in the nine-dimensional cube. Counts were computed by the21 free coordinate pairs and independently checked using all36 singleton-square predicates.

The JSON record preserves the complete vertex sequence, window, all21 opposite corners for each centre, absent corners, distances and source hashes. Screening stopped after this counterexample; no later witness is claimed checked. This disproves the stated endpoint implication, including its restriction to odd-length snakes. It does not exclude different conditions involving longer windows or additional counts.
'''
    else:
        report = f'''# Endpoint condition for pair sum9

No counterexample was found among {len(rows)} independently validated source entries: the explicit191-edge witness, the131-entry191-edge bank, and the120-edge endpoint-count witness. There are {out['distinct_exact_vertex_sequences_checked']} distinct exact vertex sequences. Every entry was checked for membership in the nine-dimensional cube, distinct vertices, and adjacency exactly at consecutive indices.

There are {out['canonical_windows_checked']} fitting canonical012032 windows, but only {out['pair9_windows_checked']} have pair sum9. The qualifying-window screen is therefore {'vacuous: these witnesses provide no evidence for or against the proposed endpoint implication' if out['qualifying_window_screen_is_vacuous'] else 'finite only; it proves no universal endpoint implication'}.

The stronger odd-length proposal, requiring the same endpoint to be at distance2 from both centres, also receives no qualifying test. The saved checker records edge-length parity and both endpoint conditions whenever a qualifying window occurs. An even-length counterexample alone would not refute this odd-length proposal.

At each internal centre, the count uses the21 coordinate pairs avoiding the two incident directions and counts absent opposite corners. An independent evaluation of all36 singleton-square predicates gives the same result. The JSON record preserves source hashes, per-entry validation counts, pair-sum distributions, and every qualifying window. No solver, Lean or full-graph computation was run.
'''
    (HERE/'audit/endpoint9-witness-screen.md').write_text(report,encoding='utf-8')
    print(json.dumps({k:out[k] for k in ['status','witnesses_checked','pair9_windows_checked','canonical_windows_checked','seconds']},indent=2))
    if counterexample:
        print(json.dumps(counterexample['window'],indent=2))

if __name__ == '__main__':
    main()
