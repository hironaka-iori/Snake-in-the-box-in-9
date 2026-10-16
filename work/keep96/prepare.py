"""All-bank positive controls and deterministic outcome-blind diverse pilot selection."""
import json
import math
import subprocess
from collections import Counter
from common import *


def features(p):
    prefix, head = p[:96], p[95]
    banned = set(prefix[:-1])
    for v in prefix[:-1]:
        banned.update(v ^ (1 << k) for k in range(9))
    region, stack = {head}, [head]
    while stack:
        for k in range(9):
            x = stack[-1] ^ (1 << k)
            if x not in banned and x not in region:
                region.add(x)
                stack.insert(0, x)
        stack.pop()
    degree = {v: sum((v ^ (1 << k)) in region for k in range(9)) for v in region}
    counts = Counter((a ^ b).bit_length() - 1 for a, b in zip(prefix, prefix[1:]))
    return [len(region), sum(degree.values()) // 2, degree[head],
            sum(d == 1 for d in degree.values()), sum(d == 2 for d in degree.values()),
            abs(sum(1 if v.bit_count() % 2 else -1 for v in region)),
            sum(c*c for c in counts.values()), (prefix[0] ^ head).bit_count()]


def main():
    paths = bank()
    records, feature_rows = [], []
    for entry, p in enumerate(paths):
        verify_path(p)
        if len(p) != 192:
            raise ValueError('known witness length changed')
        data = encode(p, 96, 192)  # POSITIVE CONTROL ONLY: known witnesses have 191 edges.
        suffix = p[95:]
        assignment, failed = witness_assignment(data, suffix)
        if set(assignment) != set(range(1, data['variables'] + 1)) or failed:
            raise ValueError((entry, failed[:10]))
        # Independently check all auxiliary wires, including negative absent-count leaves.
        for counter in data['counters']:
            count = sum(bool(assignment[abs(lit)]) == (lit > 0) for lit in counter['leaves'])
            for threshold, wire in enumerate(counter['outputs'], 1):
                if assignment[wire] != (count >= threshold):
                    raise ValueError('counter interpretation')
        # Off-by-one negative control: unchanged known witness cannot satisfy 193-vertex target.
        target = encode(p, 96, 193)
        _, rejection = witness_assignment(target, suffix)
        if not rejection:
            raise ValueError('target mistakenly accepts only 192 vertices')
        records.append(dict(entry=entry, bank_index=entry//2, reversed=bool(entry%2),
                            status='PASSED', target_vertices=192, suffix_vertices=len(suffix),
                            assigned_variables=len(assignment), clauses_checked=len(data['clauses']),
                            counters_checked=len(data['counters']), rejected_at_target193=True))
        feature_rows.append(features(p))
        if entry % 20 == 0:
            print(f'positive controls {entry+1}/262', flush=True)
    lo = [min(row[k] for row in feature_rows) for k in range(8)]
    hi = [max(row[k] for row in feature_rows) for k in range(8)]
    norm = [[(x-lo[k])/(hi[k]-lo[k] or 1) for k,x in enumerate(row)] for row in feature_rows]
    chosen = [max(range(0,262,2), key=lambda j:(feature_rows[j][0],-j))]
    while len(chosen) < 12:
        candidates = [j for j in range(262) if j%2 == len(chosen)%2 and all(j//2 != s//2 for s in chosen)]
        def distance(j):
            return min(sum((x-y)**2 for x,y in zip(norm[j],norm[s])) for s in chosen)
        chosen.append(max(candidates, key=lambda j:(distance(j),-j)))
    provenance = dict(baseline=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
                      bank_sha256=sha(ROOT/'work/bank9.json'), encoder_sha256=sha(ROOT/'work/build_regrowth_cnf.py'),
                      prepare_sha256=sha(Path(__file__)),common_sha256=sha(HERE/'common.py'))
    save(OUT/'positive-controls.json',dict(status='PASSED', keep=96, bank_paths=131,oriented_entries=262,
                                         provenance=provenance,entries=records))
    save(OUT/'pilot-selection.json',dict(entries=chosen,provenance=provenance,
        method='Largest forward region first, then farthest-point sampling on min-max normalized features; alternate orientation; distinct bank indices; ties smallest entry. No solver outcomes used.',
        feature_names=['region_vertices','region_edges','head_degree','degree_one_count','degree_two_count','parity_imbalance','prefix_coordinate_count_squares','prefix_endpoint_distance'],
        features={str(i): row for i,row in enumerate(feature_rows)},minima=lo,maxima=hi))
    print('pilot',chosen,flush=True)


if __name__ == '__main__':
    main()
