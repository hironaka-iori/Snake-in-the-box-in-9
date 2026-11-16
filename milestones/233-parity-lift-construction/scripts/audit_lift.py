"""Read-only reconstruction of saved lift evidence; no optimizer or compiler."""
from pathlib import Path
import collections
import hashlib
import itertools
import json
import math
import re

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
SOURCE = R / 'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def connected_component(adj, start):
    reached = {start}
    pending = [start]
    while pending:
        v = pending.pop()
        for w in adj[v] - reached:
            reached.add(w)
            pending.append(w)
    return reached


def check_model(path, arcs):
    text = path.read_text(encoding='utf-8')
    variable = r'variables\s*\{\s*name:\s*"a(\d+)_(\d+)"\s*domain:\s*\[0,\s*1\]\s*\}'
    assert [tuple(map(int, x)) for x in re.findall(variable, text)] == arcs
    remainder = re.sub(variable, '', text).strip()
    circuit = (r'constraints\s*\{\s*circuit\s*\{\s*tails:\s*\[([^\]]*)\]'
               r'\s*heads:\s*\[([^\]]*)\]\s*literals:\s*\[([^\]]*)\]\s*\}\s*\}')
    match = re.fullmatch(circuit, remainder)
    assert match is not None
    arrays = [list(map(int, re.findall(r'-?\d+', s))) for s in match.groups()]
    assert list(zip(arrays[0], arrays[1])) == arcs
    assert arrays[2] == list(range(len(arcs)))
    assert len(set(arcs)) == len(arcs) and all(a != b for a, b in arcs)


def graph(parent_set, neighbour_sets):
    labels = {}
    adj = {v: set() for v in sorted(parent_set)}
    for label, neighbours in neighbour_sets:
        selected = sorted(neighbours & parent_set)
        if len(selected) == 2:
            a, b = selected
            labels.setdefault((a, b), []).append(label)
            adj[a].add(b)
            adj[b].add(a)
    return labels, adj


def run():
    destination = H / 'data/lift-audit.json'
    report = H / 'logs/lift-audit.md'
    assert not destination.exists() and not report.exists()
    pin_paths = [SOURCE, H/'scripts/lift_search.py', H/'scripts/run_lift.py',
                 H/'scripts/native_resources.py', H/'data/lift.json',
                 H/'data/lift-execution.json']
    pins = {str(p): sha(p) for p in pin_paths}
    parents = json.loads(SOURCE.read_bytes())
    result = json.loads((H/'data/lift.json').read_bytes())
    execution = json.loads((H/'data/lift-execution.json').read_bytes())
    assert result['source_sha256'] == sha(SOURCE)
    assert result['script_sha256'] == sha(H/'scripts/lift_search.py')
    assert result['status'] == 'COMPLETE_QUERY_BATCH'
    assert result['arguments']['start'] == 0 and result['q9_witness'] is None
    expected_count = sum(sum(math.comb(len(parents[str(n)]['vertices']), k)
                             for k in range(3)) for n in range(5, 9))
    assert expected_count == 6763
    assert [r['id'] for r in result['results']] == list(range(expected_count))
    assert result['next_id'] == expected_count
    witnesses = {w['id']: w for w in result['witnesses']}
    assert len(witnesses) == len(result['witnesses']) == 28
    statuses = collections.Counter()
    by_dimension = {}
    models = []
    verified_witnesses = []
    obstructions = []
    ident = 0

    for n in range(5, 9):
        source = parents[str(n)]
        parent = source['vertices']
        full = set(parent)
        assert len(full) == len(parent) == source['edges'] + 1
        assert all(0 <= x < 2**n for x in parent)
        assert all(((parent[i] ^ parent[j]).bit_count() == 1) == (j == i+1)
                   for i in range(len(parent)) for j in range(i+1, len(parent)))
        if 'transitions' in source:
            assert [parent[i] ^ parent[i+1] for i in range(len(parent)-1)] == [
                1 << k for k in source['transitions']]
        lift = lambda x: x | ((x.bit_count() % 2) << n)
        # Compute neighbours by actual adjacency in Q_(n+1), independently
        # of the producer's closed-neighbourhood bit-mask calculation.
        neighbour_sets = []
        for y in range(2**n):
            z = y | ((1-y.bit_count() % 2) << n)
            actual = {x for x in parent if (lift(x) ^ z).bit_count() == 1}
            closed = {x for x in parent if (x ^ y).bit_count() <= 1}
            assert actual == closed
            neighbour_sets.append((z, actual))
        _, initial_adj = graph(full, neighbour_sets)
        initial_isolated = {x for x in parent if not initial_adj[x]}
        covers = {d: {x for x in initial_isolated if (x ^ d).bit_count() <= 2}
                  for d in parent}
        maximum = max(map(len, covers.values()))
        lower = (len(initial_isolated)+maximum-1)//maximum if maximum else 0
        balls = {x: {d for d in parent if (x ^ d).bit_count() <= 2}
                 for x in initial_isolated}
        triple = next((list(t) for t in itertools.combinations(sorted(balls), 3)
                       if all(not balls[a] & balls[b]
                              for a, b in itertools.combinations(t, 2))), None)
        pair = max(itertools.combinations(parent, 2),
                   key=lambda ds: len(covers[ds[0]] | covers[ds[1]]))
        obstructions.append({
            'parent_dimension': n, 'initial_isolated': sorted(initial_isolated),
            'initial_isolated_count': len(initial_isolated),
            'coverage_by_deleted_vertex': {str(d): sorted(covers[d]) for d in parent},
            'maximum_single_deletion_coverage': maximum,
            'maximizing_single_deletions': [d for d in parent if len(covers[d]) == maximum],
            'necessary_deletions_from_count': lower,
            'maximum_two_deletion_coverage': len(covers[pair[0]] | covers[pair[1]]),
            'maximizing_pair_example': list(pair),
            'three_isolated_vertices_with_disjoint_deletion_neighbourhoods': triple,
            'triple_deletion_neighbourhoods': ({str(x): sorted(balls[x]) for x in triple}
                                               if triple else None),
        })
        counts = collections.Counter()
        for omissions in range(3):
            for indices in itertools.combinations(range(len(parent)), omissions):
                removed = {parent[i] for i in indices}
                selected = full - removed
                ordered = sorted(selected)
                labels, adj = graph(selected, neighbour_sets)
                row = result['results'][ident]
                assert row['parent_dimension'] == n and row['cube_dimension'] == n+1
                assert row['removed_indices'] == list(indices)
                assert row['target_edges'] == 2*(len(selected)-1)
                assert row['edges'] == len(labels)
                leaves = [v for v in ordered if len(adj[v]) == 1]
                assert row['leaves'] == leaves
                isolated = [v for v in ordered if not adj[v]]
                # Verify the persistence conclusion for every enumerated deletion.
                affected = set().union(*(covers[d] for d in removed)) if removed else set()
                assert initial_isolated - affected <= set(isolated)
                if isolated:
                    expected = 'ISOLATED'
                    assert row['certificate'] == isolated
                elif len(leaves) > 2:
                    expected = 'TOO_MANY_LEAVES'
                else:
                    reached = connected_component(adj, ordered[0])
                    if len(reached) < len(selected):
                        expected = 'DISCONNECTED'
                        assert row['certificate'] == sorted(reached)
                    else:
                        expected = 'WITNESS' if ident in witnesses else 'INFEASIBLE'
                assert row['status'] == expected
                statuses[expected] += 1
                counts[expected] += 1
                if expected in ['WITNESS', 'INFEASIBLE']:
                    index = {v: i for i, v in enumerate(ordered)}
                    size = len(ordered)
                    arcs = []
                    for a, b in labels:
                        arcs.extend([(index[a], index[b]), (index[b], index[a])])
                    for i in range(size):
                        arcs.extend([(i, size), (size, i)])
                    model = H/'data'/row['model']
                    assert model.name == f'lift-{ident:05d}.pbtxt'
                    assert sha(model) == row['model_sha256']
                    assert set(v for arc in arcs for v in arc) == set(range(size+1))
                    check_model(model, arcs)
                    models.append({'id': ident, 'sha256': sha(model),
                                   'variables': len(arcs), 'status': expected})
                else:
                    assert 'model' not in row and ident not in witnesses
                if expected == 'WITNESS':
                    w = witnesses[ident]
                    route = w['contracted_path']
                    path = w['path']
                    assert len(route) == len(set(route)) == len(selected)
                    assert set(route) == selected
                    assert w['removed_indices'] == list(indices)
                    assert w['cube_dimension'] == n+1 and w['edges'] == row['target_edges']
                    reconstructed = [lift(route[0])]
                    for a, b in zip(route, route[1:]):
                        reconstructed.extend([labels[min(a,b), max(a,b)][0], lift(b)])
                    assert path == reconstructed
                    assert len(path) == len(set(path)) == w['edges']+1
                    assert all(0 <= v < 2**(n+1) for v in path)
                    assert all(((path[i] ^ path[j]).bit_count() == 1) == (j == i+1)
                               for i in range(len(path)) for j in range(i+1, len(path)))
                    verified_witnesses.append({'id': ident, 'dimension': n+1,
                                               'edges': w['edges'], 'vertices': len(path),
                                               'unordered_pairs': len(path)*(len(path)-1)//2})
                ident += 1
        by_dimension[str(n)] = dict(counts)

    assert ident == expected_count and dict(statuses) == result['statuses']
    assert len(models) == 36 and len(verified_witnesses) == 28
    assert all(by_dimension[str(n)] == {'ISOLATED': sum(math.comb(len(parents[str(n)]['vertices']), k)
                                                      for k in range(3))} for n in [6, 7, 8])
    assert execution['status'] == 'ACCEPTED_NATIVE_RESULT'
    assert execution['exit_code'] == 0 and execution['stop_reason'] is None
    for p, digest in execution['pins'].items():
        assert sha(p) == digest
    assert execution['result_sha256'] == sha(H/'data/lift.json')
    for suffix in ['stdout', 'stderr']:
        assert execution[suffix+'_sha256'] == sha(H/'logs'/('lift-'+suffix+'.log'))
    assert not (H/'logs/lift-stderr.log').read_bytes()
    stdout = json.loads((H/'logs/lift-stdout.log').read_bytes())
    for key in ['status', 'statuses', 'seconds', 'next_id', 'q9_witness']:
        assert stdout[key] == result[key]
    assert stdout['witnesses'] == [[w['cube_dimension'], w['edges'], w['id']]
                                 for w in result['witnesses']]
    assert all(not s['errors'] and not s['lean_processes'] for s in execution['resource_samples'])
    assert all(sha(path) == digest for path, digest in pins.items())
    output = {
        'status': 'PASS_INDEPENDENT_SAVED_LIFT_AUDIT',
        'scope': 'Finite graph/certificate/model/witness reconstruction; no optimizer, compiler or software tests.',
        'auditor_sha256': sha(Path(__file__)), 'pins': pins,
        'rows': expected_count, 'statuses': dict(statuses),
        'by_parent_dimension': by_dimension,
        'verified_models': models, 'verified_witnesses': verified_witnesses,
        'isolation_obstructions': obstructions,
        'execution': {'status': execution['status'], 'wrapper_seconds': execution['seconds'],
                      'worker_seconds': result['seconds'], 'samples': len(execution['resource_samples']),
                      'maximum_sampled_private_bytes': max(s['private_bytes'] or 0 for s in execution['resource_samples']),
                      'minimum_sampled_free_bytes': min(s['free_bytes'] for s in execution['resource_samples'])},
        'limitations': ['The eight INFEASIBLE queries remain native solver evidence.',
                        'No exhaustive search for arbitrary parity classes or parent snakes is implied.',
                        'The isolation covering lower bounds are necessary, not sufficient, for Hamiltonicity.',
                        'No end-to-end Lean proof of extraction or saved native contradictions was checked.'],
    }
    destination.write_text(json.dumps(output, indent=2)+'\n', encoding='utf-8')
    lines = [
        '# Parity-lift construction audit', '',
        '**No blocking defect found.** Independently reconstructed all 6,763 saved graphs, their static outcomes, all 36 exported circuit models, and all 28 successful witnesses. No optimizer, compiler, or software test was run.', '',
        '## Exact reduction and coverage', '',
        'The parity lift maps a retained parent word x to (x, parity(x)), which has even total parity. The opposite-colour vertex over a word y is adjacent to that lift exactly when x equals y or differs from y in one coordinate. The audit derived this by direct Hamming adjacency in the larger cube and checked its agreement with every closed neighbourhood used by the producer.', '',
        'A physical opposite-colour vertex with exactly two selected neighbours labels their contraction edge. Parallel labels may be collapsed for Hamiltonian-path existence: different edges of an injective ordering cannot reuse a label, since its selected neighbour pair is fixed. A Hamiltonian ordering lifts to an induced path with 2(|S|-1) edges. All endpoints and ordering are free within this exact selected parity-class family.', '',
        'The 0-, 1-, and 2-omission combinations were independently enumerated in the recorded order. All parent vertex sequences and transitions were checked. IDs are exactly 0 through 6762, with no missing or repeated row and no early stop.', '',
        '| Parent dimension | Rows | Isolated | Excess leaves | Disconnected | Native infeasible | Witnesses |',
        '|---:|---:|---:|---:|---:|---:|---:|',
    ]
    for n, d in by_dimension.items():
        lines.append(f"| {n} | {sum(d.values())} | {d.get('ISOLATED',0)} | {d.get('TOO_MANY_LEAVES',0)} | {d.get('DISCONNECTED',0)} | {d.get('INFEASIBLE',0)} | {d.get('WITNESS',0)} |")
    lines += [
        '', 'Every graph edge count, leaf list, isolated-vertex certificate, and disconnected component matched the reconstruction. All 36 models contain exactly the expected Boolean arcs and one circuit constraint: both directions of each simple graph edge and both directions between every graph vertex and a mandatory dummy, with no self-loops. Every node therefore lies on the single circuit; removing the dummy gives precisely a Hamiltonian path. Model hashes all match the saved records.', '',
        'All 28 witnesses were reconstructed from their contracted order and labels, checked for distinct vertices and correct dimension/length, and checked on every unordered vertex pair. They occur only in Q6. The eight remaining circuit results are native infeasibility reports; their contradictions were not independently replayed. No Q9 witness was produced.', '',
        '## Isolation covering argument', '',
        'Let I be the initially isolated parent vertices. If a retained x in I acquires a contraction edge after deleting a set D, some deleted vertex d must have shared a relevant closed neighbourhood with x. Hence their parent-cube Hamming distance is at most two. If x itself is deleted, it is also covered by this condition. Therefore removing all inherited isolation requires I to be covered by the radius-two neighbourhoods of the deleted parent vertices.', '',
        'This necessity was additionally checked against every enumerated deletion: each initially isolated vertex outside that union remains in the reconstructed isolated set. If one deletion covers at most c members of I, at least ceil(|I|/c) deletions are necessary. Three initially isolated vertices whose permissible-deletion neighbourhoods are pairwise disjoint also require at least three deletions.', '',
        '| Parent dimension | Initial isolated vertices | Maximum coverage by one deletion | Necessary deletions from count | Disjoint triple |',
        '|---:|---:|---:|---:|---|',
    ]
    for o in obstructions:
        lines.append(f"| {o['parent_dimension']} | {o['initial_isolated_count']} | {o['maximum_single_deletion_coverage']} | {o['necessary_deletions_from_count']} | {o['three_isolated_vertices_with_disjoint_deletion_neighbourhoods']} |")
    lines += [
        '', 'For the Q8 parent, 69 initially isolated vertices and maximum coverage 17 prove that at least five deletions are needed to remove inherited isolation. Thus every deletion of at most four parent vertices still leaves an isolated vertex; the stronger conclusion is a consequence of this small covering certificate, rather than an additional Hamiltonian search. For the Q7 parent, 37 and 12 similarly require at least four deletions. The full parent-restricted neighbourhood lists, coverage maxima, and triple witnesses are saved in the audit JSON.', '',
        'The Q6 counting bound alone requires only two deletions and supplies no disjoint triple. Its complete 0/1/2-omission exclusion is supported by the directly reconstructed isolated-vertex certificates. The Q5 parent has no initially isolated vertex, so this inherited-isolation argument gives no bound there. None of these necessary deletion bounds guarantees a path after that many deletions.', '',
        '## Execution integrity and limits', '',
        'The resource receipt is ACCEPTED_NATIVE_RESULT with exit code zero and no stop reason. All source/input/result/stdout/stderr pins match; stderr is empty and stdout agrees with the result. The resource sample arrays contain no recorded errors or Lean processes. Exact timing and sampled-memory values are retained in the audit JSON; sampled maxima are not continuous peak guarantees.', '',
        'The covered families use only the four saved parent paths, their specified parity lift, and the listed omissions. They do not cover arbitrary parent snakes or arbitrary parity-class changes. The general reduction and isolation argument are written mathematical deductions; no end-to-end Lean extraction or solver-certificate claim is made.', '',
        '## Pinned evidence', '', '| File | SHA-256 |', '|---|---|',
    ]
    lines += [f'| `{p}` | `{digest}` |' for p, digest in pins.items()]
    lines += [f'| `scripts/audit_lift.py` | `{sha(Path(__file__))}` |',
              f'| `data/lift-audit.json` | `{sha(destination)}` |', '',
              'Only the assigned audit script, audit JSON, and this report were written. Existing search evidence and documents were unchanged.', '']
    report.write_text('\n'.join(lines), encoding='utf-8')
    print(json.dumps({'status': output['status'], 'rows': expected_count,
                      'statuses': dict(statuses), 'by_parent_dimension': by_dimension,
                      'witness_lengths': dict(collections.Counter(w['edges'] for w in verified_witnesses)),
                      'obstructions': [{k: o[k] for k in ['parent_dimension', 'initial_isolated_count',
                          'maximum_single_deletion_coverage', 'necessary_deletions_from_count',
                          'maximum_two_deletion_coverage',
                          'three_isolated_vertices_with_disjoint_deletion_neighbourhoods']}
                          for o in obstructions],
                      'execution': output['execution'], 'audit_json_sha256': sha(destination),
                      'report_sha256': sha(report), 'auditor_sha256': sha(Path(__file__))}, indent=2))


if __name__ == '__main__':
    run()
