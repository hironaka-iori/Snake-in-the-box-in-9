"""Independent Q9 path/count audit and source-only Lean witness preparation.

No solver or compiler is imported or launched. By default only prints a summary.
--output and --prepare-lean create new files exclusively; neither overwrites.
"""
from pathlib import Path
from itertools import combinations
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def lean_source(label, order, start, pair):
    size, m = len(order), len(order)-1
    a, b = pair
    return f'''import LocalWindowTags
import LocalWindowBridge
import ReferenceInterface

namespace Snake9.Boundary121.Pair{label}
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private def values : Array Nat := #[{', '.join(map(str, order))}]
private def vertex (i : Fin {size}) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem distinct : ∀ i j : Fin {size}, vertex i = vertex j → i = j := by
  decide +kernel
#print axioms distinct

theorem induced : ∀ i j : Fin {size}, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by
  decide +kernel
#print axioms induced

def witness : Snake {m} := ⟨vertex, distinct, induced⟩

theorem window_directions : ∀ j : Fin 6,
    dir witness ({start}+j.val) = ([0,1,2,0,3,2] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel
#print axioms window_directions

theorem window_word : dsOf witness {start} 6 = [0,1,2,0,3,2] := by
  simp only [dsOf, dir, Tags.dirOfStep_eq]
  decide +kernel
#print axioms window_word

theorem canonical_window : canon (dsOf witness {start} 6) = [0,1,2,0,3,2] := by
  rw [window_word]
  rfl
#print axioms canonical_window

theorem counts : coreAlpha witness {start+2} = {a} ∧
    coreAlpha witness {start+4} = {b} := by
  decide +kernel
#print axioms counts

theorem total : coreAlpha witness {start+2} + coreAlpha witness {start+4} = 8 := by
  rcases counts with ⟨h2,h4⟩
  omega
#print axioms total

theorem attainment : ∃ p : Snake {m},
    {start}+6 ≤ {m} ∧ canon (dsOf p {start} 6) = [0,1,2,0,3,2] ∧
    coreAlpha p {start+2} = {a} ∧ coreAlpha p {start+4} = {b} ∧
    coreAlpha p {start+2} + coreAlpha p {start+4} = 8 := by
  exact ⟨witness,by decide,canonical_window,counts.1,counts.2,total⟩
#print axioms attainment
end Snake9.Boundary121.Pair{label}
'''


parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path)
parser.add_argument('--prepare-lean', action='store_true')
args = parser.parse_args()
if args.output:
    assert not args.output.exists(), 'Evidence output already exists'
if args.prepare_lean:
    assert all(not (HERE/'lean'/f'Boundary{label}.lean').exists() for label in ['26','35','44'])

pins, rows, sources = {}, [], []
expected = {'26': (143, [10,2,8,6,12]),
            '35': (139, [13,3,12,5,12]),
            '44': (145, [12,4,12,4,13])}
for label, (size, expected_counts) in expected.items():
    path = HERE/'data/full-probes'/f'012032-full-pair{label}.json'
    d = json.loads(path.read_text(encoding='utf-8-sig'))
    pins[path.relative_to(ROOT).as_posix()] = sha(path)
    assert d['status'] == 'SAT_PATH_CANDIDATE' and d['radius'] == 9
    assert d['ball_vertices'] == 512 and d['sum_cap'] is None and not d['sum_counter_added']
    producer = HERE/'scripts/probe_full.py'
    assert sha(producer) == d['script_sha256']
    pins[producer.relative_to(ROOT).as_posix()] = sha(producer)
    for rel, digest in d['source_files_sha256'].items():
        assert sha(ROOT/rel) == digest, rel
        pins[rel] = digest
    selected = d['selected']
    S = set(selected)
    assert len(S) == len(selected) == size and all(0 <= v < 512 for v in S)
    adj = {v: {v ^ (1 << k) for k in range(9)} & S for v in S}
    endpoints = sorted(v for v in S if len(adj[v]) == 1)
    assert len(endpoints) == 2 and all(len(adj[v]) in [1,2] for v in S)
    order = [endpoints[0]]
    while True:
        following = adj[order[-1]] - ({order[-2]} if len(order)>1 else set())
        if not following:
            break
        assert len(following) == 1
        nxt = next(iter(following))
        assert nxt not in order
        order.append(nxt)
    assert set(order) == S and len(order) == size and order[-1] == endpoints[1]
    word = [0,1,2,0,3,2]
    assert d['directions'] == word
    window = [0]
    for direction in word:
        window.append(window[-1] ^ (1 << direction))
    assert d['window'] == window
    placements = [i for i in range(size-6) if order[i:i+7] == window]
    if not placements:
        order.reverse()
        placements = [i for i in range(size-6) if order[i:i+7] == window]
    assert len(placements) == 1
    start = placements[0]
    checked_pairs = 0
    for i, j in combinations(range(size), 2):
        assert ((order[i] ^ order[j]).bit_count() == 1) == (j == i+1)
        checked_pairs += 1
    assert checked_pairs == size*(size-1)//2
    actual_word = [(order[start+j] ^ order[start+j+1]).bit_length()-1 for j in range(6)]
    assert actual_word == word
    counts, absent_vertices = [], []
    for j in range(1,6):
        at = start+j
        v = order[at]
        used = {(v ^ order[at-1]).bit_length()-1, (v ^ order[at+1]).bit_length()-1}
        assert len(used) == 2
        corners = [v ^ (1 << a) ^ (1 << b)
                   for a,b in combinations([k for k in range(9) if k not in used],2)]
        assert len(corners) == len(set(corners)) == 21
        missing = sorted(c for c in corners if c not in S)
        counts.append(len(missing))
        absent_vertices.append(missing)
    assert counts == expected_counts == d['census']['alpha']
    assert all(lo <= value <= hi for value,(lo,hi) in zip(counts,d['bounds']))
    pair = [int(label[0]), int(label[1])]
    assert [counts[1],counts[3]] == pair and sum(pair) == 8
    for cut in d['cycle_cuts']:
        C = set(cut)
        assert len(C) == len(cut)>2 and all(0<=v<512 for v in C)
        cadj = {v: {v ^ (1 << k) for k in range(9)} & C for v in C}
        assert all(len(ns)==2 for ns in cadj.values())
        seen, todo = {cut[0]}, [cut[0]]
        while todo:
            for v in cadj[todo.pop()]-seen:
                seen.add(v)
                todo.append(v)
        assert seen == C and not C <= S
    source = lean_source(label,order,start,pair)
    source_path = HERE/'lean'/f'Boundary{label}.lean'
    if args.prepare_lean:
        with source_path.open('x',encoding='utf-8',newline='\n') as stream:
            stream.write(source)
        sources.append(dict(path=source_path.relative_to(ROOT).as_posix(),sha256=sha(source_path),
                            status='SOURCE_ONLY_NOT_COMPILED',axiom_report_requests=8))
    rows.append(dict(label=label,probe=path.relative_to(ROOT).as_posix(),probe_sha256=sha(path),
        vertices=size,edges=size-1,order=order,endpoints=[order[0],order[-1]],start=start,
        window=window,directions=actual_word,counts=counts,absent_corner_vertices=absent_vertices,
        pair=pair,pair_sum=8,all_pair_checks=checked_pairs,components=1,validated_cycle_cuts=len(d['cycle_cuts']),
        source_path=source_path.relative_to(ROOT).as_posix()))

template = ROOT/'milestones/119-shared-five-count-pressure/lean/Counterexample119.lean'
pins[template.relative_to(ROOT).as_posix()] = sha(template)
out = dict(status='PASS_INDEPENDENT_FULL_Q9_BOUNDARY_PATHS',paths=rows,
    total_pair_checks=sum(row['all_pair_checks'] for row in rows),prepared_sources=sources,
    source_pins=pins,script_sha256=sha(Path(__file__)),
    scope='Direct path reconstruction, full all-pair inducedness, five exact absent-corner counts, window alignment, cut and source-hash validation. Lean source preparation only; no compiler or solver run. Establishes native witnesses attaining sum8, independently of the pending universal lower-bound proof.')
if args.output:
    with args.output.open('x',encoding='utf-8',newline='\n') as stream:
        json.dump(out,stream,indent=2)
        stream.write('\n')
print(json.dumps(dict(status=out['status'],paths=[{k:r[k] for k in ['label','vertices','edges','start','counts','pair_sum','all_pair_checks']} for r in rows],
    total_pair_checks=out['total_pair_checks'],output_sha256=sha(args.output) if args.output else None,
    sources=sources),indent=2))
