"""Independent pairwise witness and cycle audit; does not certify solver UNSAT."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def adjacent(v,w): return (v^w).bit_count() == 1


def main():
    table_path = ROOT/'milestones/16-cycle-reservoirs/data/cell-states.json'
    tables = json.loads(table_path.read_text())['tables']
    expected = sorted(h*32+v for h in range(16) for v in tables[h.bit_count()%2]['vertices'])
    sources = [HERE/'scripts/search.py',*sorted((HERE/'scripts/snapshots').glob('*.py'))]
    source_hashes = {sha(p) for p in sources}
    out = {'status':'PASSED','scope':'Independent witnesses, cycle cuts, source hashes, and Lean audit; no solver infeasibility certificate.',
           'runs':{},'sha256_lf':{}}
    cycle_reference = None
    for p in sorted((HERE/'data').glob('*.json')):
        d = json.loads(p.read_text())
        if 'rounds' not in d: continue
        assert d['script_sha256_lf'] in source_hashes
        assert d['table_sha256_lf'] == sha(table_path)
        assert d['allowed_vertices'] == expected
        for c in d['initial_cycles']+d['cuts_added']:
            assert len(c) == len(set(c)) and len(c) >= 4
            assert all(sum(adjacent(v,w) for w in c) == 2 for v in c)
        if not d['allow_local_cycles']:
            assert len(d['initial_cycles']) == 160
            if cycle_reference is None: cycle_reference = d['initial_cycles']
            assert cycle_reference == d['initial_cycles']
        for r in d['rounds']:
            if 'seed_vertices' not in r: continue
            selected = r['seed_vertices']; s = set(selected)
            assert len(s) == len(selected) and s <= set(expected)
            if d.get('maximize',False): assert len(s) <= d['target_edges']+1
            else: assert len(s) == d['target_edges']+1
            degrees = {v:sum(adjacent(v,w) for w in s) for v in s}
            assert all(k in (1,2) for k in degrees.values())
            assert sum(k == 1 for k in degrees.values()) == 2
            flat = [v for c in r['components'] for v in c]
            assert len(flat) == len(set(flat)) and set(flat) == s
            for c in r['components']:
                reached = {c[0]}
                while True:
                    nxt = reached | {w for v in reached for w in c if adjacent(v,w)}
                    if nxt == reached: break
                    reached = nxt
                assert reached == set(c)
                assert all(not adjacent(v,w) for v in c for w in s-set(c))
            path = r['path_vertices']
            assert len(set(path)) == len(path) and set(path) <= s
            for j,v in enumerate(path):
                for i,w in enumerate(path[:j]): assert adjacent(v,w) == (i+1 == j)
            assert r['path_edges'] == len(path)-1
            assert set(path) in [set(c) for c in r['components']]
            assert r['cycle_lengths'] == sorted(len(c) for c in r['components'] if set(c) != set(path))
            if d['connected_model']: assert set(path) == s
            for h in range(16):
                t = tables[h.bit_count()%2]
                mask = sum(1<<i for i,v in enumerate(t['vertices']) if h*32+v in s)
                assert mask == r['cell_masks'][h]
                assert mask in {row[0] for row in t['rows']}
            for c in d['initial_cycles']: assert not set(c) <= s
            if 'snake_vertices' in d: assert d['snake_vertices'] == path
        out['runs'][p.name] = [{k:r[k] for k in ('status','path_edges','cycle_lengths') if k in r} for r in d['rounds']]
    source = (HERE/'lean/LocalCycles.lean').read_text(encoding='utf-8')
    encoded = re.search(r'def cycles : List \(List Vertex\) := (\[.*\])',source).group(1)
    assert json.loads(encoded) == cycle_reference
    log = (HERE/'logs/local-cycles.log').read_text(encoding='utf-8')
    assert 'error:' not in log and 'sorryAx' not in log
    audits = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    assert len(audits) == 3
    assert all(set(a.replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'} for _,a in audits)
    out['lean_audits'] = [n for n,_ in audits]
    cap = json.loads((HERE/'data/capacity-audit.json').read_text())
    assert all(t['subsets_examined'] == 262144 and t['matched_table_rows'] == 4973 and
               t['acyclic_rows'] == 4142 and t['max_vertices_by_internal_endpoints'] == [10,14,14] for t in cap['types'])
    source = (HERE/'lean/Capacity.lean').read_text(encoding='utf-8')
    pairs = re.search(r'def profiles : List \(Nat × Nat\) := (\[.*\])',source).group(1)
    assert [[int(a),int(b)] for a,b in re.findall(r'\((\d+),(\d+)\)',pairs)] == cap['profiles']
    log = (HERE/'logs/capacity.log').read_text(encoding='utf-8')
    assert 'error:' not in log and 'sorryAx' not in log
    audits = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    no_axioms = re.findall(r"'([^']+)' does not depend on any axioms",log)
    assert len(audits)+len(no_axioms) == 4
    assert all(set(a.replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'} for _,a in audits)
    out['lean_audits'] += [n for n,_ in audits]+no_axioms
    for name,expected_status in [('positive-control.json','OPTIMAL'),('connected-control.json','OPTIMAL'),
                                 ('cycle-control.json','INFEASIBLE'),('connectivity-rejection-control.json','INFEASIBLE')]:
        assert out['runs'][name][0]['status'] == expected_status
    for p in sorted(HERE.rglob('*')):
        if p.is_file() and p.suffix in ('.py','.lean','.json','.log') and p.name != 'verification.json':
            out['sha256_lf'][p.relative_to(ROOT).as_posix()] = sha(p)
    (HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'status':'PASSED','runs':len(out['runs']),'lean_audits':len(out['lean_audits']),'hashes':len(out['sha256_lf'])}))


if __name__ == '__main__': main()
