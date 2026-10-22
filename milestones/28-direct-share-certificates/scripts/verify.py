"""Independent integer/graph checks of the saved evidence; no solver imports."""
import gzip, hashlib, itertools, json
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
def read(name): return json.loads((HERE/name).read_text(encoding='utf-8'))
def canon(ds):
    seen = {}; out = []
    for d in ds:
        if d not in seen: seen[d] = len(seen)
        out.append(seen[d])
    return tuple(out)
def key(ds, bounds):
    bs=tuple(map(tuple,bounds))
    return min((canon(ds),bs),(canon(ds[::-1]),bs[::-1]))
def neighbors(v): return [v ^ (1 << j) for j in range(9)]
def components(S):
    unseen = set(S); out = []
    while unseen:
        stack = [next(iter(unseen))]; part = set()
        while stack:
            v = stack.pop()
            if v not in unseen: continue
            unseen.remove(v); part.add(v)
            stack.extend(w for w in neighbors(v) if w in unseen)
        out.append(part)
    return out
def check_cut(cc):
    C = set(cc)
    assert len(C) == len(cc) and len(components(C)) == 1
    assert all(sum(w in C for w in neighbors(v)) == 2 for v in C)
def census(row):
    S = set(row['selected']); dirs = row['dirs']; W = [0]
    for j in dirs: W.append(W[-1] ^ (1 << j))
    centres = W[1:-1]
    B = {v for v in range(512) if min((v ^ w).bit_count() for w in centres) <= 4}
    interior = {v for v in B if set(neighbors(v)) <= B}
    degree = {v: sum(w in S for w in neighbors(v)) for v in range(512)}
    assert len(S) == len(row['selected']) and S <= B and set(W) <= S
    assert all(degree[v] <= 2 for v in S)
    assert all(degree[v] >= 1 for v in S & interior)
    ends = sorted(v for v in S & interior if degree[v] == 1)
    assert len(ends) <= 2
    assert all(any(degree[v] != 2 for v in part) for part in components(S))
    pairs = list(itertools.combinations(range(9), 2))
    def other(v,a,b): return (v ^ (1<<a), v ^ (1<<b), v ^ (1<<a) ^ (1<<b))
    alpha = [sum(all(w not in S for w in other(c,a,b)) for a,b in pairs) for c in centres]
    bounds = row.get('bounds', row.get('alpha'))
    assert all(lo <= v <= hi for v,(lo,hi) in zip(alpha,bounds))
    share = []
    for c in centres:
        total = 0
        for q in neighbors(c):
            assert degree[q] > 0
            squares = [(q, *other(q,a,b)) for a,b in pairs]
            assert all(set(sq) <= B for sq in squares)
            e = sum(not S.intersection(sq) for sq in squares)
            total += 12 * e // degree[q]
        share.append(total)
    return dict(alpha=alpha,share=share,total_share=sum(share),cycles=[],
                selected_vertices=len(S),ball_vertices=len(B),interior_endpoints=ends)
def data_bytes(name):
    p = HERE/'certificates'/name
    return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
def clauses(name):
    return [list(map(int,l.split()))[:-1] for l in data_bytes(name).decode().splitlines()
            if l.strip() and not l.startswith(('p','c'))]

def main():
    for row in read('data/upstream.json')['files']:
        p = HERE/'upstream'/Path(row['path']).name
        assert hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest() == row['sha256_lf']
    controls = read('data/controls.json')
    assert controls['status'] == 'PASSED' and len(controls['cases']) == 56
    assert read('data/assignment-controls.json')['status'] == 'PASSED'
    cycle_count = 0
    for name in ['data/plain-screen.json','data/obstruction-probes.json']:
        records = read(name); assert records['complete'] and len(records['rows']) == 11
        for row in records['rows']:
            for cc in row.get('cycle_cuts',[]): check_cut(cc); cycle_count += 1
            if row['status'] == 'SAT': census(row)
    for name in ['share163','share301','share245','pair10']:
        row = read('data/'+name+'.json')
        assert row['script_sha256_lf'] == hashlib.sha256((HERE/'scripts/direct.py').read_bytes().replace(b'\r\n',b'\n')).hexdigest()
        for cc in row.get('cycle_cuts',[]): check_cut(cc); cycle_count += 1
    w = read('certificates/share1.json'); report = census(w)
    for cc in w['cycle_cuts']: check_cut(cc); cycle_count += 1
    assert report == read('data/share1-independent.json')
    assert report['total_share'] == 104 <= w['cap']

    obstruction = read('data/cache-obstruction.json'); rows = obstruction['records']; n = len(rows)
    forbidden = {key(d,a) for d,a in read('data/exclusion-keys.json')}
    lower = {}
    for name in ['threshold_results.jsonl','ceiling_results.jsonl','probe_results.jsonl','refshare_results.jsonl']:
        for line in (HERE.parent/'27-empty-square-packing/upstream'/name).read_text().splitlines():
            if not line.strip(): continue
            r=json.loads(line)
            if r.get('M',12)!=12 or len(r['dirs'])!=6 or r.get('status')=='UNSAT_MODEL': continue
            al=r.get('alpha') or [(6,21) if s=='6+' else (int(s),int(s)) for s in r['alpha_req'].split(',')]
            b=(r['T'] if r['result']=='UNSAT' else 0) if 'result' in r else r.get('min_lower',0)
            kk=key(r['dirs'],al);lower[kk]=max(lower.get(kk,0),b)
    for i,r in enumerate(rows):
        assert r['next_state'] == rows[(i+1)%n]['state']
        ds = r['directions']; counts = r['state'][1]+[r['alpha']]
        assert tuple(r['state'][0]) == canon(ds[:-1])
        assert tuple(r['next_state'][0]) == canon(ds[1:])
        assert r['next_state'][1] == counts[1:]
        W = [0]
        for j in ds: W.append(W[-1] ^ (1<<j))
        assert len(W) == len(set(W))
        assert all((W[j]^W[k]).bit_count()!=1 for j in range(len(W)) for k in range(j+2,len(W)))
        for k in range(2,6):
            b = [(a,a) if a<6 else (6,21) for a in counts[-k:]]
            assert key(ds[-k-1:],b) not in forbidden
        assert r['share'] == r['five_window_bound'] == 0
        assert lower.get(key(*r['five_window_key']),0)==0
    assert Fraction(sum(r['alpha'] for r in rows),n) == Fraction(42,11) < Fraction(19,4)

    full = clauses('obstruction0.cnf'); compact = clauses('plain0.cnf')
    meta = read('data/plain0.json'); rename = {int(k):v for k,v in meta['original_to_new'].items()}
    with gzip.open(HERE/'certificates/obstruction0.meanings.json.gz','rt') as f: meanings = json.load(f)
    selected = [full[i-1] for i in meta['source_original_clause_ids']]
    assert all(meanings['tags'][i-1][0] == 'old' for i in meta['source_original_clause_ids'])
    assert [[(1 if v>0 else -1)*rename[abs(v)] for v in cl] for cl in selected] == compact
    assert len(compact) == 1795 and meta['active_variables'] == 1134
    for file, expected in [('WindowExclusion.log',2),('share-arithmetic.log',3)]:
        audit=(HERE/'logs'/file).read_text(encoding='utf-8')
        assert audit.count('depends on axioms:') == expected
        assert all(x not in audit for x in ('sorryAx','error:','Lean.ofReduceBool'))
    result = dict(status='PASSED',fixed_model_controls=56,local_sat_witnesses=3,
                  saved_cycle_cuts_checked=cycle_count,plain_core_clauses=1795,
                  audited_new_theorems=5,share_counterexample=report)
    (HERE/'data/verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
if __name__ == '__main__': main()
