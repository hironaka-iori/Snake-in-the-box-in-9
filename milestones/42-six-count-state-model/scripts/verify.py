"""Check the saved exact graph certificate independently of cycle optimization."""
from pathlib import Path
from fractions import Fraction
import gzip, hashlib, json, re, sys
ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'work/solver_packages'))
import numpy as np

def sha(b): return hashlib.sha256(b).hexdigest()
def canon(word):
    labels = {}
    return tuple(labels.setdefault(x, len(labels)) for x in word)
def encode(word):
    n = 0
    for c in word: n = 6*n+c-1
    return n

meta = json.loads((HERE/'data/model.json').read_text())
result = json.loads((HERE/'data/analysis.json').read_text())
graph = np.load(HERE/'build/graph.npz')
for name, digest in meta['arrays_sha256'].items():
    assert sha(graph[name].tobytes()) == digest, name
raw = gzip.decompress((HERE/'data/potential.i64.gz').read_bytes())
assert sha(raw) == result['potential_sha256']
potential = np.frombuffer(raw, dtype='<i8')
assert len(potential) == meta['states']
assert int(potential.min()) == 0 and int(potential.max()) == 8064
keep = ~graph['excluded']
u, v = graph['U'][keep], graph['V'][keep]
w = 168*graph['count'][keep].astype(np.int64)+24*graph['demand'][keep]+42*graph['share'][keep]
assert len(u) == 4561226
assert np.all(7056+potential[v] <= 11*w+potential[u])
shapes = {tuple(s): i for i, s in enumerate(meta['direction_shapes'])}
cycle = result['cycle']
assert len(cycle) == 11
for i, row in enumerate(cycle):
    ds, cs = row['directions'], row['counts']
    s = shapes[canon(ds[:7])]*6**6+encode(cs[:6])
    t = shapes[canon(ds[1:])]*6**6+encode(cs[1:])
    assert (s,t) == (row['state'],row['next_state'])
    assert t == cycle[(i+1)%len(cycle)]['state']
    mask = keep & (graph['U'] == s) & (graph['V'] == t)
    indices = np.flatnonzero(mask)
    assert any(meta['extensions'][int(graph['direction'][j])] == ds and
               int(graph['count_code'][j]) == encode(cs) and
               int(graph['demand'][j]) == row['demand'] == 0 and
               int(graph['share'][j]) == row['share_event'] == 0
               for j in indices)
    assert row['weight'] == 168*cs[-1]
assert Fraction(sum(r['weight'] for r in cycle), 168*len(cycle)) == Fraction(42,11)
log = (HERE/'logs/CommonBudget.log').read_text(encoding='utf-8-sig')
audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.S)
assert len(audits) == 2
for _, axioms in audits:
    assert set(x.strip() for x in axioms.split(',')) <= {'propext','Classical.choice','Quot.sound'}
assert "'SixCountStateBudget.maximum_demand' does not depend on any axioms" in log
screen = []
for i in range(11):
    data = json.loads((HERE/f'data/screen-{i}.json').read_text())
    screen.append(data)
receipt = dict(status='PASS', edges_checked=len(u), cycle_length=11,
    normalized_mean='42/11', potential_range=8064, lean_accounting_audits=3,
    graph_array_hashes=meta['arrays_sha256'], potential_sha256=sha(raw),
    scope='Independent integer verification of the saved finite graph and cycle. Graph generation and its complete arbitrary-snake bridge are not Lean checked. Numerical window screens are not refutation certificates.')
(HERE/'data/verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='graph_array_hashes'},indent=2))
