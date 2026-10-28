"""Compute finite-model means and independently check all-edge integer potentials."""
from pathlib import Path
from fractions import Fraction
import gzip, hashlib, json, sys, time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0, str(ROOT/'milestones/51-exact-bucket-pressure/scripts'))
import analyze_share
np = model.np

def run(name, use_share):
    start = time.monotonic()
    folder = HERE/name
    meta = json.loads((folder/'data/model.json').read_text())
    with np.load(folder/'build/graph.npz') as data:
        a = {k: data[k] for k in data.files}
    U, V = a['U'], a['V']
    W = 120*a['count'].astype(np.int64)+(a['share_lower'] if use_share else 0)
    algorithms, source_sha = analyze_share.algorithms()
    pool = np.flatnonzero(algorithms['prune'](meta['states'], U, V))
    active = np.unique(np.concatenate([U[pool], V[pool]]))
    index = np.full(meta['states'], -1, dtype=np.int32); index[active] = np.arange(len(active))
    mode = 'share' if use_share else 'count'
    print(name, mode, 'cyclic states', len(active), 'edges', len(pool), flush=True)
    _, cycle = algorithms['howard'](len(active), index[U[pool]], index[V[pool]], W[pool], iters=400)
    chosen = pool[np.array(cycle)]
    mean = Fraction(int(W[chosen].sum()), len(chosen))
    assert all(V[e] == U[chosen[(j+1)%len(chosen)]] for j, e in enumerate(chosen))
    print('Candidate', str(mean/120), 'period', len(chosen), flush=True)
    p, q = mean.numerator, mean.denominator
    cost = q*W-p; potential = np.zeros(meta['states'], dtype=np.int64)
    verified = False
    for iteration in range(1500):
        new = potential.copy(); np.minimum.at(new, V, potential[U]+cost)
        if np.array_equal(new, potential):
            verified = True; break
        potential = new
        if iteration % 50 == 0:
            print('Potential iteration', iteration, 'range', int(potential.max()-potential.min()), flush=True)
    assert verified, 'Candidate cycle did not yield an all-edge potential'
    assert np.all(p+potential[V] <= q*W+potential[U])
    potential -= potential.min(); loss = int(potential.max())
    encoded = potential.astype('<i8').tobytes()
    (folder/f'data/potential-{mode}.i64.gz').write_bytes(gzip.compress(encoded, mtime=0))
    records = []
    for e in chosen:
        records.append(dict(state=int(U[e]), next_state=int(V[e]), directions=meta['extensions'][int(a['direction'][e])],
            counts=analyze_share.decode(int(a['count_code'][e]), 6), weight=int(W[e]),
            share_lower=int(a['share_lower'][e]) if use_share else 0))
    # Seven omitted internal counts and two endpoint counts contribute at least
    # 7 + 4 + 4 = 15, hence W + 1800 <= 5G.
    conditional_bound = Fraction(1099680*q+8*p+loss, p+4200*q)
    out = dict(status='EXACT_FINITE_MODEL', mode=mode, states=meta['states'], edges=len(U),
        cyclic_states=len(active), cyclic_edges=len(pool), integer_weight_mean=str(mean),
        normalized_charge_mean=str(mean/120), potential_range=loss, potential_sha256=hashlib.sha256(encoded).hexdigest(),
        potential_iterations=iteration+1, cycle=records, conditional_edge_bound=str(conditional_bound),
        conditional_integer_bound=conditional_bound.numerator//conditional_bound.denominator,
        algorithm_source_sha256=source_sha, seconds=round(time.monotonic()-start, 3),
        scope='Exact finite-model minimum. Numerical exclusion premises and complete graph/overlap/boundary assembly remain separate proof obligations; this is not a new global snake bound.')
    (folder/f'data/analysis-{mode}.json').write_text(json.dumps(out, indent=2)+'\n')
    print({k: v for k, v in out.items() if k != 'cycle'}, flush=True)

if __name__ == '__main__':
    for name in sys.argv[1:] or ['lifted', 'extended']:
        for use_share in [True]:
            run(name, use_share)
