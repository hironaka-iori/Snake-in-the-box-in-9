"""Independent audit: the clause lists G* in <Mod>/Inputs.lean are exactly the CNF clauses listed
in `idx` (of data/<tag>.cnf, sha256 printed), with matching kinds; prints the used-clause sha256."""
import re, hashlib, json, sys
for tag, mod in [('w223_rep', 'W223Rep'), ('w223_dis', 'W223Dis')]:
    raw = open(f'data/{tag}.cnf', 'rb').read()
    cls = [list(map(int, l.split()))[:-1] for l in raw.decode().splitlines() if l and l[0] not in 'pc']
    s = open(f'{mod}/Inputs.lean').read()
    G = {}
    for k, body in re.findall(r'^def G(\d+) : CNF := \[(.*)\]$', s, re.M):
        G[int(k)] = [[int(x) if a == 'pos' else -int(x) for a, x in re.findall(r'(pos|neg) (\d+)', c)]
                     for c in re.findall(r'\[([^\[\]]*)\]', body)]
    F = [c for k in sorted(G) for c in G[k]]
    idx = list(map(int, re.search(r'^def idx : List Nat := \[(.*)\]$', s, re.M).group(1).split(', ')))
    kinds = re.findall(r'"([^"]*)"', re.search(r'^def kinds : List String := \[(.*)\]$', s, re.M).group(1))
    meta = json.load(open(f'data/{tag}.meta.json'))
    assert len(F) == len(idx) == len(kinds) and idx == sorted(set(idx))
    assert all(F[j] == cls[i-1] and kinds[j] == meta['kinds'][i-1] for j, i in enumerate(idx))
    assert re.search(r'^def F : CNF := G0 \+\+ \(G1', s, re.M) and len(G) == max(G) + 1
    usha = hashlib.sha256(''.join(' '.join(map(str, c)) + ' 0\n' for c in F).encode()).hexdigest()
    print(tag, 'OK', len(F), 'of', len(cls), 'clauses; cnf sha256', hashlib.sha256(raw).hexdigest(), 'used sha256', usha, usha in s)
