"""Controls for work/snake_dfs.c (implementation evidence, not proofs).

1. Exact maxima in Q3..Q6 from vertex 0 (known values 4, 7, 13, 26 edges), with and
   without the leaf-peeling bound, both feasible and infeasible directions.
2. Independent pure-Python exhaustive regrowth on random small-cube prefixes compared
   with the C search, outcome by outcome.
3. Q9 sanity: each bank snake regrows to its own length from a long prefix.
"""
import json, os, random, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = os.environ.get('SNAKE_DFS', str(ROOT / 'work' / 'snake_dfs'))


def c_regrow(n, snake, keep, target, peel=True):
    env = dict(os.environ)
    if not peel:
        env['SNAKE_NO_PEEL'] = '1'
    out = subprocess.run([str(x) for x in (BIN, 'regrow', n, keep, target, 10**12, -1, 1)], text=True, capture_output=True,
                         input=f"{len(snake)} {' '.join(map(str, snake))}\n", env=env, check=True).stdout
    return json.loads(out.splitlines()[0])['status']


def py_max_extension(n, prefix):
    """Plain exhaustive DFS, no pruning: longest induced extension of prefix."""
    nb = [[v ^ (1 << k) for k in range(n)] for v in range(1 << n)]
    used = set(prefix)
    ban = set(prefix)
    for v in prefix[:-1]:
        ban.update(nb[v])
    best = len(prefix)

    def dfs(head, length, ban):
        nonlocal best
        best = max(best, length)
        for x in nb[head]:
            if x not in ban:
                dfs(x, length + 1, ban | set(nb[head]) | {head})
    dfs(prefix[-1], len(prefix), ban)
    return best


def random_snake(n, rng, length):
    nb = [[v ^ (1 << k) for k in range(n)] for v in range(1 << n)]
    s = [0]
    ban = {0}
    while len(s) < length:
        opts = [x for x in nb[s[-1]] if x not in ban]
        if not opts:
            break
        x = rng.choice(opts)
        ban |= set(nb[s[-1]]) | {s[-1]}
        s.append(x)
    return s


def main():
    rows, ok = [], True
    for n, best in [(3, 5), (4, 8), (5, 14), (6, 27)]:
        for peel in (True, False):
            a = c_regrow(n, [0], 1, best, peel)
            b = c_regrow(n, [0], 1, best + 1, peel)
            good = a == 'FOUND' and b == 'INFEASIBLE'
            ok &= good
            rows.append({'test': 'exact maximum', 'n': n, 'vertices': best, 'peel': peel, 'found_max': a,
                         'beyond_max': b, 'pass': good})
    rng = random.Random(20261015)
    agree = 0
    for t in range(300):
        n = rng.choice([4, 5])
        s = random_snake(n, rng, rng.randint(2, 8))
        m = py_max_extension(n, s)
        for target in (m, m + 1):
            expect = 'FOUND' if target <= m else 'INFEASIBLE'
            got = c_regrow(n, s, len(s), target)
            agree += got == expect
            if got != expect:
                ok = False
                rows.append({'test': 'random prefix mismatch', 'n': n, 'prefix': s, 'target': target, 'got': got})
    rows.append({'test': 'random prefixes vs Python', 'comparisons': 600, 'agreements': agree})
    bank = [e['vertex_sequence'] for e in json.loads((ROOT / 'work' / 'bank9.json').read_text())]
    q9 = sum(c_regrow(9, s, 150, 192) == 'FOUND' for s in bank)
    ok &= q9 == len(bank)
    rows.append({'test': 'Q9 bank regrows to 192 vertices from 150', 'passed': q9, 'total': len(bank)})
    report = {'all_passed': ok, 'rows': rows}
    (ROOT / 'outputs' / 'dfs_controls.json').write_text(json.dumps(report, indent=1), encoding='utf-8')
    print(json.dumps(report if not ok else {'all_passed': ok, 'tests': len(rows)}, indent=1))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
