"""Floors of the combined weight on known sets (stage C).

For a vertex set S of Q9 and each x in S:
  alpha(x)  singleton squares at x,
  share(x)  sum over unselected neighbours q of floor(12 e0(q) / d(q))  (wincert_share.share_exact),
  c(x)      sum over 3-subcubes Q containing x of floor(12 / |Q cap S|).
A local method that cannot tell S from a snake cannot prove a per-vertex mean of
g = (24 alpha + share) + beta c above the mean over S, so the combined identity
  sum g + 840 v <= 221136 + beta 64512
caps it at v_floor(beta) = (221136 + 64512 beta) / (mean g + 840), m_floor = v_floor - 1.
usage: adversary.py   (bank snakes: work/bank9.json if present)
"""
import itertools, json, os, sys
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
N = 9
SQ = list(itertools.combinations(range(N), 2))
CU = list(itertools.combinations(range(N), 3))


def quantities(S):
    S = set(S)
    out = []
    for x in sorted(S):
        al = 0
        for a, b in SQ:
            Q = {x, x ^ 1 << a, x ^ 1 << b, x ^ 1 << a ^ 1 << b}
            if len(Q & S) == 1:
                al += 1
        sh = 0
        for k in range(N):
            q = x ^ 1 << k
            if q in S:
                continue
            e0 = sum(1 for a, b in SQ if not ({q, q ^ 1 << a, q ^ 1 << b, q ^ 1 << a ^ 1 << b} & S))
            d = sum(1 for t in range(N) if q ^ 1 << t in S)
            sh += (12 * e0) // d
        c = 0
        for a, b, cc in CU:
            Q = {x ^ (i & 1) << a ^ (i >> 1 & 1) << b ^ (i >> 2 & 1) << cc for i in range(8)}
            c += 12 // len(Q & S)
        out.append((al, sh, c))
    return np.array(out)


def floors(q, betas):
    g0 = (24 * q[:, 0] + q[:, 1]).mean(); c = q[:, 2].mean()
    return {str(b): round((221136 + 64512 * b) / (g0 + b * c + 840) - 1, 2) for b in betas}, g0, c


def main():
    betas = [0, 0.05, 0.1, 0.2, 0.5, 1, 2, 5, 1000]
    res = {}
    for name in ('adversary208', 'adversary224'):
        S = json.load(open(os.path.join(ROOT, 'milestones', '11-local-ceiling', 'data', name + '.json')))['S']
        q = quantities(S)
        fl, g0, c = floors(q, betas)
        res[name] = dict(v=len(S), mean_alpha=q[:, 0].mean(), mean_share=q[:, 1].mean(), mean_c=c,
                         mean_24a_share=g0, m_floor=fl)
        print(name, json.dumps(res[name]), flush=True)
    bank = os.path.join(ROOT, 'work', 'bank9.json')
    if os.path.exists(bank):
        B = json.load(open(bank))
        snakes = B if isinstance(B, list) else B.get('snakes', [])
        qs = []
        for s in snakes[:20]:
            S = s['vertex_sequence']
            qs.append(quantities(S))
        q = np.concatenate(qs)
        fl, g0, c = floors(q, betas)
        res['bank20'] = dict(mean_alpha=q[:, 0].mean(), mean_share=q[:, 1].mean(), mean_c=c, m_floor=fl)
        print('bank (first 20)', json.dumps(res['bank20']), flush=True)
    json.dump(res, open(os.path.join(HERE, 'data', 'c_adversaries.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
