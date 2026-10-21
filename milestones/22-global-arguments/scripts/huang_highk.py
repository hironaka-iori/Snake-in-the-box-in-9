"""Huang augmentation restricted to outside vertices with >= kmin snake neighbours:
exact spectral test (lambda_max < 3) and the local Gershgorin test on A_s[U]^2."""
import json, random, os
from huang_aug import n, NV, lam_max, gersh_ok, ball2
root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..') + '/'
bank = json.load(open(root + 'work/bank9.json'))
sets = [('bank0', bank[0]['vertex_sequence'])] + [(nm, json.load(open(root + 'milestones/11-local-ceiling/data/%s.json' % nm))['S']) for nm in ('adversary208', 'adversary224')]
for nm, S in sets:
    for kmin in (2, 3, 4, 5, 6):
        for mode in ('spectral', 'gershgorin'):
            if mode == 'spectral' and nm != 'bank0':
                continue
            best = 0
            for seed in range(2 if mode == 'spectral' else 6):
                rng = random.Random(seed); U = set(S)
                cand = [y for y in range(NV) if y not in U and sum(1 for i in range(n) if y ^ (1 << i) in U) >= kmin]
                rng.shuffle(cand); added = 0
                for _ in range(1 if mode == 'spectral' else 3):
                    for y in cand:
                        if y in U:
                            continue
                        U.add(y)
                        ok = lam_max(U) < 3 - 1e-9 if mode == 'spectral' else gersh_ok(U, ball2(y))
                        if ok: added += 1
                        else: U.remove(y)
                best = max(best, added)
            print(nm, 'kmin', kmin, 'candidates', len(cand), mode, 'added', best, flush=True)
