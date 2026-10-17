import json, sys, collections, itertools
bank = json.load(open(sys.argv[1]))
L = lambda x: json.loads(x) if isinstance(x, str) else x
def light_coords(t, n):
    c = collections.Counter(t)
    return sorted(range(9), key=lambda k: (c[k], k))[:n]
def outer_transitions(t, light):
    pos = {k: i for i, k in enumerate(light)}
    return [pos[k] for k in t if k in pos]
def canon(seq, n):
    # canonical form under coordinate permutation of the light coords and reversal
    best = None
    for s in (seq, seq[::-1]):
        for perm in itertools.permutations(range(n)):
            m = tuple(perm[k] for k in s)
            if best is None or m < best: best = m
    return best
forms = collections.Counter(); singles = []
for i, e in enumerate(bank):
    t = L(e['transition_sequence'])
    li = light_coords(t, 4)
    forms[canon(outer_transitions(t, li), 4)] += 1
    c = collections.Counter(t)
    if min(c.values()) == 1:
        k = min(range(9), key=lambda k: c[k]); j = t.index(k)
        singles.append((i, j, len(t) - 1 - j))
print('distinct outer (Q4-level) transition words up to symmetry/reversal:', len(forms))
for f, n in forms.most_common(6): print(n, len(f), ''.join(map(str, f)))
print('single-crossing bank snakes (index, layer lengths):', singles)
