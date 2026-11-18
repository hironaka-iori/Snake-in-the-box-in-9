"""Seeds for sa: occurrences of a canonical 8-direction shape in real snakes / adversaries,
mapped onto the canonical window (translation + coordinate relabelling)."""
import json, os, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))

def canon(ds):
    m = {}; out = []
    for d in ds:
        if d not in m: m[d] = len(m)
        out.append(m[d])
    return tuple(out), m

def occurrences(seq, S, L=8):
    """yield (canonical dirs, mapped selection) for every window of L directions of path seq,
    both orientations; S = full selected set."""
    for orient in (seq, seq[::-1]):
        dirs = [(orient[i] ^ orient[i+1]).bit_length() - 1 for i in range(len(orient) - 1)]
        for i in range(len(dirs) - L + 1):
            c, m = canon(dirs[i:i+L])
            rest = [d for d in range(9) if d not in m]
            perm = dict(m)
            for d in rest: perm[d] = len(perm)
            x0 = orient[i]
            def mp(v):
                y = v ^ x0; r = 0
                for d in range(9):
                    if y >> d & 1: r |= 1 << perm[d]
                return r
            yield c, [mp(v) for v in S]

def bank_paths():
    for sn in json.load(open(os.path.join(ROOT, 'work', 'bank9.json'))):
        yield sn['vertex_sequence'], sn['vertex_sequence']

def adversary_paths(name):
    """components of a 2-regular adversary as cyclic sequences unrolled (path = cycle + 9 more)."""
    d = json.load(open(os.path.join(ROOT, 'milestones', '11-local-ceiling', 'data', name)))
    S = d['S'] if isinstance(d, dict) and 'S' in d else d.get('vertices', d) if isinstance(d, dict) else d
    S = set(S); seen = set()
    for v in S:
        if v in seen: continue
        cyc = [v]; seen.add(v); prev = None; cur = v
        while True:
            nb = [cur ^ 1 << k for k in range(9) if cur ^ 1 << k in S and cur ^ 1 << k != prev]
            nxt = nb[0] if prev is not None or len(nb) else None
            if prev is None: nxt = nb[0]
            if nxt == v: break
            prev, cur = cur, nxt; cyc.append(cur); seen.add(cur)
        yield cyc + cyc[:10], sorted(S)
