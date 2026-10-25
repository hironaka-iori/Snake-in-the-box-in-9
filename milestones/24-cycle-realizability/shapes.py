"""Shape semantics of the L7 direction automata (gen_lean_automaton5/6.py, refine.py).

A state's direction part is canon(x_{t-6..t}), the restricted-growth relabelling of the
last 7 concrete directions.  A transition appends one label d and moves to
canon(window[1:] + (d,)).  Along a walk of shapes the concrete continuation is therefore
forced up to one choice per step:
  * the new label is one of the window's labels that survive (positions 1..6): the new
    direction must equal x_{t-delta}, delta = 7 - (last position of that label);
  * otherwise (a new RGS symbol): the new direction is any of the 9 coordinates not among
    the last 6 directions (it may equal the direction 7 back, which leaves the window).
"""
import json, os, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
UNROLL = os.environ.get('UNROLL_BIN', os.path.join(HERE, 'unroll'))


def canon(ds):
    m, r = {}, []
    for d in ds:
        m.setdefault(d, len(m)); r.append(m[d])
    return tuple(r)


def rule(src, dst):
    """Rule (0 = fresh, delta = repeat) of the transition src -> dst between 7-shapes."""
    src, dst = tuple(src), tuple(dst)
    hits = []
    for d in range(max(src) + 2):
        if canon(src[1:] + (d,)) == dst:
            hits.append(d)
    assert hits, (src, dst)
    tail = src[1:]
    rules = set()
    for d in hits:
        if d in tail:
            i = len(tail) - 1 - tail[::-1].index(d)      # last position in tail
            rules.add(6 - i)                              # = 7 - position in src
        else:
            rules.add(0)
    assert len(rules) == 1, (src, dst, rules)
    return rules.pop()


def rules_of_cycle(states):
    p = len(states)
    return [rule(states[i], states[(i + 1) % p]) for i in range(p)]


def minimal_period(states):
    p = len(states)
    for q in range(1, p + 1):
        if p % q == 0 and all(tuple(states[i]) == tuple(states[(i + q) % p]) for i in range(p)):
            return q
    return p


def unroll(states, phase=0, limit=0):
    """L_max (transitions) of the cyclic shape walk entered at `phase`."""
    p = len(states)
    st = [tuple(states[(phase + i) % p]) for i in range(p)]
    rs = rules_of_cycle(st)
    args = [UNROLL, str(p)] + [str(a) for a in st[0]] + [str(r) for r in rs]
    if limit:
        args.append(str(limit))
    out = subprocess.run(args, capture_output=True, text=True, check=True).stdout
    res = json.loads(out)
    res['rules'] = rs
    return res


def check_sequence(seq, states, phase=0):
    """Independent re-check: seq follows the shapes from `phase` and is an induced path."""
    p = len(states)
    n = len(seq) - 7
    for t in range(n + 1):
        assert canon(seq[t:t + 7]) == tuple(states[(phase + t) % p]), t
    vs = [0]
    for d in seq:
        vs.append(vs[-1] ^ (1 << d))
    assert len(set(vs)) == len(vs)
    for j in range(len(vs)):
        for i in range(j - 1):
            assert bin(vs[i] ^ vs[j]).count('1') >= 2
    return True
