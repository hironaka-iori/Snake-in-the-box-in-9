"""Positive controls for winmin: windows (k centres) cut from genuine snakes, normalised, must be feasible,
both with alpha targets and with the selection fixed to the (transformed) genuine snake inside the ball."""
import sys, json, itertools
sys.dont_write_bytecode = True
from ortools.sat.python import cp_model
import winmin
from verify_real import order_path, alphas

def normalise(seq, i, k):
    """window vertices seq[i-1..i+k] ; return shape, and map phi on all of Q9"""
    p0 = seq[i - 1]
    ts = [(seq[j] ^ seq[j + 1]).bit_length() - 1 for j in range(i - 1, i + k)]
    mp = {}
    for t in ts:
        if t not in mp:
            mp[t] = len(mp)
    rest = [c for c in range(9) if c not in mp]
    for c in rest:
        mp[c] = len(mp)
    def phi(v):
        v ^= p0
        out = 0
        for c in range(9):
            if v >> c & 1:
                out |= 1 << mp[c]
        return out
    return [mp[t] for t in ts], phi

def fixed_check(shape, radius, alpha, fixedset):
    m, x, ball, win, centers, obj, al = winmin.build(shape, radius, alpha)
    for v in ball:
        m.add(x[v] == int(v in fixedset))
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = 60
    return s.status_name(s.solve(m))

if __name__ == '__main__':
    k = int(sys.argv[1]); radius = int(sys.argv[2])
    bank = json.load(open('/home/user/Snake-in-the-box-in-9/work/bank9.json'))
    snakes = [('bank0', bank[0]['vertex_sequence']), ('bank130', bank[130]['vertex_sequence'])]
    for r in json.load(open('real_r9_a.json')):
        snakes.append(('real' + ''.join(map(str, r['alpha'])), order_path(r['selected'])))
    for name, seq in snakes:
        a = alphas(seq)
        # lowest-sum window and two others
        cands = sorted(range(1, len(seq) - k), key=lambda i: sum(a[i:i + k]))[:2] + [len(seq) // 2]
        for i in cands:
            shape, phi = normalise(seq, i, k)
            al = a[i:i + k]
            r = winmin.solve(shape, radius, 60, al, False)
            fx = fixed_check(shape, radius, al, {phi(v) for v in seq})
            print(name, 'pos', i, 'shape', shape, 'alphas', al, 'target-test:', 'FEASIBLE' if r['best'] else r['status'], ' fixed-genuine:', fx, flush=True)
