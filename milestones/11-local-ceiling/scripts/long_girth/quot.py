"""Translation-symmetric search. Pick a random binary [9,k] code T with min weight >= 3.
S = union of T-cosets; S/T = S' in the quotient Cayley graph on Z2^(9-k) with generators h_i
(columns of a parity-check matrix). deg_S(x) = deg_{S'}([x]); a quotient cycle of length L lifts to
cycles of length L (zero holonomy) or 2L (nonzero holonomy).
SAT on S': induced 2-regular, |S'| >= ceil(target/2^k), every quotient cycle >= ceil(g/2) (label
encoding), lazy cuts for zero-holonomy quotient cycles shorter than g.
usage: python quot.py k g target conf_budget ncodes seed outprefix
"""
import sys, json, itertools, random, time
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
k, g, target, budget, ncodes, seed, outp = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]),
    int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7])
rng = random.Random(seed)
r = 9 - k; NQ = 1 << r

def random_code():
    while True:
        gens = [rng.randrange(1, 512) for _ in range(k)]
        T = {0}
        for gv in gens: T |= {t ^ gv for t in T}
        if len(T) == 1 << k and min(bin(t).count('1') for t in T if t) >= 3: return sorted(T)

def syndrome_map(T):
    # coset representative index: map each x to coset id 0..NQ-1
    cid = {}; reps = []
    for x in range(512):
        if x in cid: continue
        for t in T: cid[x ^ t] = len(reps)
        reps.append(x)
    return cid, reps

def solve_quot(T):
    cid, reps = syndrome_map(T)
    nb = [[cid[reps[q] ^ (1 << i)] for i in range(9)] for q in range(NQ)]
    for q in range(NQ): assert len(set(nb[q])) == 9 and q not in nb[q]
    gq = (g + 1) // 2; M = 2 * gq - 2
    pool = IDPool(); cls = []
    X = lambda q: pool.id(('x', q)); D = lambda a, b: pool.id(('d', a, b)); Y = lambda q, j: pool.id(('y', q, j))
    for w in range(NQ):
        N = nb[w]; outs = [D(w, z) for z in N]; ins = [D(z, w) for z in N]
        cls.append([-X(w)] + outs); cls.append([-X(w)] + ins)
        for a, b in itertools.combinations(outs, 2): cls.append([-a, -b])
        for a, b in itertools.combinations(ins, 2): cls.append([-a, -b])
        for z in N:
            cls.append([-D(w, z), X(w)]); cls.append([-D(w, z), X(z)])
            if z > w: cls.append([-D(w, z), -D(z, w)]); cls.append([-X(w), -X(z), D(w, z), D(z, w)])
            d = D(w, z)
            cls.append([-d, -Y(z, 1), -Y(w, M)])
            for j in range(1, M):
                cls.append([-d, -Y(z, 1), -Y(w, j), Y(z, j + 1)])
                cls.append([-d, -Y(z, 1), Y(w, j), -Y(z, j + 1)])
            cls.append([-d, Y(z, 1), Y(w, gq - 1)])
        for j in range(1, M): cls.append([-Y(w, j + 1), Y(w, j)])
    cls.append([X(0)])
    need = -(-target // (1 << k))
    cls += CardEnc.atleast([X(q) for q in range(NQ)], bound=need, vpool=pool, encoding=EncType.seqcounter).clauses
    s = Solver(name='glucose4', bootstrap_with=cls)
    for it in range(200):
        s.conf_budget(budget)
        res = s.solve_limited()
        if res is not True: return res, None
        m = set(l for l in s.get_model() if l > 0)
        Sq = {q for q in range(NQ) if X(q) in m}
        S = sorted(x for x in range(512) if cid[x] in Sq)
        # lift check: cycle lengths in Q9
        Ss = set(S); seen = set(); badcycles = []
        for x0 in S:
            if x0 in seen: continue
            comp = []; st = [x0]
            while st:
                x = st.pop()
                if x in seen: continue
                seen.add(x); comp.append(x); st += [x ^ 1 << i for i in range(9) if x ^ 1 << i in Ss]
            if len(comp) < g: badcycles.append({cid[x] for x in comp})
        if not badcycles: return True, S
        for qc in badcycles: s.add_clause([-X(q) for q in qc])
    return None, None

t0 = time.time()
for c in range(ncodes):
    T = random_code()
    res, S = solve_quot(T)
    print(f"code {c} T={T} res={res} t={time.time()-t0:.0f}", flush=True)
    if res is True:
        fn = f"{outp}_k{k}_g{g}_{len(S)}_s{seed}c{c}.json"
        json.dump({'S': S, 'T': T, 'k': k, 'g': g}, open(fn, 'w'))
        print("HIT saved", fn, len(S), flush=True)
        break
