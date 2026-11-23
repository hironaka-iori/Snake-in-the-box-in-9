import argparse
import collections
import itertools
import json
import random
import time
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

BASE = Path(__file__).resolve().parent
SOURCE = BASE.parent / 'q9_q5_coupled_20261121'
N = [[x ^ (1 << d) for d in range(5)] for x in range(32)]


def local_bound():
    masks = [sum(1 << y for y in neighbors) for neighbors in N]
    counts = collections.Counter()
    def walk(x, used, length):
        counts[length] += 1
        for y in N[x]:
            if (1 << y) & used == 0 and masks[y] & used == 1 << x:
                walk(y, used | (1 << y), length + 1)
    walk(0, 1, 1)
    assert max(counts) == 14
    return counts


def layer_order(word):
    order = [0]
    for d in word:
        order.append(order[-1] ^ (1 << int(d)))
    assert len(set(order)) == 16
    return order


def verify(path, word):
    assert len(path) == len(set(path)) and all(0 <= v < 512 for v in path)
    assert [k for k, g in itertools.groupby(v >> 5 for v in path)] == layer_order(word)
    assert all(((v ^ u).bit_count() == 1) == (j == i + 1)
               for i, v in enumerate(path) for j, u in enumerate(path) if i < j)
    return len(path) - 1


def seeds():
    frozen = BASE / "seed_paths.json"
    if frozen.exists():
        return json.loads(frozen.read_text())
    best = {}
    for log in sorted(SOURCE.glob('*.log')):
        for row in log.read_text().splitlines():
            parts = row.split()
            if not parts or parts[0] != 'BEST':
                continue
            word, path = parts[2], list(map(int, parts[5:]))
            if len(path) <= len(best.get(word, [])):
                continue
            assert verify(path, word) == int(parts[1])
            best[word] = path
    return best


class Model:
    def __init__(self, word, target):
        self.top = 0
        self.clauses = []
        self.order = layer_order(word)
        self.x = [self.row() for i in range(16)]
        self.junction = [self.row() for i in range(15)]
        self.ends = {0: self.row(), 15: self.row()}
        for row in [*self.junction, *self.ends.values()]:
            self.one(row)
        for i in range(16):
            for j in range(i + 1, 16):
                if (self.order[i] ^ self.order[j]).bit_count() != 1:
                    continue
                for k, (a, b) in enumerate(zip(self.x[i], self.x[j])):
                    if j > i + 1:
                        self.clauses.append([-a, -b])
                    else:
                        cross = self.junction[i][k]
                        self.clauses.extend([[-cross, a], [-cross, b], [cross, -a, -b]])
        for i, row in enumerate(self.x):
            for k, v in enumerate(row):
                sides = [row[t] for t in N[k]]
                if i:
                    sides.append(self.junction[i - 1][k])
                if i < 15:
                    sides.append(self.junction[i][k])
                if i in self.ends:
                    e = self.ends[i][k]
                    self.clauses.append([-e, v])
                    sides.append(e)
                # An endpoint flag contributes a dummy incident edge.
                self.clauses.extend([[-v, -a, -b, -c] for a, b, c in itertools.combinations(sides, 3)])
                self.clauses.extend([[-v] + sides[:j] + sides[j+1:] for j in range(len(sides))])
        deficits = []
        for row in self.x:
            # Descending sorting network; bit k denotes at least k+1 colours.
            wires = list(row)
            width = 2
            while width <= 32:
                step = width // 2
                while step:
                    for a in range(32):
                        b = a ^ step
                        if b <= a:
                            continue
                        p, q = wires[a], wires[b]
                        hi, lo = self.var(), self.var()
                        self.clauses.extend([[-p, hi], [-q, hi], [p, q, -hi],
                                             [p, -lo], [q, -lo], [-p, -q, lo]])
                        wires[a], wires[b] = (hi, lo) if not a & width else (lo, hi)
                    step //= 2
                width *= 2
            self.clauses.append([-wires[14]])
            deficits.extend(-v for v in wires[:14])
        cap = CardEnc.atmost(deficits, bound=224 - target, top_id=self.top, encoding=EncType.seqcounter)
        self.top = cap.nv
        self.clauses.extend(cap.clauses)

    def var(self):
        self.top += 1
        return self.top

    def row(self):
        return [self.var() for _ in range(32)]

    def one(self, row):
        cnf = CardEnc.equals(row, 1, top_id=self.top, encoding=EncType.seqcounter)
        self.top = cnf.nv
        self.clauses.extend(cnf.clauses)

    def decode(self, positives):
        vertices = {(self.order[i] << 5) | k for i, row in enumerate(self.x)
                    for k, v in enumerate(row) if v in positives}
        graph = {v: [v ^ (1 << j) for j in range(9) if v ^ (1 << j) in vertices] for v in vertices}
        endpoints = [v for v, ns in graph.items() if len(ns) == 1]
        assert len(endpoints) == 2 and all(len(ns) in (1, 2) for ns in graph.values())
        start = next(v for v in endpoints if v >> 5 == self.order[0])
        path = [start]
        while True:
            choices = [u for u in graph[path[-1]] if len(path) == 1 or u != path[-2]]
            if not choices:
                break
            path.append(choices[0])
        remainder = vertices - set(path)
        cuts = []
        while remainder:
            stack = [remainder.pop()]
            component = []
            while stack:
                v = stack.pop()
                component.append(v)
                for u in graph[v]:
                    if u in remainder:
                        remainder.remove(u)
                        stack.append(u)
            # A full induced cycle saturates the degree at every vertex.
            cuts.append([-self.x[self.order.index(v >> 5)][v & 31] for v in component])
        return path, cuts


def run(word, target, seedword, seed, pins, budget):
    start = time.monotonic()
    model = Model(word, target)
    seedorder = layer_order(seedword)
    masks = [{v & 31 for v in seed if v >> 5 == a} for a in seedorder]
    phases = [v if k in masks[i] else -v for i, row in enumerate(model.x) for k, v in enumerate(row)]
    rng = random.Random(71031)
    fixed = [v for i, row in enumerate(model.x) for v in rng.sample(
        [row[k] for k in sorted(masks[i])], min(pins, len(masks[i])))]
    cuts = 0
    with Solver(name='cadical195', bootstrap_with=model.clauses) as solver:
        solver.set_phases(phases)
        solver.conf_budget(budget)
        while True:
            ret = solver.solve_limited(assumptions=fixed)
            if ret is not True:
                status = 'UNSAT' if ret is False else 'UNKNOWN'
                break
            path, invalid = model.decode(set(solver.get_model()))
            if not invalid:
                assert verify(path, word) >= target - 1
                status = 'SAT'
                break
            for clause in invalid:
                solver.add_clause(clause)
            cuts += len(invalid)
            remaining = budget - solver.accum_stats()['conflicts']
            if remaining <= 0:
                status = 'UNKNOWN'
                break
            solver.conf_budget(remaining)
        stats = solver.accum_stats()
    return dict(word=word, target_vertices=target, seedword=seedword, seed_edges=len(seed)-1,
                positive_pins=len(fixed), status=status, cuts=cuts, conflicts=stats['conflicts'],
                seconds=round(time.monotonic()-start,3), path=path if status=='SAT' else [])


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', choices=['control','all','seeded'], required=True)
    ap.add_argument('--pins', type=int, default=0)
    ap.add_argument('--budget', type=int, default=500)
    ap.add_argument('--max', type=int, default=98)
    ap.add_argument('--start', type=int, default=0)
    ap.add_argument('--edges', type=int)
    args = ap.parse_args()
    local_bound()
    known = seeds()
    words = (SOURCE/'orders.txt').read_text().split()
    assert len(words) == len(set(words)) == 98
    best = max(known, key=lambda w:len(known[w]))
    if args.mode != 'all':
        words = sorted(known, key=lambda w:(-len(known[w]),w))
    for word in words[args.start:args.start+args.max]:
        seedword = word if word in known else best
        target = args.edges+1 if args.edges else (len(known[word]) if args.mode=='control' else 193)
        print(json.dumps(run(word,target,seedword,known[seedword],args.pins,args.budget)), flush=True)
