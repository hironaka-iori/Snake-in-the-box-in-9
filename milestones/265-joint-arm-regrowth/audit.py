"""Check the constructions, classify completions and independently replay the exchange closure."""
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import gzip
import json

from exchange import input_paths, variants

HERE = Path(__file__).resolve().parent
NEIGHBOURS = [frozenset(v ^ (1 << j) for j in range(8)) for v in range(256)]


def read(name):
    return json.loads((HERE / name).read_bytes())


def verify(path):
    assert len(set(path)) == len(path) and all(0 <= v < 512 for v in path)
    sites = set(path)
    for i, v in enumerate(path):
        adjacent = {v ^ (1 << j) for j in range(9)} & sites
        assert adjacent == set(path[max(0, i-1):i] + path[i+1:i+2])
    return len(path) - 1


def pattern(bits):
    names = {}
    return bytes(names.setdefault(b, len(names)) for b in bits)


def path_class(path):
    steps = [x ^ y for x, y in zip(path, path[1:])]
    return min(pattern(steps), pattern(reversed(steps)))


def chart_class(a, b):
    # Place the crossing at its actual position in the transition word.
    # The unique 9th axis is distinguished by also recording its position.
    def orient(p, q):
        steps = [x ^ y for x, y in zip(p, p[1:])][::-1]
        steps += [512] + [x ^ y for x, y in zip(q, q[1:])]
        return (len(p), pattern(steps))
    return min(orient(a, b), orient(b, a))


def joined(a, b):
    return list(reversed(a)) + [256 + v for v in b]


@lru_cache(maxsize=512)
def edits(arm):
    # Delete an occupied site, add a site, and recover the path from its
    # induced adjacency graph. The traversal also rejects disconnected cycles.
    sites = set(arm)
    base_degree = {v: len(NEIGHBOURS[v] & sites) for v in arm}
    equal = {arm}
    for removed in arm[1:]:
        rest = sites - {removed}
        ends = {0, arm[-1]} | (NEIGHBOURS[removed] & rest)
        ends.discard(removed)
        candidates = set().union(*(NEIGHBOURS[v] for v in ends)) - sites
        for w in candidates:
            hits = NEIGHBOURS[w] & rest
            if not 1 <= len(hits) <= 2 or not hits <= ends:
                continue
            if any(base_degree[v] - (v in NEIGHBOURS[removed]) + (v in hits)
                   > (1 if v == 0 else 2) for v in ends):
                continue
            occupied = rest | {w}
            order = [0]
            seen = {0}
            while True:
                options = (NEIGHBOURS[order[-1]] & occupied) - seen
                if not options:
                    break
                assert len(options) == 1
                v = next(iter(options))
                seen.add(v)
                order.append(v)
            if len(seen) == len(occupied):
                equal.add(tuple(order))
    possibilities = set(equal)
    for p in equal:
        possibilities.add(p[:-1])
        s = set(p)
        if len(p) < 99:
            for w in NEIGHBOURS[p[-1]] - s:
                if NEIGHBOURS[w] & s == {p[-1]}:
                    possibilities.add(p + (w,))
    return [(p, frozenset(p)) for p in possibilities]


def main():
    known = {path_class(p): name for name, p in input_paths()}
    assert Counter(name.split("-")[0] for name in known.values()) == {"190":1042,"191":131}
    ex = read("exchange.json")
    data = (HERE / "exchange-states.json.gz").read_bytes()
    assert sha256(data).hexdigest() == ex["states_sha256"]
    states = [(tuple(bytes.fromhex(a)), tuple(bytes.fromhex(b))) for a,b,parent in json.loads(gzip.decompress(data))]
    ids = {chart_class(a,b):i for i,(a,b) in enumerate(states)}
    assert len(ids) == len(states) == ex["expanded"] == ex["start_charts"]
    archives = dict(input_paths())
    source_charts = set()
    for name, path in archives.items():
        steps = [u ^ v for u,v in zip(path,path[1:])]
        for bit,n in Counter(steps).items():
            if n == 1:
                i = steps.index(bit)
                source_charts.add((name, bit.bit_length()-1))
    assert source_charts == {(s["name"],s["axis"]) for s in ex["starts"]}
    neighbours = set()
    direct_neighbours = set()
    moves = Counter()
    for i,(a,b) in enumerate(states):
        seq = joined(a,b)
        verify(seq)
        seed = ex["starts"][i]
        assert known[path_class(seq)] == seed["name"]
        p = archives[seed["name"]]
        bit = 1 << seed["axis"]
        cut = next(j for j,(u,v) in enumerate(zip(p,p[1:])) if u ^ v == bit)
        assert ids[chart_class(p[:cut+1][::-1],p[cut+1:])] == i
        for left_group in variants(bytes(a)):
            for right_group in variants(bytes(b)):
                for left,s in left_group:
                    for right,t in right_group:
                        if len(left)+len(right)-1 >= 190 and s & t == 1:
                            direct_neighbours.add((i,ids[chart_class(left,right)]))
        for left,s in edits(a):
            for right,t in edits(b):
                if len(left)+len(right)-1 < 190 or s & t != {0}:
                    continue
                j = ids[chart_class(left,right)]
                neighbours.add((i,j))
                moves["labelled"] += 1
                if left != a and right != b:
                    moves["both_changed"] += 1
                if i != j:
                    moves["different_chart"] += 1
    assert moves["labelled"] == ex["pair_visits"]
    assert direct_neighbours == neighbours
    searches = read("conditional-190.json")
    shapes = searches["shapes"]
    complete = {}
    for width, groups in searches["widths"].items():
        totals = Counter()
        names = set()
        accounted = set()
        for row in groups.values():
            k = int(width)
            for entry,axis in row["bank_crossings"]:
                path = archives[f"191-{entry}"]
                cut = next(i for i,(x,y) in enumerate(zip(path,path[1:])) if x ^ y == 1 << axis)
                assert chart_class(path[cut-k:cut+1][::-1],path[cut+1:cut+2+k]) == chart_class(row["A"],row["B"])
                accounted.add((f"191-{entry}",axis))
            for w in row["witnesses"]:
                a = row["A"] + w["tail_A"]
                b = row["B"] + w["tail_B"]
                seq = joined(a,b)
                n = verify(seq)
                word = path_class(seq)
                assert sha256(word).hexdigest() == w["shape"]
                sample = shapes[w["shape"]]
                assert verify(sample["joined"]) == n and path_class(sample["joined"]) == word
                totals[n] += 1
                names.add(known.get(word, w["shape"]))
        assert accounted == {pair for pair in source_charts if pair[0].startswith("191-")}
        complete[width] = dict(classes=len(groups), completed=sum(g["status"]=="complete" for g in groups.values()),
                               completions=totals, distinct=len(names), archive_matches=sum(n in archives for n in names))
    assert complete["38"]["completions"] == {190:56,191:25} and complete["38"]["completed"] == 9
    g = read("growth.json")["runs"]
    p = read("placements.json")
    for r in p["cases"].values():
        assert verify(joined(r["A"],r["B"])) == r["edges"]
    for r in g.values():
        for w in (r["best"], r["both_changed"]):
            if w:
                assert verify(w["joined"]) == w["edges"] and joined(w["A"],w["B"])==w["joined"]
    leader = max((r for r in g.values() if r["mode"]=="fixed"), key=lambda r:r["best"]["edges"])
    w = leader["best"]
    original = p["cases"][leader["seed"]]
    assert w["A"] == original["A"]
    assert all(((u^v).bit_count()==1) == (j==i+1) for (i,u),(j,v) in combinations(enumerate(w["joined"]),2))
    control = next(r for r in g.values() if r["seed"]=="control")["both_changed"]
    global_witness = read("../../outputs/snake9_witness.json")["vertex_sequence"]
    assert verify(global_witness)==191
    paired = sum(r["counts"]["repairs"] for r in g.values())
    output = dict(placement_endpoints=len(p["cases"]), donor_shapes=p["donors"],donor_words=p["directed_words"],
                  placement_histogram=Counter(r["edges"] for r in p["cases"].values()),
                  growth_runs=len(g), collision_repairs=paired, best_fixed_seed=leader["seed"],
                  seed_join_lengths=[original["prior"],original["edges"],w["edges"]], arm_lengths=[len(w[s])-1 for s in ("A","B")],
                  independent_witness_pairs=len(w["joined"])*(len(w["joined"])-1)//2,
                  altered_191_control_archive=known[path_class(control["joined"])],central_segments=complete,
                  exchange=dict(charts=len(ids),checked_moves=moves,distinct_directed_pairs=len(neighbours),closed=True,
                                transitions_sha256=sha256(json.dumps(sorted(neighbours),separators=(",",":")).encode()).hexdigest()),
                  source_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    for name, obj in (("best-open-join.json",dict(seed=leader["seed"],**w)),("summary.json",output)):
        (HERE/name).write_text(json.dumps(obj,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps(output,indent=2))


if __name__ == "__main__":
    main()
