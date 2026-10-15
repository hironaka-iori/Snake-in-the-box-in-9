"""Generate kernel-checked regrowth certificates for the bank (work/final_lean).

For each of the 262 oriented bank snakes, one theorem states that the verified search
`Snake9.Dfs.search` fails from the first KEEP vertices with target 193 vertices; each is
proved by `decide +kernel` (kernel evaluation only, no native code).  The aggregate
theorem `bank_no192_keepKEEP` then follows from `no192_from_prefix`.

Search trees larger than SPLIT nodes are split into child theorems combined with
`search_of_children`, which keeps the kernel's peak memory per theorem small.  Node
counts come from the C search with the reachable-count bound, which is the bound the
Lean checker uses.  Shards are balanced so that `lake build` checks them in parallel.

  python3 work/build_lean_certificates.py --keep 160 --shards 4
  cd work/final_lean && lake build DfsBankCert160
"""
import argparse, json, re, subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / 'work' / 'final_lean'

ap = argparse.ArgumentParser()
ap.add_argument('--keep', type=int, default=160)
ap.add_argument('--shards', type=int, default=4, help='unused; kept for compatibility')
ap.add_argument('--cap', type=int, default=8000, help='cost units (~ nodes) per module')
ap.add_argument('--split', type=int, default=300)
ap.add_argument('--v2', action='store_true',
                help='use search2 (parity + leaf-peeling bound) with literal search states')
a = ap.parse_args()
K, need = a.keep, 193 - a.keep

bank = [e['vertex_sequence'] for e in json.loads((ROOT / 'work' / 'bank9.json').read_text())]
oriented = [r for s in bank for r in (s, s[::-1])]


def c_nodes(paths):
    """Node counts of the Lean search (reachable-count bound) from each path, via the C tool."""
    text = ''.join(f"{len(p)} {' '.join(map(str, p))}\n" for p in paths)
    out = subprocess.run([str(ROOT / 'work' / 'snake_dfs'), 'regrow', '9', '999', '193', str(10**11), '-1', '1'],
                         input=text, capture_output=True, text=True, check=True,
                         env={} if a.v2 else {'SNAKE_COUNT_ONLY': '1'}).stdout
    res = [json.loads(l)['nodes'] for l in out.splitlines() if '"regrow"' in l]
    assert len(res) == len(paths)
    return res


def nbrs(v):
    return {v ^ (1 << k) for k in range(9)}


# Recursively split every search tree larger than SPLIT nodes into child subtrees.
SPLIT = a.split
theorems = {}   # j -> list of (name, lean_text, cost)


def plan(j, path, head_e, ban_e, name, out):
    need = 193 - len(path)
    n = c_nodes([path])[0]
    stmt = f"search {head_e} {ban_e} {need} = false"
    if n <= SPLIT or need <= 1:
        out.append((name, f"theorem {name} : {stmt} := by decide +kernel", n))
        return
    banned = set(path)
    for v in path[:-1]:
        banned |= nbrs(v)
    head = path[-1]
    cases = []
    for k in range(9):
        c = head ^ (1 << k)
        if c in banned:
            cases.append(f"    | {k}, _ => exact Or.inl (by decide +kernel)")
        else:
            child = f"{name}_{k}"
            plan(j, path + [c], f"({head_e} ^^^ 2 ^ {k})", f"({ban_e} ||| cnMask {head_e})", child, out)
            cases.append(f"    | {k}, _ => exact Or.inr {child}")
    body = (f"theorem {name} : {stmt} :=\n  search_of_children {head_e} {ban_e} {need - 1} (fun k hk => by\n"
            f"    match k, hk with\n" + "\n".join(cases) + "\n    | n + 9, h => exact absurd h (by omega))")
    out.append((name, body, 50))



def cn(v):
    m = 1 << v
    for k in range(9):
        m |= 1 << (v ^ (1 << k))
    return m


def plan2(path, H, B, name, out):
    """v2: literal head H and ban mask B at every node."""
    need = 193 - len(path)
    n = c_nodes([path])[0]
    stmt = f"search2 {H} {B} {need} = false"
    if n <= SPLIT or need <= 1:
        out.append((name, f"theorem {name} : {stmt} := by decide +kernel", n))
        return
    B2 = B | cn(H)
    cases = []
    for k in range(9):
        c = H ^ (1 << k)
        if (B >> c) & 1:
            cases.append(f"    | {k}, _ => exact Or.inl (by decide +kernel)")
        else:
            child = f"{name}_{k}"
            plan2(path + [c], c, B2, child, out)
            cases.append(f"    | {k}, _ => exact Or.inr (by\n"
                         f"        rw [show {H} ^^^ 2 ^ {k} = {c} from by decide +kernel,\n"
                         f"          show {B} ||| cnMask {H} = {B2} from by decide +kernel]\n"
                         f"        exact {child})")
    body = (f"theorem {name} : {stmt} :=\n  search2_of_children {H} {B} {need - 1} (fun k hk => by\n"
            f"    match k, hk with\n" + "\n".join(cases) + "\n    | n + 9, h => exact absurd h (by omega))")
    out.append((name, body, 50))


tag = f"{K}v2" if a.v2 else f"{K}"
for j, s in enumerate(oriented):
    out = []
    if a.v2:
        pre = s[:K]
        B = 0
        for v in pre[:-1]:
            B |= cn(v)
        plan2(pre, pre[-1], B, f"keep{tag}_{j}_lit", out)
        out.append((f"keep{tag}_{j}",
                    f"theorem keep{tag}_{j} : search2 (oriented {j})[{K - 1}]! "
                    f"(banFrom (fun i => (oriented {j})[i]!) {K - 1}) {need} = false := by\n"
                    f"  rw [show (oriented {j})[{K - 1}]! = {pre[-1]} from by decide +kernel,\n"
                    f"    show banFrom (fun i => (oriented {j})[i]!) {K - 1} = {B} from by decide +kernel]\n"
                    f"  exact keep{tag}_{j}_lit", 60))
    else:
        plan(j, s[:K], f"(oriented {j})[{K - 1}]!", f"(banFrom (fun i => (oriented {j})[i]!) {K - 1})",
             f"keep{K}_{j}", out)
    theorems[j] = out
nodes = [sum(c for _, _, c in theorems[j]) for j in range(len(oriented))]

# Module layout.  A Lean process keeps its kernel memory until it exits, so every module
# is capped at CAP cost units (~ search nodes).  Instances below the cap are packed
# together; a larger instance is cut into a chain of modules, each importing the previous
# one (its theorems are emitted children first, so every reference points backwards).
CAP = a.cap
cost = {j: sum(60 + c for _, _, c in theorems[j]) for j in theorems}
for old in LEAN.glob(f'DfsBankCert{tag}_*.lean'):
    old.unlink()
base = 'DfsDecide' if a.v2 else 'DfsCertificate'
header = f"""import {base}
import DfsBankData
"""
opts = """
namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
"""
modules = []          # (name, imports, theorem texts)
targets = []          # modules handed to the parallel runner (no two share a dependency)
bins = []             # packed small instances: [load, [texts]]
for j in sorted(theorems, key=lambda j: -cost[j]):
    if cost[j] <= CAP:
        for b in bins:
            if b[0] + cost[j] <= CAP:
                b[0] += cost[j]; b[1] += [t for _, t, _ in theorems[j]]
                break
        else:
            bins.append([cost[j], [t for _, t, _ in theorems[j]]])
    else:
        chunks, cur, load = [], [], 0
        for _, t, c in theorems[j]:
            if cur and load + 60 + c > CAP:
                chunks.append(cur); cur, load = [], 0
            cur.append(t); load += 60 + c
        chunks.append(cur)
        prev = None
        for ci, texts in enumerate(chunks):
            name = f'DfsBankCert{tag}_j{j}c{ci}'
            modules.append((name, [prev] if prev else [], texts))
            prev = name
        targets.append(prev)
for i, (load, texts) in enumerate(bins):
    name = f'DfsBankCert{tag}_g{i}'
    modules.append((name, [], texts))
    targets.append(name)
for name, imps, texts in modules:
    body = header + ''.join(f'import {m}\n' for m in imps) + opts + '\n'.join(texts) + '\n\nend Snake9.Dfs\n'
    (LEAN / f'{name}.lean').write_text(body, encoding='utf-8')
(LEAN / f'DfsBankCert{tag}.targets').write_text('\n'.join(targets) + '\n', encoding='utf-8')
names = [m[0] for m in modules]
load = [cost[j] for j in theorems]

srch = "search2" if a.v2 else "search"
agg = [f"import {n}" for n in targets] + ["", "namespace Snake9.Dfs", "set_option maxRecDepth 100000", ""]
agg.append(f"""theorem search_keep{tag} (j : Nat) (hj : j < {len(oriented)}) :
    {srch} (oriented j)[{K - 1}]! (banFrom (fun i => (oriented j)[i]!) {K - 1}) {need} = false := by
  match j, hj with""")
for j in range(len(oriented)):
    agg.append(f"  | {j}, _ => exact keep{tag}_{j}")
agg.append(f"  | n + {len(oriented)}, h => exact absurd h (by omega)")
agg.append(f"""
/-- No 192-edge snake begins with the first {K} vertices of any bank snake, in either
orientation (entry `2*s` of `oriented` is bank snake `s`, entry `2*s+1` its reversal).
Reversing a snake, this also excludes 192-edge snakes ending in those {K} vertices. -/
theorem bank_no192_keep{tag} (j : Nat) (hj : j < {len(oriented)}) :
    ¬ ∃ p : Snake 192, ∀ i (h : i < {K}), (p.vertex ⟨i, by omega⟩).val = (oriented j)[i]! :=
  {'no192_from_prefix2' if a.v2 else 'no192_from_prefix'} (oriented j) {K} (by decide) (by decide) (search_keep{tag} j hj)

#print axioms bank_no192_keep{tag}
end Snake9.Dfs
""")
(LEAN / f'DfsBankCert{tag}.lean').write_text('\n'.join(agg), encoding='utf-8')

lake = (LEAN / 'lakefile.toml').read_text()
lake = re.sub(r'\n\[\[lean_lib\]\]\nname = "DfsBankCert' + re.escape(tag) + r'_[^"]*"\n', '', lake)
for n in names + [f'DfsBankCert{tag}']:
    if f'name = "{n}"' not in lake:
        lake += f'\n[[lean_lib]]\nname = "{n}"\n'
(LEAN / 'lakefile.toml').write_text(lake)
print(f'keep={K}: {len(oriented)} instances, {sum(len(theorems[j]) for j in theorems)} theorems, '
      f'{sum(nodes)} leaf nodes, {len(modules)} modules, {len(targets)} runner targets, '
      f'max instance cost {max(load)}')
