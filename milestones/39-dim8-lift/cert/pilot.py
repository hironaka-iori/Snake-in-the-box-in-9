"""Pilot: turn one cube's LRAT refutation into the repository's v3 replay modules.
1. core = input clauses reachable from the empty clause (in original order, original ids);
2. compact the core's variables to 1..V (new v' stands for old back[v'-1]); rename lemma literals too;
3. write LocalWindowCnf/<Mod>.lean (raw core, decodeLit coding), the renamed LRAT, the core json,
   and <Mod>Glue.lean: back list, core with indices into the full CNF, and the two glue checks.
usage: python3 pilot.py full.cnf proof.lrat Mod outdir"""
import sys, os, json
cnf, lrat, mod, out = sys.argv[1:5]
os.makedirs(os.path.join(out, 'LocalWindowCnf'), exist_ok=True)
ncls = int(open(cnf).readline().split()[3])
lem = {}; order = []
for line in open(lrat):
    p = line.split()
    if p[1] == 'd': continue
    cid = int(p[0]); z = p.index('0', 1)
    lem[cid] = (p[1:z], [int(x) for x in p[z + 1:-1]]); order.append(cid)
last = order[-1]; assert lem[last][0] == []
need = {last}; core = set(); st = [last]
while st:
    c = st.pop()
    for h in lem[c][1]:
        if h <= ncls: core.add(h)
        elif h not in need: need.add(h); st.append(h)
core_ids = sorted(core)
clauses = {}
i = 0
for line in open(cnf):
    if line.startswith('p'): continue
    i += 1
    if i in core: clauses[i] = [int(x) for x in line.split()[:-1]]
vs = sorted({abs(l) for c in clauses.values() for l in c})
new = {v: k + 1 for k, v in enumerate(vs)}
ren = lambda l: new[abs(l)] if l > 0 else -new[abs(l)]
enc = lambda l: 2 * abs(l) + (0 if l > 0 else 1)
def natpack(xs):
    """NatPack chunks (work/final_lean/NatPack.lean): n + 2^8 (w + 2^16 (z + 2^n st))."""
    out = []
    for k in range(0, len(xs), 255):
        ch = xs[k:k + 255]; n = len(ch)
        w = max([x.bit_length() for x in ch] + [1])
        z = 0; st = 0; pos = 0
        for i, x in enumerate(ch):
            if x == 0: z |= 1 << i
            else: st |= x << pos; pos += w
        out.append(n + (w << 8) + (z << 24) + (st << (24 + n)))
    return out
flat = []
for c in core_ids:
    flat += [enc(ren(l)) for l in reversed(clauses[c])] + [0]
chunks = natpack(flat)
with open(os.path.join(out, 'LocalWindowCnf', mod + '.lean'), 'w') as f:
    f.write("import LocalWindowModel\nimport SplitZ\n/-! Compacted UNSAT core of cube %s: %d of %d clauses, %d variables (renamed), NatPack-packed. -/\n"
            "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Snake9.LocalWindow.%s\n" % (mod, len(core_ids), ncls, len(vs), mod))
    f.write("noncomputable def raw : List (List Nat) := Snake9.SplitZ.splitZ (Snake9.NatPack.unpackL [\n%s])\n" % ",\n".join(map(str, chunks)))
    f.write("noncomputable def cnf : List (List Int) := raw.map (·.map decodeLit)\nend Snake9.LocalWindow.%s\n" % mod)
# renamed LRAT, keeping only needed lemmas (others dropped; ids unchanged)
with open(os.path.join(out, mod + '.lrat'), 'w') as f:
    for cid in order:
        if cid not in need: continue
        lits, hints = lem[cid]
        f.write('%d %s 0 %s 0\n' % (cid, ' '.join(str(ren(int(l))) for l in lits), ' '.join(map(str, hints))))
os.makedirs(os.path.join(out, 'core'), exist_ok=True)
json.dump(dict(module='Snake9.LocalWindow.' + mod, core_ids=core_ids), open(os.path.join(out, 'core', mod + '.json'), 'w'))
json.dump(dict(back=vs, core_ids=core_ids, nvars=len(vs)), open(os.path.join(out, mod + '.glue.json'), 'w'))
print(json.dumps(dict(core=len(core_ids), vars=len(vs), lemmas=len(need), hints=sum(len(lem[c][1]) for c in need))))
