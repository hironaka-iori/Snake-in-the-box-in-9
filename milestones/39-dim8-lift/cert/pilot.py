"""Pilot: turn one cube's LRAT refutation into the repository's v3 replay modules.
1. core = input clauses reachable from the empty clause (in original order, original ids);
2. compact the core's variables to 1..V (new v' stands for old back[v'-1]); rename lemma literals too;
3. write LocalWindowCnf/<Mod>.lean (raw core, decodeLit coding), the renamed LRAT, the core json,
   and <Mod>Glue.lean: back list, core with indices into the full CNF, and the two glue checks.
usage: python3 pilot.py full.cnf proof.lrat Mod outdir"""
import sys, os, json
from array import array
cnf, lrat, mod, out = sys.argv[1:5]
os.makedirs(os.path.join(out, 'LocalWindowCnf'), exist_ok=True)
ncls = int(open(cnf).readline().split()[3])
# pass 1 over the LRAT: only the hints are kept, in one flat array (the old dict of lists of strings
# reached 13 GB on a 2.25 GB LRAT); cids[i] is the id of the i-th lemma, H[st[i]:st[i+1]] its hints
cids = array('q'); st = array('q', [0]); H = array('i'); empty_last = False
for line in open(lrat, 'rb'):
    p = line.split()
    if p[1] == b'd': continue
    z = p.index(b'0', 1)
    cid = int(p[0]); assert not cids or cid > cids[-1], 'lemma ids must increase'
    cids.append(cid); H.extend(map(int, p[z + 1:-1])); st.append(len(H)); empty_last = (z == 1)
assert empty_last, 'the last lemma must be the empty clause'
pos = array('i', [-1]) * (cids[-1] + 1)          # lemma id -> index
for i, c in enumerate(cids): pos[c] = i
need = bytearray(len(cids)); need[-1] = 1; core = set(); stk = [len(cids) - 1]
while stk:
    i = stk.pop()
    for h in H[st[i]:st[i + 1]]:
        if h <= ncls: core.add(h)
        else:
            j = pos[h]
            if not need[j]: need[j] = 1; stk.append(j)
nhints = sum(st[i + 1] - st[i] for i in range(len(cids)) if need[i]); nlem = sum(need)
del H, st, pos
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
rows = ['[' + ', '.join(str(enc(ren(l))) for l in clauses[c]) + ']' for c in core_ids]
CH = 4000
os.makedirs(os.path.join(out, 'LocalWindowCnf', mod), exist_ok=True)
names = []
for k in range(0, len(rows), CH):
    nm = 'R%d' % (k // CH); names.append(nm)
    with open(os.path.join(out, 'LocalWindowCnf', mod, nm + '.lean'), 'w') as f:
        f.write("set_option maxRecDepth 100000\nnamespace Snake9.LocalWindow.%s\ndef r%d : List (List Nat) := [\n%s]\nend Snake9.LocalWindow.%s\n"
                % (mod, k // CH, ",\n".join(rows[k:k + CH]), mod))
with open(os.path.join(out, 'LocalWindowCnf', mod + '.lean'), 'w') as f:
    f.write("import LocalWindowModel\n" + "".join("import LocalWindowCnf.%s.%s\n" % (mod, nm) for nm in names) +
            "/-! Compacted UNSAT core of cube %s: %d of %d clauses, %d variables (renamed). -/\n"
            "namespace Snake9.LocalWindow.%s\ndef raw : List (List Nat) := %s\n"
            "def cnf : List (List Int) := raw.map (·.map decodeLit)\nend Snake9.LocalWindow.%s\n"
            % (mod, len(core_ids), ncls, len(vs), mod, " ++ ".join("r%d" % (k // CH) for k in range(0, len(rows), CH)), mod))
open(os.path.join(out, 'LocalWindowCnf', mod + '.parts'), 'w').write(' '.join(names))
# renamed LRAT, keeping only needed lemmas (others dropped; ids unchanged): pass 3, streamed
needed = {cids[i] for i in range(len(cids)) if need[i]}
with open(os.path.join(out, mod + '.lrat'), 'w') as f:
    for line in open(lrat):
        p = line.split()
        if p[1] == 'd': continue
        cid = int(p[0])
        if cid not in needed: continue
        z = p.index('0', 1)
        f.write('%d %s 0 %s 0\n' % (cid, ' '.join(str(ren(int(l))) for l in p[1:z]), ' '.join(p[z + 1:-1])))
os.makedirs(os.path.join(out, 'core'), exist_ok=True)
json.dump(dict(module='Snake9.LocalWindow.' + mod, core_ids=core_ids), open(os.path.join(out, 'core', mod + '.json'), 'w'))
json.dump(dict(back=vs, core_ids=core_ids, nvars=len(vs)), open(os.path.join(out, mod + '.glue.json'), 'w'))
print(json.dumps(dict(core=len(core_ids), vars=len(vs), lemmas=nlem, hints=nhints)))
