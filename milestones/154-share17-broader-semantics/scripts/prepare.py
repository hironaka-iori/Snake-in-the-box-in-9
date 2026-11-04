"""Prepare broader semantics for the existing 153 compact CNF; never run Lean."""
from pathlib import Path
import gzip, hashlib, json, re, sys

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
P = R / 'milestones/153-pair-conditioned-share17'
D = P / 'broader'
read = lambda p: json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def write(p, s):
    p.parent.mkdir(parents=True, exist_ok=True)
    if p.exists():
        assert p.read_bytes() == s.encode('utf-8'), p
        return
    p.write_text(s, encoding='utf-8', newline='\n')

def cnf(p):
    return [list(map(int, s.split()))[:-1] for s in Path(p).read_text().splitlines()
            if s and not s.startswith(('p', 'c'))]

checked = read(D / 'verification.json')
assert checked['status'] == 'PASS_BROADER_CONDITIONS_NATIVE_RUP_REPLAY'
assert checked['compact_core_identical']
for p, digest in checked['source_files_sha256'].items():
    assert sha(R / p) == digest, p
exactplan = read(P / 'data/semantic-source-plan.json')
for row in exactplan['artifacts']:
    assert sha(P / row['path']) == row['sha256'], row['path']

sys.path.insert(0, str(R / 'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
import gen_lean_sat as gen

bounds = [(4, 4), (0, 4), (4, 4), (0, 5), (3, 3)]
e = TaggedShare([0, 1, 2, 0, 3, 2], bounds, 16, M=12)
assert e.clauses == cnf(D / 'input.cnf')
assert len(e.ctrs) == 9
packed = json.loads(gzip.decompress((D / 'meanings.json.gz').read_bytes()))
regenerated = dict(meaning=e.meaning, smeaning=e.smeaning, ctrs=e.ctrs,
                   tots=e.tots, tags=e.tags, ball=e.ball, var=e.var)
assert packed == json.loads(json.dumps(regenerated))
mapping = read(D / 'mapping.json')
rename = {int(k): v for k, v in mapping['existing_compact_map'].items()}
assert sorted(rename.values()) == list(range(1, len(rename) + 1))
nv = len(rename)
rl = lambda x: (1 if x > 0 else -1) * rename[abs(x)]
code = lambda x: gen.code(rl(x))
indices = [i - 1 for i in read(D / 'core-ids.json')]
core = [e.clauses[i] for i in indices]
compact = [[rl(x) for x in c] for c in core]
assert compact == cnf(P / 'certificates/share153.cnf')
tags = [e.tags[i] for i in indices]
raw = [[code(x) for x in c] for c in core]
chunks = [raw[i:i + 128] for i in range(0, len(raw), 128)]
tagchunks = [tags[i:i + 128] for i in range(0, len(tags), 128)]
assert len(chunks) == 93

# Check every old raw declaration before importing it as the shared CNF.
shared_source = P / 'lean/LocalWindowCnf/ShareWindow153.lean'
shared_text = shared_source.read_text(encoding='utf-8')
for i, chunk in enumerate(chunks):
    assert f'def raw{i} : List (List Nat) := {chunk}\n' in shared_text, i
assert 'def cnf : List (List Int) := raw.map (·.map decodeLit)' in shared_text

def leaves(r, s):
    if r + s > nv:
        return [r]
    return leaves(r, 2 * s) + leaves(r + s, 2 * s)

old = {rename[k]: v for k, v in e.meaning.items() if k in rename}
new = {rename[k]: v for k, v in e.smeaning.items() if k in rename}

def leaf48(k):
    m = old.get(k)
    if m is None:
        return 0
    if m[0] == 'p':
        return 1 + 4 * m[1]
    if m[0] == 'e':
        return 2 + 4 * m[1]
    _, c, i, j = m
    assert c < 256 and i < 65536 and j < (1 << 22)
    return 3 + 4 * (c + (i << 8) + (j << 24))

def leaf64(k):
    m = new.get(k)
    if m is None:
        return 0
    if m[0] == 'sq':
        return 1 + 4 * (m[1] + (m[2] << 16) + (m[3] << 24))
    if m[0] == 'u':
        return 3 + 4 * (m[1] + (m[2] << 16))
    _, i, lo, hi, c = m
    assert i < 1024 and lo < 65536 and hi < 65536 and c < (1 << 20)
    return 2 + 4 * (i + (lo << 10) + (hi << 26) + (c << 42))

def stream(xs, bits):
    out = 0
    for x in reversed(xs):
        assert 0 <= x < 1 << bits
        out = (out << bits) | x
    return out

ms = stream([leaf48(k) for k in leaves(0, 1)], 48)
xs = stream([leaf64(k) for k in leaves(0, 1)], 64)
HEADER = 'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
NS = 'Snake9.LocalWindow.ShareWindow154'
head = HEADER + 'namespace ' + NS + '\nopen Snake9.LocalWindow.Tags\n'
body = ('import LocalWindowTagsPacked\nimport LocalWindowTagsSharePacked\n'
        'import LocalWindowCnf.ShareWindow153\n' + head)
body += f'def window : List Nat := {e.window}\n'
body += f'def bounds : List (Nat × Nat) := {bounds}\n'
body += 'def resolution : Nat := 12\ndef cap : Nat := 16\n'
body += f'noncomputable def meaning : MT := (mtB {nv} 64 0 1 (nat_lit 0x{ms:x})).1\n'
body += f'noncomputable def smeaning : MS := (mtB64 {nv} 64 0 1 (nat_lit 0x{xs:x})).1\n'
ct = []
for lits, k, kind in e.ctrs:
    kt = '.ends' if kind[0] == 'ends' else f'(.{kind[0]} {kind[1]})'
    ct.append('⟨' + str([code(x) for x in lits]) + f', {k}, {kt}⟩')
body += 'def ctrs : List Ctr := [' + ','.join(ct) + ']\n'
tt = []
for lits, kind in e.tots:
    kt = f'(.{kind[0]} {kind[1]})' if kind[0] != 'cap' else '(.cap ' + str(kind[1]) + ')'
    tt.append('⟨' + str([code(x) for x in lits]) + ', ' + kt + '⟩')
body += 'def tots : List Tot := [' + ','.join(tt) + ']\n'
def tag(t):
    return '(.old ' + gen.lean_tag(t[1]) + ')' if t[0] == 'old' else gen.lean_tag(t)
for i, chunk in enumerate(tagchunks):
    body += f'def tags{i} : List TagS := [' + ','.join(map(tag, chunk)) + ']\n'
body += 'end ' + NS + '\n'
write(H / 'lean/Share154/Data.lean', body)

head = 'import Share154.Data\n' + head
write(H / 'lean/Share154/Structure.lean', head +
      'theorem counts_ok : ctrs.all (ctrOK meaning (centresK window bounds)) = true := by decide +kernel\n'
      'theorem totals_ok : tots.all (totOK meaning smeaning window (centresK window bounds)) = true := by decide +kernel\n'
      '#print axioms counts_ok\n#print axioms totals_ok\nend ' + NS + '\n')
for i in range(len(chunks)):
    write(H / f'lean/Share154/Shard{i:02d}.lean', head +
          f'theorem shard{i} : ckAllS meaning smeaning resolution ctrs tots window cap tags{i} '
          f'ShareWindow153.raw{i} = true := by decide +kernel\n'
          f'#print axioms shard{i}\nend ' + NS + '\n')

body = 'import Share154.Structure\n' + ''.join(f'import Share154.Shard{i:02d}\n' for i in range(len(chunks)))
body += HEADER + 'namespace ' + NS + '\nopen Snake9.LocalWindow.Tags\n'
body += '''theorem interpreted_core154 (S E : Nat → Bool)
    (ax : AxiomsS S E window (centresOf window bounds) resolution cap) :
    cnfTrue (tauS S E meaning smeaning resolution ctrs tots) ShareWindow153.cnf = true := by
  rw [centresK_eq] at ax
'''
for i in range(len(chunks)):
    body += f'''  have h{i} : ShareWindow153.raw{i}.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard{i} counts_ok totals_ok ax)
'''
body += '  simp only [ShareWindow153.cnf, cnfTrue, List.all_map, ShareWindow153.raw, List.all_append, Bool.and_eq_true,\n'
body += '    List.all_nil, and_true, and_assoc]\n'
body += '  exact ⟨' + ', '.join(f'h{i}' for i in range(len(chunks))) + '⟩\n'
body += '''#print axioms interpreted_core154
theorem local_share17_of_core_unsat154 (h : Unsat ShareWindow153.cnf) :
    RefutedShare window bounds resolution cap :=
  refutedShare_of_sat (fun S E ax => ⟨_, interpreted_core154 S E ax⟩) h
#print axioms local_share17_of_core_unsat154
'''
body += 'end ' + NS + '\n'
write(H / 'lean/Share154/Semantics154.lean', body)

# Reuse the arbitrary-interval transport proof as uncompiled source, with the
# conclusion specialized to the weaker intervals and correctly reversed counts.
adapter = (P / 'lean/CriticalShareAdapter153.lean').read_text(encoding='utf-8')
adapter = adapter.replace('import Share153.Semantics153', 'import Share154.Semantics154')
adapter = adapter.replace('Snake9.CriticalShare153', 'Snake9.CriticalShare154')
adapter = adapter.replace('Exact critical counts; a reversed direction match uses reversed counts.',
                          'Broader critical intervals; the reversed case uses reversed intervals.')
adapter = adapter.replace('[(4,4),(4,4),(4,4),(5,5),(3,3)]', '[(4,4),(0,4),(4,4),(0,5),(3,3)]')
adapter = adapter.replace('ShareWindow153.window, ShareWindow153.bounds,\n      ShareWindow153.resolution, ShareWindow153.cap',
                          'ShareWindow154.window, ShareWindow154.bounds,\n      ShareWindow154.resolution, ShareWindow154.cap')
adapter = adapter.replace('ShareWindow153.local_share17_of_core_unsat153', 'ShareWindow154.local_share17_of_core_unsat154')
for old, new in [('coreAlpha p (r+2) = 4', 'coreAlpha p (r+2) ≤ 4'),
                 ('coreAlpha p (r+4) = 5', 'coreAlpha p (r+4) ≤ 5'),
                 ('coreAlpha p (r+2) = 5', 'coreAlpha p (r+2) ≤ 5'),
                 ('coreAlpha p (r+4) = 4', 'coreAlpha p (r+4) ≤ 4')]:
    assert adapter.count(old) == 1, old
    adapter = adapter.replace(old, new)
assert adapter.count('(hunsat : Unsat ShareWindow153.cnf)') == 1
write(H / 'lean/CriticalShareAdapter154.lean', adapter)

order = ['Share154.Data', 'Share154.Structure'] + [f'Share154.Shard{i:02d}' for i in range(len(chunks))]
order += ['Share154.Semantics154', 'CriticalShareAdapter154']
artifacts = []
for module in order:
    p = H / 'lean' / (module.replace('.', '/') + '.lean')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', p.read_text(encoding='utf-8'))
    artifacts.append(dict(module=module, path=p.relative_to(H).as_posix(),
                          bytes=p.stat().st_size, sha256=sha(p)))
pins = [Path(__file__), D / 'verification.json', D / 'mapping.json', D / 'meanings.json.gz',
        D / 'input.cnf', D / 'core.cnf', D / 'core-ids.json',
        P / 'certificates/share153.cnf', shared_source,
        P / 'data/semantic-source-plan.json', P / 'lean/CriticalShareAdapter153.lean',
        R / 'milestones/28-direct-share-certificates/scripts/tagged_share.py',
        Path(gen.__file__).resolve()]
plan = dict(status='PREPARED_BROADER_SHARE17_SEMANTICS_UNCHECKED', checked=False,
            Lean_started=False, actual_snake_theorem_complete=False, new_global_upper_bound=False,
            bounds=bounds, cap=16, resolution=12, counter_count=len(e.ctrs), semantic_variables=nv,
            core_clauses=len(core), shards=len(chunks), module_order=order, artifacts=artifacts,
            shared_cnf_module='LocalWindowCnf.ShareWindow153',
            shared_cnf_constant='Snake9.LocalWindow.ShareWindow153.cnf',
            shared_cnf_source_sha256=sha(shared_source), duplicate_contradiction_required=False,
            external_unchecked_dependency='LocalWindowCnf.ShareWindow153',
            additional_dependency='CanonicalShareAdapter from milestone148; checked generic framework from milestone147',
            source_files_sha256={p.relative_to(R).as_posix(): sha(p) for p in pins},
            exact153_artifacts_unchanged=all(sha(P / row['path']) == row['sha256'] for row in exactplan['artifacts']),
            scope='Source preparation only. The new clause meanings use the broader nine-counter encoding and the exact shared compact CNF. Lean must check all semantic modules and the conditional actual-snake adapter. The single shared contradiction replay remains pending.')
write(H / 'data/source-plan.json', json.dumps(plan, indent=2) + '\n')
print(json.dumps({k: v for k, v in plan.items() if k not in ['module_order', 'artifacts', 'source_files_sha256']}))
