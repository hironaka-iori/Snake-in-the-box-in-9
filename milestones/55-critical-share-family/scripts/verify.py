"""Check certificate identity, Lean replay coverage, and independent geometric controls."""
from pathlib import Path
from fractions import Fraction
import collections, gzip, hashlib, json, re, subprocess, sys

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT/'milestones/28-direct-share-certificates/scripts'))
sys.path.insert(0, str(ROOT/'milestones/52-share-on-235/scripts'))
from tagged_share import TaggedShare
from geometry_helpers import forest, shares

def read(name):
    return json.loads((HERE/name).read_text(encoding='utf-8'))

def sha(data):
    return hashlib.sha256(data).hexdigest()

def raw(name):
    path = HERE/'certificates'/name
    return path.read_bytes() if path.exists() else gzip.decompress(path.with_name(path.name+'.gz').read_bytes())

def cnf(name):
    return [list(map(int, line.split()))[:-1] for line in raw(name).decode().splitlines()
            if line and not line.startswith(('p', 'c'))]

certificates = []
for row, expected_hints in [(6, 1063501)]:
    stem = f'obstruction{row}_95'
    module = f'ShareObstruction55{row}'
    meta = read(f'data/{stem}.json')
    enc = TaggedShare(meta['directions'], meta['bounds'], 95)
    assert enc.clauses == cnf(stem+'.full.cnf')
    assert len(enc.clauses) == meta['clauses'] == 444845 and enc.nv == meta['variables']
    ids = [i-1 for i in meta['source_original_clause_ids']]
    core = [enc.clauses[i] for i in ids]
    rename = {int(k): v for k, v in meta['original_to_new'].items()}
    compact = [[(-1 if v < 0 else 1)*rename[abs(v)] for v in clause] for clause in core]
    assert compact == cnf(stem+'.cnf')
    assert len(core) == meta['core_clauses']
    used = {abs(v) for clause in core for v in clause}
    needed = used | {abs(v) for ls, k, kind in enc.ctrs for v in ls} | {abs(v) for ls, kind in enc.tots for v in ls}
    assert set(rename) == needed and len(set(rename.values())) == len(rename)
    source = (HERE/f'lean/LocalWindowCnf/{module}.lean').read_text(encoding='utf-8')
    body = source.split('def raw : List (List Nat) := [', 1)[1].split('def cnf', 1)[0]
    leanraw = [[int(v) for v in clause.split(',') if v.strip()]
               for clause in re.findall(r'\[([0-9, ]*)\]', body)]
    assert leanraw == [[2*v if v > 0 else -2*v+1 for v in clause] for clause in compact]
    assert dict(collections.Counter(enc.tags[i][0] for i in ids)) == meta['families']
    assert meta['families']['shareCap'] == 1 and meta['families']['shareCl'] > 0
    assert 's VERIFIED' in (HERE/f'logs/{stem}-drat-check.txt').read_text()
    export = read(f'logs/{stem}-export.txt')
    assert export['simulated'] and export['hints'] == expected_hints
    assignment = read(f'data/assignment-controls{row}.json')
    assert assignment['status'] == 'PASSED' and len(assignment['rows']) == 4
    assert all(r['clauses_checked'] == 444845 for r in assignment['rows'])
    assert assignment['rows'][0]['only_expected_premise_failures'] == 1
    certificates.append(dict(row=row, directions=meta['directions'], bounds=meta['bounds'],
                             core_clauses=len(core), active_variables=len(used),
                             semantic_variables=len(needed), hints=expected_hints, checked_share=96))

for row in read('data/archives.json'):
    assert sha(raw(row['file'])) == row['sha256']
    assert sha((HERE/'certificates'/(row['file']+'.gz')).read_bytes()) == row['archive_sha256']

subprocess.run([sys.executable,'-X','utf8',str(HERE/'scripts/verify_finite.py')],check=True)
finite=read('data/finite-verification.json');assert finite['status']=='PASS'
record=read('logs/build-record.json');build=Path(record['build'])
assert (HERE/'build/latest.txt').read_text().strip()==str(build)
sources={p.relative_to(HERE/'lean').with_suffix('').as_posix():p for p in (HERE/'lean').rglob('*.lean')}
assert len(record['records'])==len(sources)
assert {r['module'] for r in record['records']}==sources.keys()
for r in record['records']:
    assert r['exit_code']==0 and r['source_sha256']==sha(sources[r['module']].read_bytes())
    assert (build/(r['module']+'.olean')).exists()
audits=[]
for module,count in [('CriticalShareCover',4),('LocalWindowSat-ShareObstruction556',1),('ShareBound6',2),('ShareInSnake6',2),('ReversedShareInSnake',1)]:
    log=(HERE/f'logs/{module}.log').read_text()
    assert not any(s in log for s in ['error:','sorryAx','Lean.ofReduceBool'])
    rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    rows += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
    assert len(rows)==count,(module,rows)
    for n,axs in rows:
        assert {a.strip() for a in axs.split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'}
        audits.append(n)
out=dict(status='PASS',lean_modules=len(sources),lean_audits=len(audits),audited_theorems=audits,
    certificates=certificates,assignment_cases=4,assignment_clauses=444845,positive_controls=25,
    critical_cover=[6],models=finite['models'],source_hashes={n:sha(p.read_bytes()) for n,p in sources.items()},
    scope='Local share96 and recorded critical-graph cycle cover checked in Lean. Finite graph means independently checked. Earlier numerical premises and full global assembly remain unresolved; no improved global bound.')
(HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['source_hashes','audited_theorems']})
