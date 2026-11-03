"""Check exact local evidence and successful Lean receipts without restarting jobs."""
from pathlib import Path
from collections import Counter
from itertools import combinations
import hashlib, json, re, sys
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
pins = {}
def pin(p):
    pins[p.relative_to(ROOT).as_posix()] = sha(p)

sys.path.insert(0, str(ROOT/'milestones/10-window-aggregate/scripts'))
from gen_lean_sat import TaggedEncoding, is_cycle_set
from wincert import window_from_dirs
for p in [ROOT/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',
          ROOT/'milestones/10-window-aggregate/scripts/wincert.py']:
    pin(p)

probes = []
for p in sorted((HERE/'data/probes').glob('*.json')):
    d = read(p); pin(p)
    assert sha(HERE/'scripts/probe_sum.py') == d['script_sha256']
    for name, digest in d['source_files_sha256'].items():
        assert sha(ROOT/name) == digest
        pin(ROOT/name)
    assert all(is_cycle_set(cut) for cut in d['cycle_cuts'])
    probes.append(dict(name=d['name'], status=d['status'], cuts=len(d['cycle_cuts'])))
assert Counter(x['status'] for x in probes) == {
    'UNSAT_UNCERTIFIED': 6, 'UNKNOWN': 2, 'SAT_LOCAL_WITNESS': 3}

case = read(HERE/'data/probes/012034-middle545-pair8.json')
enc = TaggedEncoding(window_from_dirs(case['directions']), [tuple(b) for b in case['bounds']], radius=4)
lits = []
for j in case['positions']:
    i = j+1; v = enc.window[i]
    used = {v^enc.window[i-1], v^enc.window[i+1]}
    lits += [-enc.var[v^(1<<a)^(1<<b)] for a,b in combinations(range(9),2)
             if (1<<a) not in used and (1<<b) not in used]
lits.sort()
assert len(lits) == case['literal_occurrences'] == 42
assert len(set(lits)) == case['distinct_literals'] == 41
enc.atmost(lits, case['cap'], ('unproved_sum',))
assert not case['cycle_cuts']
assert (len(enc.clauses), enc.nv) == (case['clauses'], case['variables'])
cnf = (f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode()
timeouts = []
for suffix, script in [('', 'certify_sum.py'), ('-plain', 'certify_sum_plain.py')]:
    name = '012034-middle545-pair8'+suffix
    p = HERE/'data'/(name+'-solver.json'); d = read(p); pin(p)
    assert d['status'] == 'TIMEOUT' and d['timeout_seconds'] == 30
    assert (HERE/'work'/name/'full.cnf').read_bytes() == cnf
    assert hashlib.sha256(cnf).hexdigest() == d['cnf_sha256']
    assert sha(HERE/'scripts'/script) == d['script_sha256']
    assert sha(HERE/'data/probes/012034-middle545-pair8.json') == d['probe_sha256']
    raw = HERE/'work'/name/'full.raw.lrat'
    assert sha(raw) == d['raw_sha256'] and raw.stat().st_size == d['raw_bytes']
    for stream in ['stdout','stderr']:
        assert sha(HERE/'logs'/(name+'-solver.'+stream+'.txt')) == d[stream+'_sha256']
    timeouts.append(dict(name=name, status=d['status'], raw_bytes=d['raw_bytes']))

modules = []; audits = []
for name, folder, status, count in [
    ('PairGeometry113','build-pair-geometry','PASS_PAIR_GEOMETRY',1),
    ('PairBudget113','build','PASS_PAIR_BUDGET_ARITHMETIC',3)]:
    p = HERE/'data'/(name+'-audit.json'); d = read(p); pin(p)
    assert d['status'] == status and d['exit_code'] == 0 and not d['timeout']
    source = HERE/'lean'/(name+'.lean')
    assert sha(source) == d['source_sha256'] == sha(HERE/d['source_snapshot'])
    assert sha(HERE/d['checker_snapshot']) == d['checker_sha256']
    assert sha(HERE/folder/(name+'.olean')) == d['olean_sha256']
    assert sha(HERE/d['log']) == d['log_sha256']
    for dep, digest in d['dependencies'].items():
        assert sha(Path(dep)) == digest, dep
    text = source.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide)\b', text)
    assert not re.search(r'^\s*(def|abbrev|structure|inductive)\b', text, re.M)
    if name == 'PairGeometry113':
        assert '(hlocal :' in text
    assert len(d['theorem_audits']) == count == text.count('#print axioms')
    for row in d['theorem_audits']:
        assert set(row['axioms']) <= {'propext','Classical.choice','Quot.sound'}
        audits.append(row)
    modules.append(dict(module=name, receipt=p.relative_to(HERE).as_posix(), receipt_sha256=sha(p)))
    pin(source); pin(HERE/d['log'])

profiles = []
for label, edges, additional in [('interval45454',4887350,21877), ('pair24',4867866,41361)]:
    p = HERE/'data'/label/'results.json'; d = read(p); pin(p)
    assert d['edges'] == edges and d['additional_to_previous_family'] == additional
    assert [(x['mean'], x['range'], x['comparison_integer_bound']) for x in d['profiles']] == [
        ('484','557',235), ('496','602',234)]
    for name, digest in d['source_files_sha256'].items():
        assert sha(ROOT/name) == digest, name
        pin(ROOT/name)
    for x in d['profiles']:
        assert x['all_edge_inequalities_checked']
    profiles.append(dict(label=label, edges=edges, additional=additional))

independent = HERE/'data/independent-check.json'; d = read(independent); pin(independent)
assert d['status'] == 'PASS_BOUNDED_INDEPENDENT_REVIEW' and len(d['witnesses']) == 3
out = dict(status='PASS_PAIR_BUDGET_AND_CONDITIONAL_TRANSFER_LOCAL_LIMITATION',
    modules=modules, theorem_audits=audits, probes=probes, native_proof_timeouts=timeouts,
    profile_comparisons=profiles, source_files_sha256=pins, script_sha256=sha(Path(__file__)),
    new_mathematical_definitions=0, concrete_pair_contradiction_checked=False,
    complete_graph_lean_certificate=False, new_global_bound=False,
    scope='Exact CNF reconstruction, saved source pins and two successful Lean modules checked. Pair geometry retains a local contradiction premise. Native UNSAT and partial proofs do not discharge it. Independent witnesses and replacement cycles limit this fixed family.')
target = HERE/'data/proof-summary.json'; assert not target.exists()
target.write_text(json.dumps(out,indent=2)+'\n', encoding='utf-8')
print(out['status'], 'modules',len(modules),'axiom reports',len(audits),'probes',len(probes))
