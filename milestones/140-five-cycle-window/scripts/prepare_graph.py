"""Prepare, but never execute, the weak 012032 exclusion graph experiment."""
from pathlib import Path
import ast, hashlib, itertools, json, re

H=Path(__file__).resolve().parents[1]; ROOT=H.parents[1]
digest=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
SOURCE=ROOT/'milestones/139-exclusion-occurrence-credit/scripts/evaluate_graph.py'
assert digest(SOURCE)=='c38a19a4e6288f8c1e88bbc9c004525527bc613339683157569c88f0d0e244c7'
s=SOURCE.read_text(encoding='utf-8')
def change(old,new):
 global s
 assert s.count(old)==1,(old[:90],s.count(old))
 s=s.replace(old,new)
s=s.replace('SNAKE139_PARENT_PID','SNAKE140_PARENT_PID')
change("default='exclusion-credit83'", "default='five-cycle-credit83'")
change("label = args.label or 'exclusion-credit83'", "label = args.label or 'five-cycle-credit83'")

GATE=r'''
def _checked_weak_exclusion():
    # This gate executes before resource allocation, output creation, or graph imports.
    root = _home.parents[1]
    completion_path = _home / 'data/proof-completion.json'
    raw = completion_path.read_bytes()
    completion = json.loads(raw)
    assert str(completion.get('status','')).startswith('PASS'), 'The weak exclusion is not complete'
    spec = completion['weak_actual_theorem']
    assert spec['checked'] is True
    assert spec['directions'] == [0,1,2,0,3,2]
    assert spec['bounds'] == [[3,3],[0,5],[4,4],[0,5],[3,3]]
    source = (root / spec['source']).resolve()
    receipt = (root / spec['receipt']).resolve()
    source.relative_to(_home.resolve())
    receipt.relative_to(_home.resolve())
    assert source.suffix == '.lean'
    source_raw, receipt_raw = source.read_bytes(), receipt.read_bytes()
    assert hashlib.sha256(source_raw).hexdigest() == spec['source_sha256']
    assert hashlib.sha256(receipt_raw).hexdigest() == spec['receipt_sha256']
    audit = json.loads(receipt_raw)
    assert audit['status'] == 'PASS'
    assert audit['source_sha256'] == spec['source_sha256']
    assert Path(audit['source']).resolve() == source
    theorem = spec['theorem']
    assert isinstance(theorem,str) and theorem.strip()
    assert re.search(r'\btheorem\s+'+re.escape(theorem.split('.')[-1])+r'\b',source_raw.decode('utf-8-sig'))
    pins = {completion_path.relative_to(root).as_posix(): hashlib.sha256(raw).hexdigest(),
            source.relative_to(root).as_posix(): spec['source_sha256'],
            receipt.relative_to(root).as_posix(): spec['receipt_sha256']}
    return dict(theorem=theorem, pins=pins)
try:
    _proof_gate_info = _checked_weak_exclusion()
except Exception as error:
    print(json.dumps(dict(status='NOT_STARTED_PROOF_GATE',reason=repr(error))),flush=True)
    raise SystemExit(2)
'''
change('_args = _cli.parse_args()', '_args = _cli.parse_args()\n'+GATE)
change('    _owned_lock = False', "    _record['proof_gate'] = _proof_gate_info\n    _owned_lock = False")

INSERT=r'''
# Reproduce139 after all its exclusions and before the new weak exclusion.
previous139=read('milestones/139-exclusion-occurrence-credit/data/exclusion-credit83/results.json')
assert previous139['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA'
assert sha((ROOT/'milestones/139-exclusion-occurrence-credit/scripts/evaluate_graph.py').read_bytes()) == 'c38a19a4e6288f8c1e88bbc9c004525527bc613339683157569c88f0d0e244c7'
previous139_profiles={p['profile']:p for p in previous139['profiles']}
previous139_removed=read('milestones/139-exclusion-occurrence-credit/data/exclusion-credit83/removed-indices.json')
assert np.array_equal(np.flatnonzero(~mask),np.array(previous139_removed))
assert int(mask.sum())==previous139['edges']
for name in ['completed','conditional_floor18']:
    assert sha((3*(base_weights[name]+shared)+83*event)[mask].tobytes())==previous139_profiles[name]['weight_sha256']
previous139_mask=mask.copy()
pins.update(_proof_gate_info['pins'])
for rel in ['milestones/139-exclusion-occurrence-credit/scripts/evaluate_graph.py',
            'milestones/140-five-cycle-window/scripts/prepare_graph.py',
            'milestones/140-five-cycle-window/data/graph-preparation.json']:
    pins[rel]=sha((ROOT/rel).read_bytes())
weak_reject=np.zeros(len(code),dtype=bool)
weak_placements=[]
for placement in range(2):
    for reverse in [False,True]:
        oriented=np.zeros(len(code),dtype=bool)
        for di,word in enumerate(ds):
            selected=word[placement+2:placement+8]
            if reverse:selected=selected[::-1]
            if canon(selected)!=(0,1,2,0,3,2):continue
            lo,hi=np.searchsorted(arrays['direction'],[di,di+1])
            five=digits[lo:hi,placement:placement+5]
            if reverse:five=five[:,::-1]
            oriented[lo:hi]=np.all(five<6,axis=1)&(five[:,0]==3)&(five[:,1]<=5)&(five[:,2]==4)&(five[:,3]<=5)&(five[:,4]==3)
        weak_reject |= oriented
        weak_placements.append(dict(placement=placement,reverse=reverse,total=int(oriented.sum()),on_predecessor139=int((oriented&previous139_mask).sum())))
# Separate palindrome recognition and explicit chronological columns check both placements.
independent_weak=np.zeros(len(code),dtype=bool)
for placement in range(2):
    recognized=np.array([shape(word[placement+2:placement+8])==(0,1,2,0,3,2) for word in ds])[arrays['direction']]
    five=digits[:,placement:placement+5]
    independent_weak |= recognized & np.all(five<6,axis=1) & (five[:,0]==3) & (five[:,2]==4) & (five[:,4]==3) & (five[:,1]<=5) & (five[:,3]<=5)
assert np.array_equal(weak_reject,independent_weak)
mask &= ~weak_reject
assert np.array_equal(mask,previous139_mask & ~weak_reject)
predecessor_cycle_checks=[]
for name,p in previous139_profiles.items():
    cycle_ids=np.array([e['edge'] for e in p['cycle']])
    assert np.all(previous139_mask[cycle_ids])
    killed=[int(k) for k in cycle_ids if weak_reject[k]]
    predecessor_cycle_checks.append(dict(profile=name,removed=killed,survives=not killed))
    if name=='completed':assert set(killed)=={308566,3806548}
    else:assert not killed
'''
change('ids = np.flatnonzero(mask)', INSERT+'\nids = np.flatnonzero(mask)')
change('assert np.all(mask[saved_ids])', 'assert np.all(previous139_mask[saved_ids])')
change('assert np.array_equal(mask,old_mask & ~new_reject)', 'assert np.array_equal(previous139_mask,old_mask & ~new_reject)')
change("# Cross-check the saved completed18-cycle comparison without mistaking it for a minimum.",
       "# Historical18-cycle comparison is checked in the reproduced139 predecessor graph.")
change("saved18_cycle_hypothetical_mean=str(saved_mean),source_files_sha256=pins,algorithm_sha256=algsha,",
       "saved18_cycle_hypothetical_mean=str(saved_mean),saved18_checked_in='predecessor139',source_files_sha256=pins,algorithm_sha256=algsha,")
change('    predecessor131_reproduced=True,predecessor131_edges=int(old_mask.sum()),',
'''    predecessor131_reproduced=True,predecessor131_edges=int(old_mask.sum()),
    predecessor139_reproduced=True,predecessor139_edges=int(previous139_mask.sum()),
    new_weak_exclusion=dict(directions=[0,1,2,0,3,2],bounds=[[3,3],[0,5],[4,4],[0,5],[3,3]],
        checked_theorem=_proof_gate_info['theorem'],proof_pins=_proof_gate_info['pins'],
        total=int(weak_reject.sum()),removed_from139=int((weak_reject&previous139_mask).sum()),
        placements=weak_placements,independent_recognition_agrees=True),
    predecessor139_cycle_checks=predecessor_cycle_checks,''')
change("The new exclusion and occurrence allowance are proved for actual snakes; inherited local hypotheses and graph assembly remain pending.",
       "Execution was gated on the checked weak five-count exclusion; the earlier exclusion and occurrence allowance remain inherited. Other local hypotheses and graph assembly remain pending.")
assert s.index('_proof_gate_info = _checked_weak_exclusion()')<s.index('import analyze_share')
assert "W = (3*(base_weights[name]+shared)+83*event)[mask]" in s
assert 'bound = Fraction(3*1098960*d+8*p+24*83*d+R,3*4200*d+p)' in s
ast.parse(s); ast.parse(Path(__file__).read_text(encoding='utf-8'))

def canon(word):
 names={}; return tuple(names.setdefault(int(x),len(names)) for x in word)
def shape(word):return min(canon(word),canon(word[::-1]))
def bound_match(c):return c[0]==3 and c[1]<=5 and c[2]==4 and c[3]<=5 and c[4]==3
assert canon([2,3,0,2,1,0])==(0,1,2,0,3,2)
count_cases=0
for five in itertools.product(range(1,7),repeat=5):
 forward=bound_match(five); reverse=bound_match(five[::-1])
 closed=all(x<6 for x in five) and five[0]==3 and five[2]==4 and five[4]==3
 assert forward==reverse==closed
 if forward:assert all(x<6 for x in five)
 count_cases+=1
meta_path=ROOT/'milestones/59-extended-share-window/extended/data/model.json'
ds=json.loads(meta_path.read_bytes())['extensions']; shape_cases=0
for word in ds:
 for placement in range(2):
  selected=word[placement+2:placement+8]
  oriented=any(canon(v)==(0,1,2,0,3,2) for v in [selected,selected[::-1]])
  assert oriented==(shape(selected)==(0,1,2,0,3,2)); shape_cases+=1
saved_path=ROOT/'milestones/139-exclusion-occurrence-credit/data/exclusion-credit83/results.json'
saved=json.loads(saved_path.read_bytes()); saved_checks=[]
for profile in saved['profiles']:
 hits=[]
 for row,e in enumerate(profile['cycle']):
  for placement in range(2):
   for reverse in [False,True]:
    word=e['directions'][placement+2:placement+8]; five=e['counts'][placement:placement+5]
    if reverse:word=word[::-1];five=five[::-1]
    if canon(word)==(0,1,2,0,3,2) and bound_match(five):
     hits.append(dict(row=row,edge=e['edge'],placement=placement,reverse=reverse,counts=five))
 killed=sorted({x['edge'] for x in hits})
 assert killed==([308566,3806548] if profile['profile']=='completed' else [])
 saved_checks.append(dict(profile=profile['profile'],removed=killed,matches=hits))
# Isolate the gate function; test a missing receipt without importing or running the evaluator.
gate_function=next(n for n in ast.parse(GATE).body if isinstance(n,ast.FunctionDef))
ns={'Path':Path,'hashlib':hashlib,'json':json,'re':re,'_home':H/'__missing_receipt_test__'}
exec(compile(ast.Module(body=[gate_function],type_ignores=[]),'<isolated-proof-gate>','exec'),ns)
try:ns['_checked_weak_exclusion']()
except FileNotFoundError:pass
else:raise AssertionError('Missing proof receipt must prevent execution')
target=H/'scripts/evaluate_graph.py'
if target.exists():assert target.read_text(encoding='utf-8')==s,'Existing generated source differs; preserve it for review'
else:target.write_text(s,encoding='utf-8',newline='\n')
out=dict(status='PREPARED_NOT_EXECUTED_PROOF_REQUIRED',source_sha256=digest(SOURCE),prepare_sha256=digest(Path(__file__)),evaluate_sha256=digest(target),
 profiles=['completed','conditional_floor18'],credit='83/3',weight_multiplier=3,occurrence_allowance=24,
 candidate=dict(directions=[0,1,2,0,3,2],bounds=[[3,3],[0,5],[4,4],[0,5],[3,3]],placements=[0,1],orientations=['forward','reverse'],all_matching_symbols_below6=True),
 checks=dict(ast_parsed=True,five_count_cases=count_cases,direction_placement_cases=shape_cases,missing_gate_receipt_rejected=True,gate_before_graph_import=True,full_graph_run=False,lean_run=False,solver_run=False),
 predecessor_saved_cycles=saved_checks,inputs_sha256={meta_path.relative_to(ROOT).as_posix():digest(meta_path),saved_path.relative_to(ROOT).as_posix():digest(saved_path)},
 proof_gate='Requires future data/proof-completion.json with PASS and weak_actual_theorem source and successful audit receipt hashes; no completion file is created.',
 scope='Preparation only. The weak actual theorem is required before execution. Both inherited profiles, odd-length restrictions, hypothetical floors, and graph-to-snake obligations remain.')
(H/'data/graph-preparation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
