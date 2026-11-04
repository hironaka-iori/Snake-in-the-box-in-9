"""Prepare a second storage layout, preserving the stopped first attempt."""
from pathlib import Path
import ast, hashlib, json
H=Path(__file__).resolve().parents[1]
R=H.parents[1]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def replace(s,a,b):
    assert s.count(a)==1,a
    return s.replace(a,b,1)
def write(p,s):
    raw=s.encode('utf-8')
    if p.exists(): assert p.read_bytes()==raw,str(p)
    else:p.write_bytes(raw)

old=json.loads((H/'data/preparation.json').read_text())
for p,d in old['script_pins'].items():assert sha(R/p)==d,p
s=(H/'scripts/potential_range.py').read_text()
s=s.replace('data/preparation.json','data/preparation_v2.json')
s=replace(s,"    target_shape = np.asarray([s == '012034' for s in shapes], dtype=bool)[direction]", "    # Hashes and original-row checks are complete; release large temporary arrays.\n    del original_floor, old144, source16, new_floor\n    gc.collect()\n    target_shape = np.asarray([s == '012034' for s in shapes], dtype=bool)[direction]")
s=replace(s,'    weaker_conditional = conditional.copy()','    weaker_conditional = conditional')
s=replace(s,'del data, arrays, meta, direction, mask, shared, digits, source_weight, source16, source17','del data, arrays, meta, direction, mask, shared, digits, source_weight, source17')
s=replace(s,'del matched, last, conditional, new_floor, original_floor, old144','del matched, last, conditional')
ast.parse(s);write(H/'scripts/potential_range_v2.py',s)
s=(H/'scripts/run_potential.py').read_text().replace('from native_guard import snapshot','from native_guard_v2 import snapshot').replace('data/preparation.json','data/preparation_v2.json').replace('scripts/potential_range.py','scripts/potential_range_v2.py')
ast.parse(s);write(H/'scripts/run_potential_v2.py',s)
s=(H/'scripts/native_guard.py').read_text()
s=replace(s,r'run_potential\.py|potential_range\.py',r'run_potential(?:_v2)?\.py|potential_range(?:_v2)?\.py')
ast.parse(s);write(H/'scripts/native_guard_v2.py',s)
prep=dict(old)
prep['script_pins']={(H/'scripts'/name).relative_to(R).as_posix():sha(H/'scripts'/name) for name in ['prepare_memory_v2.py','reconstruct_small.py','potential_range_v2.py','run_potential_v2.py','native_guard_v2.py','native_resources.py']}
prep['input_pins']=dict(old['input_pins'])
for p in [H/'data/preparation.json',H/'scripts/potential_range.py',H/'scripts/run_potential.py',H/'scripts/native_guard.py']:
    prep['input_pins'][p.relative_to(R).as_posix()]=sha(p)
prep['storage_change']='Release original_floor, old144, source16 and new_floor after their final checks; reuse conditional storage. No mathematical or stopping-rule change.'
write(H/'data/preparation_v2.json',json.dumps(prep,indent=2)+'\n')
print('PREPARED_MEMORY_V2',sha(H/'data/preparation_v2.json'))
