"""Also retry transient readers of atomically replaced progress records."""
from pathlib import Path
import ast,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,s):
    b=s.encode()
    if p.exists():assert p.read_bytes()==b,str(p)
    else:p.write_bytes(b)
old=json.loads((H/'data/preparation_v4.json').read_text())
for p,d in old['script_pins'].items():assert sha(R/p)==d,p
original="    return json.loads(Path(path).read_text(encoding='utf-8-sig'))"
replacement="""    for attempt in range(40):
        try:
            return json.loads(Path(path).read_text(encoding='utf-8-sig'))
        except PermissionError:
            if attempt == 39:
                raise
            time.sleep(0.05)"""
for stem in ['potential_range','run_potential']:
    s=(H/'scripts'/(stem+'_v4.py')).read_text()
    assert s.count(original)==1
    s=s.replace(original,replacement).replace('data/preparation_v4.json','data/preparation_v5.json').replace('potential_range_v4.py','potential_range_v5.py').replace('native_guard_v4','native_guard_v5')
    ast.parse(s);write(H/'scripts'/(stem+'_v5.py'),s)
s=(H/'scripts/native_guard_v4.py').read_text().replace('_v[234]','_v[2345]')
ast.parse(s);write(H/'scripts/native_guard_v5.py',s)
prep=dict(old);prep['input_pins']=dict(old['input_pins'])
for p in [H/'data/preparation_v4.json',H/'scripts/potential_range_v4.py',H/'scripts/run_potential_v4.py']:
    prep['input_pins'][p.relative_to(R).as_posix()]=sha(p)
prep['script_pins']={(H/'scripts'/n).relative_to(R).as_posix():sha(H/'scripts'/n) for n in ['prepare_io_v5.py','reconstruct_mapped.py','potential_range_v5.py','run_potential_v5.py','native_guard_v5.py','native_resources.py']}
prep['io_change']='Both atomic JSON replacement and JSON reads retry PermissionError up to40 attempts with50ms spacing; numerical operations unchanged.'
write(H/'data/preparation_v5.json',json.dumps(prep,indent=2)+'\n');print('PREPARED_IO_V5')
