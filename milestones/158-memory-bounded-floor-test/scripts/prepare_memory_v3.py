"""Use disk-backed source columns and one numerical-library thread."""
from pathlib import Path
import ast,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def replace(s,a,b):
    assert s.count(a)==1,a
    return s.replace(a,b,1)
def write(p,s):
    raw=s.encode('utf-8')
    if p.exists(): assert p.read_bytes()==raw,str(p)
    else:p.write_bytes(raw)
old=json.loads((H/'data/preparation_v2.json').read_text())
for p,d in old['script_pins'].items():assert sha(R/p)==d,p
s=(H/'scripts/reconstruct_small.py').read_text().replace('import json','import json\nimport zipfile\nimport shutil').replace('def reconstruct(np):','def reconstruct(np, run):')
s=replace(s,"    with np.load(R/rel, allow_pickle=False) as z:\n        arrays = {k:z[k] for k in ['U','V','weight','direction','count_code']}","""    columns = run / 'source-columns'
    columns.mkdir()
    arrays = {}
    with zipfile.ZipFile(R/rel) as z:
        for k in ['U','V','weight','direction','count_code']:
            target = columns / (k+'.npy')
            with z.open(k+'.npy') as source, target.open('xb') as out:
                shutil.copyfileobj(source, out, length=1048576)
            arrays[k] = np.load(target, mmap_mode='r', allow_pickle=False)""")
ast.parse(s);write(H/'scripts/reconstruct_mapped.py',s)
s=(H/'scripts/potential_range_v2.py').read_text().replace('from reconstruct_small import reconstruct','from reconstruct_mapped import reconstruct').replace('data/preparation_v2.json','data/preparation_v3.json').replace('data = reconstruct(np)','data = reconstruct(np, run)')
s=replace(s,'import numpy as np',"os.environ['OPENBLAS_NUM_THREADS'] = '1'\nos.environ['OMP_NUM_THREADS'] = '1'\nimport numpy as np")
s=replace(s,"    arrays, meta, ds = data['arrays'], data['meta'], data['ds']","    save(progress, dict(phase='REPRODUCING_WEIGHTS', worker_pid=os.getpid()))\n    arrays, meta, ds = data['arrays'], data['meta'], data['ds']")
ast.parse(s);write(H/'scripts/potential_range_v3.py',s)
s=(H/'scripts/run_potential_v2.py').read_text().replace('native_guard_v2','native_guard_v3').replace('data/preparation_v2.json','data/preparation_v3.json').replace('potential_range_v2.py','potential_range_v3.py')
ast.parse(s);write(H/'scripts/run_potential_v3.py',s)
s=(H/'scripts/native_guard_v2.py').read_text().replace('(?:_v2)?','(?:_v[23])?')
ast.parse(s);write(H/'scripts/native_guard_v3.py',s)
prep=dict(old);prep['input_pins']=dict(old['input_pins'])
for p in [H/'data/preparation_v2.json',H/'scripts/potential_range_v2.py',H/'scripts/run_potential_v2.py',H/'scripts/reconstruct_small.py']:
    prep['input_pins'][p.relative_to(R).as_posix()]=sha(p)
prep['script_pins']={(H/'scripts'/name).relative_to(R).as_posix():sha(H/'scripts'/name) for name in ['prepare_memory_v3.py','reconstruct_mapped.py','potential_range_v3.py','run_potential_v3.py','native_guard_v3.py','native_resources.py']}
prep['source_storage']='Read-only memory-mapped source columns extracted in1MiB blocks; source array hashes checked; one numerical-library thread.'
write(H/'data/preparation_v3.json',json.dumps(prep,indent=2)+'\n');print('PREPARED_MEMORY_V3',sha(H/'data/preparation_v3.json'))
