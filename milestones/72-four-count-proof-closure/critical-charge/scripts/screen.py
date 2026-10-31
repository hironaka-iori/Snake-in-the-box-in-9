"""Bounded tests on representatives of every critical component; no theorem claim."""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
import direct
read=lambda p:json.loads(p.read_text())
rows=read(HERE/'data/windows.json'); family=read(HERE/'data/critical-family.json')
chosen=[]
for component in family['components']:
    options=[(i,r) for i,r in enumerate(rows) if component['id'] in r['components']]
    i,r=min(options,key=lambda ir:(-ir[1]['occurrences'],ir[0]))
    if i not in chosen:chosen.append(i)
for i in range(2):
    if i not in chosen:chosen.append(i)
output=HERE/'data/screen';output.mkdir(exist_ok=True)
manifest=dict(window_file_sha256=hashlib.sha256((HERE/'data/windows.json').read_bytes()).hexdigest(),
 source_potential_sha256=family['source_potential_sha256'],selected_windows=chosen,
 direct_sha256=hashlib.sha256(Path(direct.__file__).read_bytes()).hexdigest(),
 scope='Representative local CP-SAT probes only. No global bound or Lean-checked share exclusion follows.')
(HERE/'data/screen-plan.json').write_text(json.dumps(manifest,indent=2)+'\n')
for i in chosen:
    row=rows[i]
    for cap in [None,0,95]:
        tag='ordinary' if cap is None else f'cap{cap}'
        target=output/f'w{i:03d}-{tag}.json'
        if target.exists():continue
        case=dict(name=f'w{i:03d}-{tag}',dirs=row['directions'],alpha=[[6,21] if c==6 else [c,c] for c in row['counts']],cap=cap)
        result=direct.solve(case,seconds=8)
        result.update(window_index=i,components=row['components'],scope=manifest['scope'])
        target.write_text(json.dumps(result,indent=2)+'\n')
        print(case['name'],result['status'],result.get('census',{}).get('total_share'),flush=True)
