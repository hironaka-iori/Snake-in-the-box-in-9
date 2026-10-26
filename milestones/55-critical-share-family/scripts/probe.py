"""Test replacement-cycle windows, requiring ordinary positive controls first."""
from pathlib import Path
import collections, concurrent.futures, json, sys

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0, str(ROOT/'milestones/53-shares-on-sat-obstruction/scripts'))
import controls
sys.path.insert(0, str(ROOT/'milestones/28-direct-share-certificates/scripts'))
import direct

def task(item):
    index, row = item
    controls.HERE = HERE
    control = controls.task(item)
    path = HERE/f'data/screen/w{index:02d}.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        return json.loads(path.read_text())
    if control['status'] != 'SAT':
        result = dict(status='SKIPPED', ordinary_status=control['status'])
    else:
        case = dict(name=f'w{index:02d}', dirs=row['directions'],
                    alpha=[[6,21] if c == 6 else [c,c] for c in row['counts']], cap=95)
        result = direct.solve(case, seconds=15)
    result.update(counts=row['counts'], directions=row['directions'], occurrences=row['occurrences'],
                  scope='Numerical screen only. A local positive control does not establish full-snake extendability.')
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(index, 'share screen', result['status'], result.get('census', {}).get('total_share'), flush=True)
    return result

if __name__ == '__main__':
    rows=json.loads((HERE/'data/windows.json').read_text())
    results=[]
    with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
        for row in pool.map(task,enumerate(rows)):
            results.append({k:v for k,v in row.items() if k not in ['selected','census','cycle_cuts','iterations']})
            (HERE/'data/screen.json').write_text(json.dumps(results,indent=2)+'\n')
