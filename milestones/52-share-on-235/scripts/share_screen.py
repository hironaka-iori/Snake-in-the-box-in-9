"""Numerical share tests on the seven distinct windows of the saved critical cycle."""
from pathlib import Path
import concurrent.futures,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
import direct
def task(item):
 index,row,kind=item;file=HERE/f'data/{kind}/w{index:03d}.json';file.parent.mkdir(parents=True,exist_ok=True)
 if file.exists():return json.loads(file.read_text())
 case=dict(name=f'w{index:03d}',dirs=row['directions'],alpha=[[6,21] if c==6 else [c,c] for c in row['counts']],cap=95)
 r=direct.solve(case,seconds=12);r['counts']=row['counts'];r['occurrences']=row['occurrences'];r['scope']='Numerical share screen on selected critical windows; not a complete critical-family screen or Lean certificate.'
 file.write_text(json.dumps(r,indent=2)+'\n');print(case['name'],r['status'],r.get('census',{}).get('total_share'),flush=True)
 return r
if __name__=='__main__':
 supported='--supported' in sys.argv;kind='supported-screen' if supported else 'share-screen'
 rows=json.loads((HERE/'data/supported-critical-windows.json').read_text())[:12] if supported else json.loads((HERE/'data/critical-family.json').read_text())['cycle_windows'];results=[]
 with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
  for r in pool.map(task,[(i,r,kind) for i,r in enumerate(rows)]):
   results.append({k:v for k,v in r.items() if k not in ['selected','census','cycle_cuts','iterations']});(HERE/f'data/{kind}.json').write_text(json.dumps(results,indent=2)+'\n')
