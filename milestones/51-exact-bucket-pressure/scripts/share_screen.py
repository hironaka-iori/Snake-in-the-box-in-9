"""Test exact empty-square shares on every current critical five-centre window."""
from pathlib import Path
import concurrent.futures,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
import direct
def task(item):
 index,row=item;file=HERE/f'data/share-screen/w{index:03d}.json';file.parent.mkdir(parents=True,exist_ok=True)
 if file.exists():return json.loads(file.read_text())
 case=dict(name=f'w{index:03d}',dirs=row['directions'],alpha=[[6,21] if c==6 else [c,c] for c in row['counts']],cap=95)
 result=direct.solve(case,seconds=12);result['counts']=row['counts'];result['occurrences']=row['occurrences'];result['scope']='Numerical CP-SAT test of share at most95; no certificate replay or universal exclusion claim.'
 file.write_text(json.dumps(result,indent=2)+'\n');print(case['name'],result['status'],result.get('census',{}).get('total_share'),flush=True)
 return result
if __name__=='__main__':
 rows=json.loads((HERE/'pass5/data/critical-family.json').read_text())['windows'];results=[]
 with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
  for r in pool.map(task,enumerate(rows)):
   results.append({k:v for k,v in r.items() if k not in ['selected','census','cycle_cuts','iterations']});(HERE/'data/share-screen.json').write_text(json.dumps(results,indent=2)+'\n')
