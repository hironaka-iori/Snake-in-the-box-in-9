"""Test hidden excess on every window of the surviving critical family."""
from pathlib import Path
import concurrent.futures,importlib.util,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
def task(item):
 i,row=item;spec=importlib.util.spec_from_file_location('probe',ROOT/'milestones/40-intervening-counts/scripts/probe.py')
 p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p);p.HERE=HERE;p.DIRS=row['directions']
 positions=[j+1 for j,c in enumerate(row['counts']) if c==6];assert positions
 caps=[21 if c==6 else c for c in row['counts']];out=HERE/'data/excess-survey';out.mkdir(exist_ok=True);records=[]
 for delta in [0,1,3,7,11]:
  name=f'excess-{i:02d}-{delta:02d}';file=out/(name+'.json')
  if file.exists():r=json.loads(file.read_text())
  else:
   r=p.solve(name,caps,seconds=8,joint=(positions,6*len(positions)+delta))
   (HERE/'data'/f'{name}.json').replace(file)
  records.append(dict(name=name,directions=row['directions'],counts=row['counts'],positions=positions,excess_cap=delta,status=r['status']))
  if r['status']=='SAT':break
 return records
if __name__=='__main__':
 rows=json.loads((HERE/'screen/data/critical-family.json').read_text())['windows'];results=[]
 with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
  for records in pool.map(task,enumerate(rows)):
   results.extend(records);(HERE/'data/excess-survey.json').write_text(json.dumps(results,indent=2)+'\n')
