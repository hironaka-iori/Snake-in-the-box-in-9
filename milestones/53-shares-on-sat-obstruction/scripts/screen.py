"""Test direct empty-square shares on the contributor's SAT obstruction."""
from pathlib import Path
import collections,concurrent.futures,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
import direct
def task(item):
 i,row=item;file=HERE/f'data/screen/w{i:02d}.json';file.parent.mkdir(parents=True,exist_ok=True)
 if file.exists():return json.loads(file.read_text())
 case=dict(name=f'w{i:02d}',dirs=row['directions'],alpha=[[6,21] if c==6 else [c,c] for c in row['counts']],cap=95)
 r=direct.solve(case,seconds=15);r['counts']=row['counts'];r['occurrences']=row['occurrences'];r['scope']='Numerical share-cap test. Contributor reports an ordinary SAT control; local witness reproduction and Lean replay remain separate obligations.'
 file.write_text(json.dumps(r,indent=2)+'\n');print(case['name'],r['status'],r.get('census',{}).get('total_share'),flush=True);return r
if __name__=='__main__':
 source=json.loads((HERE/'data/upstream/obstruction_B6.json').read_text());counts=collections.Counter()
 for edge in source['edges']:
  for ds,cs,status in edge['windows']:
   if len(cs)==5:
    assert status=='SAT';counts[(tuple(ds),tuple(cs))]+=1
 rows=[dict(directions=list(ds),counts=list(cs),occurrences=n) for (ds,cs),n in counts.most_common()]
 (HERE/'data/windows.json').write_text(json.dumps(rows,indent=2)+'\n');print('Five-centre patterns',len(rows),'occurrences',sum(counts.values()),flush=True)
 results=[]
 with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
  for r in pool.map(task,enumerate(rows)):
   results.append({k:v for k,v in r.items() if k not in ['selected','census','cycle_cuts','iterations']});(HERE/'data/screen.json').write_text(json.dumps(results,indent=2)+'\n')
