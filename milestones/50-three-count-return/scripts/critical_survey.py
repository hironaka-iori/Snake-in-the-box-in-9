"""Screen every critical five-centre window before selecting more certificates."""
from pathlib import Path
import concurrent.futures,importlib.util,json,collections
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]

def solve(item):
 i,row=item;name=f'critical-{i:03d}';out=HERE/'data/critical-survey';out.mkdir(exist_ok=True)
 file=out/(name+'.json')
 if file.exists():return i,json.loads(file.read_text())
 spec=importlib.util.spec_from_file_location('probe',ROOT/'milestones/40-intervening-counts/scripts/probe.py')
 p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
 p.HERE=HERE;p.DIRS=row['directions'];caps=[21 if x==6 else x for x in row['counts']]
 r=p.solve(name,caps,seconds=4)
 source=HERE/'data'/f'{name}.json';source.replace(file)
 r['critical_counts']=row['counts'];r['occurrences']=row['occurrences'];file.write_text(json.dumps(r,indent=2)+'\n')
 return i,r

def main():
 rows=json.loads((HERE/'data/critical-family.json').read_text())['windows'];results={}
 with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
  futures=[pool.submit(solve,item) for item in enumerate(rows)]
  for future in concurrent.futures.as_completed(futures):
   i,r=future.result();results[i]=r
   report=[dict(index=j,name=v['name'],directions=v['directions'],counts=rows[j]['counts'],caps=v['caps'],status=v['status'],seconds=v['seconds']) for j,v in sorted(results.items())]
   (HERE/'data/critical-survey.json').write_text(json.dumps(report,indent=2)+'\n')
 print('TOTAL',len(results),dict(collections.Counter(v['status'] for v in results.values())),flush=True)
if __name__=='__main__':main()
