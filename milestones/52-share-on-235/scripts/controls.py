"""Ordinary local satisfiability controls for the seven new share candidates."""
from pathlib import Path
import concurrent.futures,json,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/51-exact-bucket-pressure/scripts'))
import pressure
if __name__=='__main__':
 rows=json.loads((HERE/'data/critical-family.json').read_text())['cycle_windows']
 assert all(6 not in r['counts'] for r in rows)
 with concurrent.futures.ProcessPoolExecutor(max_workers=2) as pool:
  result=list(pool.map(pressure.query,[(str(HERE/'controls'),i,r) for i,r in enumerate(rows)]))
 (HERE/'data/ordinary-controls.json').write_text(json.dumps(result,indent=2)+'\n')
