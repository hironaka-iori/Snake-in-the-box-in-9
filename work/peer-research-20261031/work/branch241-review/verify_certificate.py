"""Read exported DIMACS/LRAT and verify positive RUP hints + geometric cuts.
Does not call CDCL or trust its reported status. It does not prove the Lean bridge.
"""
import argparse,gzip,json,hashlib
from pathlib import Path
from rup_check import check
from geometry_check import verify_cycle

def main():
 ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path,nargs='?',default=Path(__file__).parent/'certificate');ap.add_argument('--rebuild',action='store_true');a=ap.parse_args();m=json.loads((a.directory/'manifest.json').read_text())
 if m.get('cap_excluded')!=21 or m.get('occupancy_bonus') is not True or len(m.get('window',[]))!=3 or m.get('objective')!='21alpha+2e2+e3+V' or m.get('geometry_radius') not in range(4,10):raise ValueError('manifest does not support the specialized one-centre score22 claim')
 for name,h in m['files'].items():assert hashlib.sha256((a.directory/name).read_bytes()).hexdigest()==h
 cs=[]
 with gzip.open(a.directory/'pointwise_score22.cnf.gz','rt',encoding='ascii') as f:
  for line in f:
   if line.startswith('c'):continue
   if line.startswith('p'):_,_,nv,nc=line.split();nv,nc=int(nv),int(nc);continue
   ns=list(map(int,line.split()));assert ns[-1]==0 and all(0<abs(l)<=nv for l in ns[:-1]);cs.append(ns[:-1])
 assert len(cs)==nc
 proof=[]
 with gzip.open(a.directory/'pointwise_score22.lrat.gz','rt',encoding='ascii') as f:
  for i,line in enumerate(f):
   ns=list(map(int,line.split()));assert ns[0]==nc+i+1 and ns[-1]==0;split=ns.index(0,1);clause=ns[1:split];hints=ns[split+1:-1];assert all(h>0 for h in hints)
   proof.append({'clause':clause,'hints':hints})
 with gzip.open(a.directory/'cycle8_geometry.json.gz','rt',encoding='utf-8') as f:g=json.load(f)
 var={int(v):x for v,x in g['vertex_variables'].items()};cycles=g['cycles'];assert len(cycles)==m['static_cycles']
 for c in cycles:verify_cycle(c)
 assert cs[g['base_clause_count']:]==[[-var[v] for v in c] for c in cycles]
 if a.rebuild:
  import sys
  base=Path(__file__).resolve().parent.parent/'branch241-next';sys.path[:0]=[str(base),str(base/'encoding')]
  from github_query import build
  E,_,_,meta=build(m['window'],m['cap_excluded'],radius=m['geometry_radius'])
  assert E.var==var and cs[:g['base_clause_count']]==E.cnf.clauses
  assert meta['source_wincert_sha256']==m['source_wincert_sha256']
 result=check(cs,proof);print(json.dumps({'status':'PASS','independently_read_DIMACS_LRAT':True,'valid_cycle_cuts':len(cycles),'proof':result,'scope':'mathematical-window source rebuilt' if a.rebuild else 'CNF/cuts only; mathematical source scope not rebuilt','source_rebuilt':a.rebuild,'Lean_checked':False},indent=2))
if __name__=='__main__':main()
