"""Export independently checked JSON RUP hints as standard positive-hint LRAT."""
import argparse,gzip,json,hashlib,sys
from pathlib import Path
H=Path(__file__).resolve().parent;B=H.parent/'branch241-next';sys.path[:0]=[str(B),str(B/'encoding')]
from github_query import build
from rup_check import check
from geometry_check import verify_cycle

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=H/'loop_k1_cap21_r4_all8/checked_unsat.json.gz');ap.add_argument('--out',type=Path,default=H/'certificate');a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
 with gzip.open(a.input,'rt',encoding='utf-8') as f:d=json.load(f)
 scope=d['meta']
 if scope.get('cap_scaled21')!=21 or scope.get('bonus') is not True or len(scope.get('path',[]))!=3 or scope.get('objective')!='21alpha+2e2+e3+V' or scope.get('geometry_radius') not in range(4,10):raise ValueError('score22 exporter requires a one-centre bonus query excluding cap21 at radius4..9')
 result=check(d['clauses'],d['proof']);E,_,_,meta=build(d['meta']['path'],d['meta']['cap_scaled21'],radius=d['meta']['geometry_radius']);cycles=d['static_cycles']
 for c in cycles:verify_cycle(c)
 assert d['clauses']==E.cnf.clauses+[[-E.var[v] for v in c] for c in cycles]
 nv=max(abs(l) for c in d['clauses'] for l in c);base=len(d['clauses'])
 cnf=a.out/'pointwise_score22.cnf.gz';lrat=a.out/'pointwise_score22.lrat.gz';geometry=a.out/'cycle8_geometry.json.gz'
 text=f'p cnf {nv} {base}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in d['clauses'])
 with gzip.open(cnf,'wb',compresslevel=1) as f:f.write(text.encode('ascii'))
 text=''.join(str(base+i+1)+' '+' '.join(map(str,p['clause']))+' 0 '+' '.join(map(str,p['hints']))+' 0\n' for i,p in enumerate(d['proof']))
 with gzip.open(lrat,'wb',compresslevel=1) as f:f.write(text.encode('ascii'))
 with gzip.open(geometry,'wt',encoding='utf-8',compresslevel=1) as f:json.dump({'cycles':cycles,'vertex_variables':E.var,'base_clause_count':len(E.cnf.clauses)},f,separators=(',',':'))
 manifest={'claim':'Every internal Q9 snake vertex has q=21alpha+2e2+e3+V >=22; computational certificate, not Lean or improved a(9) upper bound','variables':nv,'clauses':base,'RUP':result,'window':d['meta']['path'],'cap_excluded':d['meta']['cap_scaled21'],'occupancy_bonus':True,'objective':scope['objective'],'geometry_radius':d['meta']['geometry_radius'],'static_cycles':len(cycles),'source_wincert_sha256':meta['source_wincert_sha256'],'files':{p.name:sha(p) for p in (cnf,lrat,geometry)}}
 (a.out/'manifest.json').write_text(json.dumps(manifest,indent=2));print(json.dumps(manifest,indent=2))
if __name__=='__main__':main()
