"""Zero-share specialization: no quotient gates or share counters are needed.
For q adjacent to a charged selected center, d(q)>=1 and <=9, so
floor(12*E(q)/d(q)) is zero iff E(q)=0. Therefore every square at q
must contain a selected vertex. Complete face-domain checking is mandatory.
"""
from pathlib import Path
from itertools import combinations
import ast,json,sys,gzip,time,hashlib,argparse
H=Path(__file__).resolve().parent;ROOT=H.parent;sys.path.insert(0,str(ROOT/'branch241-review'))
from solver_plus import Solver
from rup_check import check

def encoding():
 p=ROOT/'branch241-audit/repo/milestones/10-window-aggregate/scripts/wincert.py';raw=p.read_bytes();tree=ast.parse(raw.decode('utf-8-sig'));cls=next(n for n in tree.body if isinstance(n,ast.ClassDef) and n.name=='Encoding');ns={'combinations':combinations};exec(compile(ast.Module(body=[cls],type_ignores=[]),str(p),'exec'),ns);return ns['Encoding'],hashlib.sha256(raw).hexdigest()

def build(edge):
 path=[0]
 for d in edge['directions']:path.append(path[-1]^(1<<d))
 alpha=[None,None]+edge.get('count_bounds',[(6,21) if c==6 else c for c in edge['counts']]);Encoding,digest=encoding();E=Encoding(path,alpha,4);before=len(E.clauses);faces=set();charged=path[4:9]
 for c in charged:
  for d in range(9):
   q=c^(1<<d)
   for a,b in combinations(range(9),2):
    square={q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}
    if not square<=E.B:raise ValueError('incomplete empty-face domain')
    faces.add(tuple(sorted(E.var[v] for v in square)))
 for clause in sorted(faces):E.add(clause,'zero_share_nonempty_face')
 return E,{'directions':edge['directions'],'counts':edge['counts'],'count_bounds':alpha[2:],'window':path,'charged_centres':charged,'base_clauses':before,'zero_share_positive_face_clauses':len(faces),'variables':E.nv,'source_wincert_sha256':digest,'scope':'necessary local conditions plus five-center total share ZERO; not a full snake model'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=20);ap.add_argument('--cycle-offset',type=int,default=0);args=ap.parse_args()
 base={e['source_edge']:e for e in json.loads((H/'filtered_critical_edges.json').read_text())};cycle=json.loads((H/'bucket_excess_probe.json').read_text())['zero_gain_cycle'];edge=base[cycle[args.cycle_offset%len(cycle)]];E,meta=build(edge);solver=Solver(E.clauses,E.nv,primary=E.var.values(),phase_true=[E.var[v] for v in meta['window']],restart='lbd');r=solver.solve(seconds=args.seconds);proof=check(E.clauses,solver.proof,require_empty=r['status']=='UNSAT');model=r.pop('model',None)
 if model is not None:
  chosen=set(model);assert all(any(l in chosen for l in c) for c in E.clauses)
 out=H/'zero_share_probes';out.mkdir(exist_ok=True);tag=f'offset{args.cycle_offset}';receipt={'meta':meta,'source_frozen_edge':edge['source_edge'],'solver':r,'proof_check':proof,'Lean_checked':False,'new_global_bound':None}
 if model is not None:receipt['selected']=[v for v,var in E.var.items() if var in chosen]
 with gzip.open(out/(tag+'.json.gz'),'wt') as f:json.dump({'clauses':E.clauses,'proof':solver.proof,'model':model,'meta':meta},f,separators=(',',':'))
 (out/(tag+'_summary.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
