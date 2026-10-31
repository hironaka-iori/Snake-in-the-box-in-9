import gzip,json,time
from pathlib import Path
from cheap_folded import FixedPathObjective
from pb_binary import BinaryCNF,self_test
from charge_fast import Geometry,Charges
HERE=Path(__file__).resolve().parent;REPO=HERE.parents[1]/'branch241-audit/repo'
def propagate(clauses):
 values={};passes=0
 while True:
  changed=False;passes+=1
  for clause in clauses:
   unknown=[];sat=False
   for lit in clause:
    v=values.get(abs(lit))
    if v is None:unknown.append(lit)
    elif v==(lit>0):sat=True;break
   if sat:continue
   if not unknown:return {'contradiction':True,'passes':passes,'assigned_variables':len(values)}
   if len(unknown)==1:lit=unknown[0];values[abs(lit)]=lit>0;changed=True
  if not changed:return {'contradiction':False,'passes':passes,'assigned_variables':len(values)}
def main():
 bank=json.loads((REPO/'work/bank9.json').read_text());path=bank[67]['vertex_sequence'];S=set(path);G=Geometry(9);rows=[]
 for bonus in (False,True):
  E=FixedPathObjective(G,path[:11],occupancy_bonus=bonus,cnf_factory=BinaryCNF);score=sum(E.evaluate(path).values());base_nv=E.cnf.nv;before=len(E.cnf.clauses);start=time.perf_counter()
  target=E.cnf.leq_binary(E.terms,score-E.offset);good=E.cnf.witness({v:x in S for x,v in E.var.items()});assert good[abs(target)]==(target>0)
  # One comparator for exact control; a separate build for cap one lower.
  row={'bonus':bonus,'score_scale21':score,'objective_variables':base_nv,'objective_clauses':before,'full_variables':E.cnf.nv,'full_clauses_with_exact_cap':len(E.cnf.clauses)+1,'PB_build_seconds':time.perf_counter()-start}
  fixed=[[v if x in S else -v] for x,v in E.var.items()]
  satclauses=E.cnf.clauses+fixed+[[target]];sat=propagate(satclauses);assert not sat['contradiction'] and sat['assigned_variables']==E.cnf.nv
  assert all(any(good[abs(l)]==(l>0) for l in c) for c in satclauses)
  F=FixedPathObjective(G,path[:11],occupancy_bonus=bonus,cnf_factory=BinaryCNF);bad=F.cnf.leq_binary(F.terms,score-1-F.offset)
  unsatclauses=F.cnf.clauses+[[v if x in S else -v] for x,v in F.var.items()]+[[bad]];unsat=propagate(unsatclauses);assert unsat['contradiction']
  row.update(exact_cap_control=sat,exact_minus_one_control=unsat);rows.append(row)
  if bonus:
   for name,C,clauses in [('exact',E,satclauses),('exact_minus_one',F,unsatclauses)]:
    with gzip.open(HERE/f'bank67_bonus_control_{name}.cnf.gz','wt',encoding='ascii') as f:
     f.write('c FIXED BANK POSITIVE/NEGATIVE CONTROL ONLY; not a universal window query\n');f.write(f'p cnf {C.cnf.nv} {len(clauses)}\n')
     for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
 result={'scalar_tests':self_test(),'bank_controls':rows,'status':'Exact-cap controls pass; minus-one controls contradict by unit propagation with all bank base variables fixed. No free-window UNSAT or Lean/LRAT claim.'}
 (HERE/'binary_pb_controls.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
