"""Test the M12 empty-square share at equality in the second pair inequality."""
import argparse,hashlib,itertools,json,time
from pathlib import Path
from pair_model import model,census,cp_model
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
DS=[0,1,2,3,4,1,5]
def solve(cap,radius=4,seconds=30,fixed=None):
 t=time.monotonic();md,x,total,W,B,known=model(9,DS,[(0,21)]*6,radius=radius,cap=cap,fixed=fixed)
 corners=[]
 for j in (1,6):
  axes=[a for a in range(9) if a not in (DS[j-1],DS[j])]
  corners.extend(W[j]^(1<<a)^(1<<b) for a,b in itertools.combinations(axes,2))
 md.add(sum(1-x[v] for v in corners)==9)
 cuts=[];status='UNKNOWN';selected=None;report=None;iterations=[];deadline=time.monotonic()+seconds
 while time.monotonic()<deadline:
  solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=max(.01,deadline-time.monotonic());solver.parameters.num_search_workers=2;solver.parameters.random_seed=196
  result=solver.solve(md);status=solver.status_name(result);iterations.append(dict(status=status,seconds=solver.wall_time,branches=solver.num_branches))
  if result not in (cp_model.OPTIMAL,cp_model.FEASIBLE):break
  S={v for v in B if solver.value(x[v])};c=census(S,9,W[1:-1]);c.pop('degree');pairshare=c['share'][0]+c['share'][5]
  assert c['alpha'][0]+c['alpha'][5]==9 and pairshare==solver.value(total) and pairshare<=cap
  if not c['cycles']:selected=sorted(S);report=c;break
  for cc in c['cycles']:
   known.add(frozenset(cc));cuts.append(cc);md.add(sum(x[v] for v in cc)<=len(cc)-1)
 else:status='TIME_LIMIT'
 out=dict(dirs=DS,alpha=[[0,21]]*6,joint_count=9,share_centres=[1,6],cap=cap,radius=radius,status=status,selected=selected,census=report,iterations=iterations,cycle_cuts=cuts,seconds=time.monotonic()-t,
 scope='Exact quotient CP model; INFEASIBLE awaits proof replay, local FEASIBLE need not extend to a snake.')
 return out
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=60);a=ap.parse_args()
 control=json.loads((ROOT/'milestones/34-distance-three-sharpness/data/witness-1.json').read_text());S=set(control['vertex_sequence'])
 W=[0]
 for d in DS:W.append(W[-1]^(1<<d))
 B={v for v in range(512) if min((v^c).bit_count() for c in W[1:-1])<=4}
 for name,cap,fixed in [('fixed-control',42,S&B),('cap11',11,None)]:
  r=solve(cap,seconds=a.seconds,fixed=fixed);r['script_sha256_lf']=hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
  (HERE/f'data/{name}.json').write_text(json.dumps(r,indent=2)+'\n')
  print(name,r['status'],'pair shares',None if r['census'] is None else [r['census']['share'][j] for j in (0,5)],flush=True)
