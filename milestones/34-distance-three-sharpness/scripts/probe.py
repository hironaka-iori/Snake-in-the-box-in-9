"""Test attainability of the proved pair bounds in the radius-four forest model."""
import argparse,hashlib,importlib.util,json,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/33-distance-three-singletons/scripts'))
from certify import TaggedEncoding,window,candidates,Cadical153,census,joint_literals,BOUNDS,prior

def probe(i,cap,seconds):
 ds=candidates()[i]['dirs'];W=window(ds);enc=TaggedEncoding(W,BOUNDS,radius=4)
 enc.atmost(joint_literals(enc,W),cap,('ends',))
 started=time.monotonic();cuts=[];status='UNKNOWN';chosen=None;counts=None
 with Cadical153(bootstrap_with=enc.clauses) as solver:
  while time.monotonic()-started<seconds:
   solver.conf_budget(3000);ok=solver.solve_limited()
   if ok is None:continue
   if not ok:status='UNSAT';break
   m=solver.get_model();S={v for v in enc.ball if m[enc.var[v]-1]>0};report=census(S,9,W[1:-1]);report.pop('degree')
   if not report['cycles']:
    assert report['alpha'][0]+report['alpha'][5]<=cap
    chosen=sorted(S);counts=report;status='SAT';break
   for cc in report['cycles']:
    prior.check_cut(cc);solver.add_clause([-enc.var[v] for v in cc]);cuts.append(cc)
 row=dict(case=i,dirs=ds,alpha=BOUNDS,cap=cap,status=status,seconds=time.monotonic()-started,selected=chosen,census=counts,cycle_cuts=cuts,
  scope='Local radius-four forest test; UNSAT is solver-only, SAT is not a complete snake.',script_sha256_lf=hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest())
 if chosen:prior.census(row)
 (HERE/f'data/pair-{i}-cap-{cap}.json').write_text(json.dumps(row,indent=2)+'\n')
 print(i,cap,status,'sum',None if not counts else counts['alpha'][0]+counts['alpha'][5],'cuts',len(cuts),flush=True)
 return status

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=20);a=ap.parse_args()
 for i,caps in [(0,[10,11,12,14]),(1,[9,10,11,12,14])]:
  for cap in caps:
   if probe(i,cap,a.seconds)=='SAT':break
if __name__=='__main__':main()
