"""Require seven successive counts from a recorded cycle on one local configuration."""
import argparse,hashlib,json,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,census,Cadical153,canonical

def cases(table='witness'):
 source=ROOT/'milestones/33-distance-three-singletons/data/pair-graph.json'
 runs=json.loads(source.read_text())['runs'];out=[]
 for row in runs:
  if row['stage']!='pair':continue
  cc=row['cycle'];n=len(cc);hits=[]
  for j,e in enumerate(cc):
   if list(canonical(e['directions'][-7:]))==[0,1,2,3,4,1,5]:hits.append(j)
   if row['table']==table:
    out.append(dict(index=j,dirs=list(canonical(e['directions'])),counts=[cc[(j-k)%n]['alpha'] for k in range(6,-1,-1)]))
  assert not hits
  print(row['table'],'period',n,'bonus occurrences',len(hits),flush=True)
 return out,hashlib.sha256(source.read_bytes().replace(b'\r\n',b'\n')).hexdigest()

def solve(case,seconds):
 t=time.monotonic();W=window(case['dirs']);bounds=[(v,v) if v<6 else (6,21) for v in case['counts']];e=TaggedEncoding(W,bounds,radius=4)
 cuts=[];status='UNKNOWN';selected=None;report=None
 with Cadical153(bootstrap_with=e.clauses) as s:
  while time.monotonic()-t<seconds:
   s.conf_budget(10000);ok=s.solve_limited()
   if ok is None:continue
   if not ok:status='UNSAT';break
   m=s.get_model();S={v for v in e.ball if m[e.var[v]-1]>0};report=census(S,9,W[1:-1]);report.pop('degree')
   if not report['cycles']:
    status='SAT';selected=sorted(S);assert all(lo<=v<=hi for v,(lo,hi) in zip(report['alpha'],bounds));break
   for c in report['cycles']:cuts.append(c);s.add_clause([-e.var[v] for v in c])
 return dict(case,status=status,selected=selected,census=report if selected else None,cycle_cuts=cuts,seconds=time.monotonic()-t,scope='Local acyclic configuration or solver exclusion; UNSAT requires proof replay and geometric interpretation.')

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=20);ap.add_argument('--table',choices=['witness','lower'],default='witness');a=ap.parse_args()
 for d in ('data','logs','lean','certificates','build'):(HERE/d).mkdir(exist_ok=True)
 prefix='' if a.table=='witness' else 'lower-'
 rows,sha=cases(a.table);(HERE/f'data/{prefix}candidates.json').write_text(json.dumps(dict(source_sha256_lf=sha,cases=rows),indent=2)+'\n')
 for c in rows:
  r=solve(c,a.seconds);(HERE/f'data/{prefix}screen-{c["index"]}.json').write_text(json.dumps(r,indent=2)+'\n');print(c,r['status'],round(r['seconds'],2),'seconds',flush=True)
