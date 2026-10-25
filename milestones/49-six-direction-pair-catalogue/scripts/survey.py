"""Exhaust all six-direction shapes and four low-cap pairs at every centre pair."""
from pathlib import Path
import importlib.util,itertools,json,contextlib,collections
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('probe',ROOT/'milestones/40-intervening-counts/scripts/probe.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p);p.HERE=HERE

def canon(ds):
 names={};return tuple(names.setdefault(d,len(names)) for d in ds)
def shapes():
 words=[()]
 for length in range(6):
  nxt=[]
  for word in words:
   for d in range(max(word,default=-1)+2):
    w=word+(d,);vs=[0]
    for x in w:vs.append(vs[-1]^(1<<x))
    if len(vs)==len(set(vs)) and all((vs[i]^vs[j]).bit_count()!=1 for i in range(len(vs)) for j in range(i+2,len(vs))):nxt.append(w)
  words=nxt
 return sorted({min(w,canon(w[::-1])) for w in words})

def main():
 ss=shapes();assert len(ss)==9
 (HERE/'data/shapes.json').write_text(json.dumps(ss,indent=2)+'\n')
 rows=[]
 with (HERE/'logs/survey.txt').open('w') as log:
  for si,ds in enumerate(ss):
   p.DIRS=list(ds)
   for a,b in itertools.combinations(range(1,6),2):
    for u,v in [(2,2),(2,3),(3,2),(3,3)]:
     name=f's{si}-p{a}{b}-c{u}{v}';f=HERE/f'data/{name}.json'
     if f.exists():r=json.loads(f.read_text())
     else:
      caps=[21]*5;caps[a-1]=u;caps[b-1]=v
      with contextlib.redirect_stdout(log):r=p.solve(name,caps,seconds=3)
     rows.append(dict(name=name,shape=si,dirs=list(ds),positions=[a,b],caps=[u,v],status=r['status'],cycle_cuts=len(r['cycle_cuts'])))
   print('Shape',si,list(ds),dict(collections.Counter(r['status'] for r in rows if r['shape']==si)),flush=True)
   (HERE/'data/survey.json').write_text(json.dumps(rows,indent=2)+'\n')
 print('TOTAL',len(rows),dict(collections.Counter(r['status'] for r in rows)),flush=True)
if __name__=='__main__':main()
