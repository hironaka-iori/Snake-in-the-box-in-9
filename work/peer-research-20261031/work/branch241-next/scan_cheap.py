import json,random,time
from pathlib import Path
from charge_fast import Geometry,Charges
HERE=Path(__file__).resolve().parent;REPO=HERE.parent/'branch241-audit/repo';G=Geometry(9);bank=json.loads((REPO/'work/bank9.json').read_text());start=time.perf_counter()
def minimum(vals,path,k):
 best=None
 for i in range(1,len(path)-k):
  s=sum(vals[v] for v in path[i:i+k]);row=(s,i)
  if best is None or row<best:best=row
 return best
rows=[]
for index,b in enumerate(bank):
 path=b['vertex_sequence'];c=Charges(G,path);q=c.cheap();row={'bank_index':index,'edges':len(path)-1,'objective_minima':{}}
 for name,data in q.items():
  row['objective_minima'][name]={'scale':data['scale'],'windows':{str(k):list(minimum(data['values'],path,k)) for k in (1,3,5,7,9)}}
 rows.append(row)
adv=[]
for name in ('adversary208','adversary224'):
 d=json.loads((REPO/f'milestones/11-local-ceiling/data/{name}.json').read_text());S=set(d['S']);c=Charges(G,S);q=c.cheap()
 assert all(sum((v^(1<<j)) in S for j in range(9))==2 for v in S)
 for cyc in d['cycles']:
  assert all((a^b).bit_count()==1 for a,b in zip(cyc,cyc[1:]+cyc[:1]))
  assert len(set(cyc))==len(cyc)
 assert set().union(*map(set,d['cycles']))==S
 adv.append({'name':name,'vertices':len(S),'cycle_lengths':[len(c) for c in d['cycles']],'charge':c.summary(),'objectives':{n:{'sum_scaled':sum(v['values']),'scale':v['scale'],'mean_display':sum(v['values'])/(v['scale']*len(S))} for n,v in q.items()}})
summary={'status':'Empirical minima from131 bank paths, NOT universal lower bounds','bank_count':len(bank),'objectives':{},'adversaries':adv,'runtime_seconds':time.perf_counter()-start}
for name in rows[0]['objective_minima']:
 d={}
 for k in (1,3,5,7,9):
  r=min(rows,key=lambda r:r['objective_minima'][name]['windows'][str(k)][0]);v=r['objective_minima'][name];score,pos=v['windows'][str(k)]
  d[str(k)]={'bank_index':r['bank_index'],'first_centre_index':pos,'sum_scaled':score,'scale':v['scale'],'mean_display':score/(v['scale']*k)}
 summary['objectives'][name]=d
(HERE/'cheap_scan.json').write_text(json.dumps({'summary':summary,'records':rows},indent=2));(HERE/'cheap_summary.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary,indent=2))
