"""Remove unnecessary outer directions from the maximal numerical exclusions."""
from survey import p,HERE,canon
import json

def main():
 rows=json.loads((HERE/'data/survey.json').read_text());uns=[r for r in rows if r['status']=='UNSAT']
 frontier=[r for r in uns if not any(s['shape']==r['shape'] and s['positions']==r['positions'] and s['caps']!=r['caps'] and all(a>=b for a,b in zip(s['caps'],r['caps'])) for s in uns)]
 (HERE/'data/frontier.json').write_text(json.dumps(frontier,indent=2)+'\n')
 answers=[]
 for i,row in enumerate(frontier):
  ds=row['dirs'];pos=row['positions'];caps=row['caps'];changed=True
  while changed:
   changed=False
   for side in ['left','right']:
    if side=='left' and min(pos)<2:continue
    if side=='right' and max(pos)>len(ds)-2:continue
    trial=list(canon(ds[1:] if side=='left' else ds[:-1]));newpos=[j-1 for j in pos] if side=='left' else pos
    bounds=[21]*(len(trial)-1)
    for j,c in zip(newpos,caps):bounds[j-1]=c
    p.DIRS=trial
    result=p.solve(f'trim-{i}-{len(trial)}-{side}',bounds,seconds=2)
    if result['status']=='UNSAT':ds=trial;pos=newpos;changed=True;break
  bounds=[21]*(len(ds)-1)
  for j,c in zip(pos,caps):bounds[j-1]=c
  p.DIRS=ds;result=p.solve(f'basis-probe-{i}',bounds,seconds=3)
  answers.append(dict(original=row['name'],dirs=ds,positions=pos,caps=caps,probe=f'basis-probe-{i}',status=result['status']))
  (HERE/'data/shortened.json').write_text(json.dumps(answers,indent=2)+'\n')
  print('Shortened',i,ds,pos,caps,flush=True)
 basis=[]
 for row in answers:
  key=(row['dirs'],row['positions'],row['caps'])
  if any((r['dirs'],r['positions'],r['caps'])==key for r in basis):continue
  row=dict(row,number=4901+len(basis),kind='cycle')
  row['bounds']=[[0,21] for _ in range(len(row['dirs'])-1)]
  for j,c in zip(row['positions'],row['caps']):row['bounds'][j-1]=[0,c]
  basis.append(row)
 (HERE/'data/cases.json').write_text(json.dumps(basis,indent=2)+'\n')
 print('Distinct shortened basis:',len(basis),flush=True)
if __name__=='__main__':main()
