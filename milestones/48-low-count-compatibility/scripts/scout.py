"""Scout the replacement cycle without mistaking the capped value six for an exact count."""
from probe import p,HERE
import json,hashlib
answers=[]
for i,row in enumerate(json.loads((HERE/'data/analysis.json').read_text())['cycle']):
    p.DIRS=row['directions'];caps=[v if v<6 else 21 for v in row['counts']]
    out=p.solve(f'next-cycle-{i}-interval',caps,seconds=3)
    answer=dict(phase=i,directions=p.DIRS,counts=row['counts'],interval_status=out['status'])
    if out['status']=='SAT':
        exact=p.solve(f'next-cycle-{i}-exact',row['counts'],seconds=3)
        answer['exact_status']=exact['status']
    source=HERE/f'data/next-cycle-{i}-interval.json'
    answer['source_sha256']=hashlib.sha256(source.read_bytes()).hexdigest()
    answers.append(answer)
    (HERE/'data/next-cycle-scout.json').write_text(json.dumps(answers,indent=2)+'\n')
if __name__=='__main__':print('Scout results:',answers,flush=True)
